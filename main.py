import html
import json
import mimetypes
import os
import shutil
import sqlite3
import subprocess
import sys
import threading
import urllib.parse
import urllib.request
from contextlib import contextmanager
from email.utils import formatdate, parsedate_to_datetime
from http import HTTPStatus
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from secrets import token_urlsafe
from ssl import _create_default_https_context, _create_unverified_context

from authlib.integrations.requests_client import OAuth2Session
from cachetools import TTLCache
from dotenv import load_dotenv
from gitea import Gitea, NotFoundException


def get_env(name: str) -> str:
    value = os.getenv(name, "").strip()
    if not value:
        raise ValueError(f"Missing required environment variable: {name}")
    return value


def parse_bool(name: str, default: bool = True) -> bool:
    value = os.getenv(name)
    if value is None:
        return default
    return value.strip().lower() in {"1", "true", "yes", "on"}


def parse_host(host_header: str) -> str:
    return host_header.split(":", 1)[0].strip().lower()


# ---------------------------------------------------------------------------
# Database layer
# ---------------------------------------------------------------------------

DB_SCHEMA = """
CREATE TABLE IF NOT EXISTS sites (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    owner       TEXT    NOT NULL,
    repo        TEXT    NOT NULL,
    branch      TEXT    NOT NULL DEFAULT '',
    root_folder TEXT    NOT NULL DEFAULT '',
    auto_update INTEGER NOT NULL DEFAULT 0,
    UNIQUE (owner, repo)
);

CREATE TABLE IF NOT EXISTS domains (
    id      INTEGER PRIMARY KEY AUTOINCREMENT,
    site_id INTEGER NOT NULL REFERENCES sites(id) ON DELETE CASCADE,
    domain  TEXT    NOT NULL UNIQUE
);

CREATE INDEX IF NOT EXISTS idx_domains_domain   ON domains(domain);
CREATE INDEX IF NOT EXISTS idx_sites_owner_repo ON sites(owner, repo);
"""


class Database:
    """Thread-safe SQLite wrapper using WAL mode."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self._local = threading.local()
        with self._conn() as conn:
            conn.executescript(DB_SCHEMA)

    def _conn(self) -> sqlite3.Connection:
        if not getattr(self._local, "conn", None):
            conn = sqlite3.connect(str(self.path), check_same_thread=False)
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA foreign_keys=ON")
            conn.row_factory = sqlite3.Row
            self._local.conn = conn
        return self._local.conn

    @contextmanager
    def transaction(self):
        conn = self._conn()
        try:
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise

    def get_site(self, owner: str, repo: str) -> sqlite3.Row | None:
        return self._conn().execute(
            "SELECT * FROM sites WHERE owner = ? AND repo = ?", (owner, repo)
        ).fetchone()

    def upsert_site(
        self, owner: str, repo: str, branch: str, root_folder: str, auto_update: bool
    ) -> int:
        with self.transaction() as conn:
            conn.execute(
                """
                INSERT INTO sites (owner, repo, branch, root_folder, auto_update)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(owner, repo) DO UPDATE SET
                    branch      = excluded.branch,
                    root_folder = excluded.root_folder,
                    auto_update = excluded.auto_update
                """,
                (owner, repo, branch, root_folder, int(auto_update)),
            )
            return conn.execute(
                "SELECT id FROM sites WHERE owner = ? AND repo = ?", (owner, repo)
            ).fetchone()["id"]

    def delete_site(self, owner: str, repo: str) -> None:
        with self.transaction() as conn:
            conn.execute("DELETE FROM sites WHERE owner = ? AND repo = ?", (owner, repo))

    def get_site_domains(self, owner: str, repo: str) -> list[str]:
        rows = self._conn().execute(
            """
            SELECT d.domain FROM domains d
            JOIN sites s ON s.id = d.site_id
            WHERE s.owner = ? AND s.repo = ?
            ORDER BY d.domain
            """,
            (owner, repo),
        ).fetchall()
        return [r["domain"] for r in rows]

    def set_site_domains(self, site_id: int, domains: list[str]) -> None:
        with self.transaction() as conn:
            conn.execute("DELETE FROM domains WHERE site_id = ?", (site_id,))
            conn.executemany(
                "INSERT OR IGNORE INTO domains (site_id, domain) VALUES (?, ?)",
                [(site_id, d) for d in domains],
            )

    def resolve_domain(self, domain: str) -> tuple[str, str] | None:
        row = self._conn().execute(
            """
            SELECT s.owner, s.repo FROM domains d
            JOIN sites s ON s.id = d.site_id
            WHERE d.domain = ?
            """,
            (domain,),
        ).fetchone()
        return (row["owner"], row["repo"]) if row else None


# ---------------------------------------------------------------------------
# RepoServer
# ---------------------------------------------------------------------------

class RepoServer:
    def __init__(
        self,
        gitea_url: str,
        token: str,
        verify_ssl: bool,
        clone_root: Path,
        db: Database,
        main_domain: str,
        pages_subdomain: str,
        instance_name: str,
        preferred_branch: str,
        logo_url: str,
        favicon_url: str,
        public_url: str,
        oauth_client_id: str,
        oauth_client_secret: str,
        webhook_url: str,
        templates_dir: Path,
    ):
        self.client = Gitea(gitea_url, token_text=token, verify=verify_ssl)
        self.clone_root = clone_root
        self.db = db
        self.main_domain = main_domain.lower()
        self.pages_subdomain = pages_subdomain.lower()
        self.instance_name = instance_name
        self.preferred_branch = preferred_branch
        self.logo_url = logo_url
        self.favicon_url = favicon_url
        self.public_url = public_url.rstrip("/")
        self.oauth_client_id = oauth_client_id
        self.oauth_client_secret = oauth_client_secret
        self.webhook_url = webhook_url.rstrip("/")
        self.templates_dir = templates_dir
        self.verify_ssl = verify_ssl

        self.locks: dict[str, threading.Lock] = {}
        self.locks_guard = threading.Lock()
        self.cache_guard = threading.RLock()

        self.domain_cache: TTLCache[str, tuple[str, str] | None] = TTLCache(maxsize=4096, ttl=15)
        self.publish_dir_cache: TTLCache[tuple[str, str], Path] = TTLCache(maxsize=2048, ttl=30)
        self.template_cache: TTLCache[str, str] = TTLCache(maxsize=16, ttl=30)
        self.oauth_metadata_cache: TTLCache[str, dict] = TTLCache(maxsize=1, ttl=3600)
        self.oauth_state_cache: TTLCache[str, str] = TTLCache(maxsize=256, ttl=600)
        self.edit_session_cache: TTLCache[str, dict] = TTLCache(maxsize=1024, ttl=43200)

        self.clone_root.mkdir(parents=True, exist_ok=True)

    # --- locks & cache -----------------------------------------------------

    def get_lock(self, key: str) -> threading.Lock:
        with self.locks_guard:
            if key not in self.locks:
                self.locks[key] = threading.Lock()
            return self.locks[key]

    def get_cached(self, cache, key, factory):
        with self.cache_guard:
            if key in cache:
                return cache[key]
        value = factory()
        with self.cache_guard:
            cache[key] = value
        return value

    def invalidate_repo_cache(self, owner: str, repo: str) -> None:
        with self.cache_guard:
            stale = [h for h, t in self.domain_cache.items() if t == (owner, repo)]
            for h in stale:
                self.domain_cache.pop(h, None)
            self.publish_dir_cache.pop((owner, repo), None)

    # --- templates ---------------------------------------------------------

    def load_template(self, name: str) -> str:
        return self.get_cached(
            self.template_cache, name,
            lambda: (self.templates_dir / name).read_text(encoding="utf-8"),
        )

    # --- domain resolution -------------------------------------------------

    def resolve_domain(self, host: str) -> tuple[str, str] | None:
        return self.get_cached(self.domain_cache, host, lambda: self.db.resolve_domain(host))

    def is_main_domain(self, host: str) -> bool:
        return host == self.main_domain

    def pages_subdomain_label(self, host: str) -> str | None:
        """Return the label part if host == label.pages_subdomain, else None."""
        suffix = f".{self.pages_subdomain}"
        if not host.endswith(suffix):
            return None
        label = host[: -len(suffix)]
        if not label or "." in label:
            return None
        return label

    # --- Gitea helpers -----------------------------------------------------

    def get_repo_info(self, owner: str, repo: str) -> dict:
        return self.client.requests_get(f"/repos/{owner}/{repo}")

    def list_repo_branches(self, owner: str, repo: str) -> list[str]:
        try:
            results = self.client.requests_get(f"/repos/{owner}/{repo}/branches?limit=50")
            if isinstance(results, list):
                return [b["name"] for b in results if isinstance(b, dict) and "name" in b]
        except Exception:
            pass
        return []

    def fetch_json(self, url: str) -> dict:
        ctx = _create_default_https_context() if self.verify_ssl else _create_unverified_context()
        with urllib.request.urlopen(url, context=ctx) as r:
            return json.loads(r.read().decode("utf-8"))

    # --- OAuth -------------------------------------------------------------

    def oauth_callback_url(self) -> str:
        return f"{self.public_url}/oauth/callback"

    def oauth_login_url(self, next_path: str) -> str:
        return f"/login?{urllib.parse.urlencode({'next': next_path})}"

    def oauth_metadata(self) -> dict:
        return self.get_cached(
            self.oauth_metadata_cache, "metadata",
            lambda: self.fetch_json(f"{self.client.url.rstrip('/')}/.well-known/openid-configuration"),
        )

    def oauth_client(self, state: str | None = None) -> OAuth2Session:
        return OAuth2Session(
            self.oauth_client_id,
            self.oauth_client_secret,
            scope="openid profile email",
            redirect_uri=self.oauth_callback_url(),
            state=state,
        )

    # --- sessions ----------------------------------------------------------

    def create_edit_session(self, user: dict) -> str:
        sid = token_urlsafe(32)
        with self.cache_guard:
            self.edit_session_cache[sid] = user
        return sid

    def get_edit_session(self, sid: str) -> dict | None:
        with self.cache_guard:
            return self.edit_session_cache.get(sid)

    def delete_edit_session(self, sid: str) -> None:
        with self.cache_guard:
            self.edit_session_cache.pop(sid, None)

    # --- repo filesystem ---------------------------------------------------

    def repo_dir(self, owner: str, repo: str) -> Path:
        return self.clone_root / owner / repo

    def publish_dir(self, owner: str, repo: str, root_folder: str) -> Path:
        def factory() -> Path:
            base = self.repo_dir(owner, repo)
            raw = (root_folder or "").strip()
            normalized = raw.replace("\\", "/").strip("/")
            if normalized and normalized != ".":
                candidate = (base / normalized).resolve()
                base_resolved = base.resolve()
                if os.path.commonpath([str(base_resolved), str(candidate)]) == str(base_resolved):
                    if candidate.is_dir():
                        return candidate
            return base
        return self.get_cached(self.publish_dir_cache, (owner, repo), factory)

    def refresh_repo(self, owner: str, repo: str, branch: str) -> None:
        lock = self.get_lock(f"{owner}/{repo}")
        if not lock.acquire(blocking=False):
            return
        try:
            repo_info = self.get_repo_info(owner, repo)
            # Validate branch, fall back to default
            try:
                self.client.requests_get(f"/repos/{owner}/{repo}/branches/{branch}")
            except NotFoundException:
                branch = repo_info["default_branch"]

            clone_url = repo_info["clone_url"]
            target = self.repo_dir(owner, repo)
            target.parent.mkdir(parents=True, exist_ok=True)

            if (target / ".git").is_dir():
                self._git(["git", "-C", str(target), "fetch", "origin", branch, "--depth", "1"])
                self._git(["git", "-C", str(target), "checkout", "-f", branch])
                self._git(["git", "-C", str(target), "reset", "--hard", f"origin/{branch}"])
                self._git(["git", "-C", str(target), "clean", "-fd"])
            else:
                if target.exists():
                    shutil.rmtree(target)
                self._git(["git", "clone", "--depth", "1", "--branch", branch,
                           "--single-branch", clone_url, str(target)])

            self.invalidate_repo_cache(owner, repo)
        finally:
            lock.release()

    def _git(self, args: list[str]) -> None:
        subprocess.run(args, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def safe_refresh(self, owner: str, repo: str, branch: str) -> None:
        try:
            self.refresh_repo(owner, repo, branch)
        except Exception:
            pass

    # --- webhooks ----------------------------------------------------------

    def find_repo_webhook(self, owner: str, repo: str) -> dict | None:
        hooks = self.client.requests_get(f"/repos/{owner}/{repo}/hooks")
        if not isinstance(hooks, list):
            return None
        for hook in hooks:
            if not isinstance(hook, dict):
                continue
            cfg = hook.get("config", {})
            if isinstance(cfg, dict) and str(cfg.get("url", "")).rstrip("/") == self.webhook_url:
                return hook
        return None

    def upsert_repo_webhook(self, owner: str, repo: str, branch: str) -> None:
        existing = self.find_repo_webhook(owner, repo)
        data = {
            "active": True,
            "branch_filter": branch,
            "events": ["push"],
            "config": {"content_type": "json", "http_method": "post", "url": self.webhook_url},
        }
        if existing:
            self.client.requests_patch(f"/repos/{owner}/{repo}/hooks/{existing['id']}", data=data)
            return
        create = dict(data)
        create["type"] = "forgejo"
        try:
            self.client.requests_post(f"/repos/{owner}/{repo}/hooks", data=create)
        except Exception:
            create["type"] = "gitea"
            self.client.requests_post(f"/repos/{owner}/{repo}/hooks", data=create)

    def delete_repo_webhook(self, owner: str, repo: str) -> None:
        existing = self.find_repo_webhook(owner, repo)
        if existing:
            self.client.requests_delete(f"/repos/{owner}/{repo}/hooks/{existing['id']}")

    # --- settings ----------------------------------------------------------

    def get_site_settings(self, owner: str, repo: str) -> dict:
        repo_info = self.get_repo_info(owner, repo)
        branches = self.list_repo_branches(owner, repo)
        site = self.db.get_site(owner, repo)
        domains = self.db.get_site_domains(owner, repo) if site else []
        webhook = self.find_repo_webhook(owner, repo)
        return {
            "repo_info": repo_info,
            "branches": branches,
            "branch": site["branch"] if site else repo_info.get("default_branch", ""),
            "root_folder": site["root_folder"] if site else "",
            "auto_update": bool(site["auto_update"]) if site else False,
            "domains": domains,
            "pages_enabled": site is not None,
            "webhook": webhook,
        }

    def save_site_settings(
        self,
        owner: str,
        repo: str,
        pages_enabled: bool,
        branch: str,
        root_folder: str,
        auto_update: bool,
        domains: list[str],
    ) -> None:
        if not pages_enabled:
            self.db.delete_site(owner, repo)
            self.delete_repo_webhook(owner, repo)
            self.invalidate_repo_cache(owner, repo)
            return

        site_id = self.db.upsert_site(owner, repo, branch, root_folder, auto_update)
        self.db.set_site_domains(site_id, domains)
        self.invalidate_repo_cache(owner, repo)

        if auto_update:
            self.upsert_repo_webhook(owner, repo, branch)
        else:
            self.delete_repo_webhook(owner, repo)

        threading.Thread(target=self.safe_refresh, args=(owner, repo, branch), daemon=True).start()

    # --- rendering ---------------------------------------------------------

    def render_landing_page(self) -> str:
        return self.load_template("landing.html").format(
            main_domain=html.escape(self.main_domain),
            instance_name=html.escape(self.instance_name),
            preferred_branch=html.escape(self.preferred_branch),
            logo_url=html.escape(self.logo_url),
            favicon_url=html.escape(self.favicon_url),
            instance_url=html.escape(self.client.url),
            pages_subdomain=html.escape(self.pages_subdomain),
        )

    def render_error_page(self, status_code: int, title: str, message: str) -> str:
        return self.load_template("error.html").format(
            status_text=html.escape(str(status_code)),
            title_text=html.escape(title),
            message_text=html.escape(message),
            instance_name=html.escape(self.instance_name),
            logo_url=html.escape(self.logo_url),
            favicon_url=html.escape(self.favicon_url),
            instance_url=html.escape(self.client.url),
        )

    def render_settings_page(
        self,
        owner: str,
        repo: str,
        settings: dict,
        user: dict,
        success_message: str = "",
        error_message: str = "",
    ) -> str:
        repo_info = settings["repo_info"]
        webhook = settings.get("webhook")
        branches = settings.get("branches", [])
        current_branch = settings["branch"]

        branch_options = ""
        for b in branches:
            sel = " selected" if b == current_branch else ""
            branch_options += f'<option value="{html.escape(b)}"{sel}>{html.escape(b)}</option>\n'
        if not branches:
            branch_options = (
                f'<option value="{html.escape(current_branch)}" selected>'
                f'{html.escape(current_branch)}</option>\n'
            )

        return self.load_template("settings.html").format(
            instance_name=html.escape(self.instance_name),
            logo_url=html.escape(self.logo_url),
            favicon_url=html.escape(self.favicon_url),
            instance_url=html.escape(self.client.url),
            owner_text=html.escape(owner),
            repo_text=html.escape(repo),
            owner_path=html.escape(urllib.parse.quote(owner)),
            repo_path=html.escape(urllib.parse.quote(repo)),
            main_domain=html.escape(self.main_domain),
            pages_subdomain=html.escape(self.pages_subdomain),
            repo_full_name=html.escape(f"{owner}/{repo}"),
            repo_url=html.escape(str(repo_info.get("html_url", f"{self.client.url}/{owner}/{repo}"))),
            branch_options=branch_options,
            root_folder_value=html.escape(settings["root_folder"]),
            webhook_url=html.escape(self.webhook_url),
            webhook_branch=html.escape(
                str(webhook.get("branch_filter", current_branch)) if webhook else current_branch
            ),
            viewer_name=html.escape(
                str(user.get("preferred_username") or user.get("name") or user.get("sub") or "Signed in")
            ),
            pages_checked="checked" if settings.get("pages_enabled") else "",
            auto_update_checked="checked" if settings.get("auto_update") else "",
            domains_text=html.escape("\n".join(settings.get("domains", []))),
            auto_update_badge="Enabled" if settings.get("auto_update") else "Disabled",
            success_block=(
                f'<div class="alert alert-success mb-4" role="alert">{html.escape(success_message)}</div>'
                if success_message else ""
            ),
            error_block=(
                f'<div class="alert alert-danger mb-4" role="alert">{html.escape(error_message)}</div>'
                if error_message else ""
            ),
        )


# ---------------------------------------------------------------------------
# HTTP request handler
# ---------------------------------------------------------------------------

class RequestHandler(BaseHTTPRequestHandler):
    server_version = "TuxForgePages/1.0"

    @property
    def app(self) -> RepoServer:
        return self.server.app

    def do_GET(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path.strip("/")
        query = urllib.parse.parse_qs(parsed.query)
        parts = [urllib.parse.unquote(p) for p in path.split("/") if p]
        host = parse_host(self.headers.get("Host", ""))

        # 1. Main admin domain
        if self.app.is_main_domain(host) or not host:
            if len(parts) == 1 and parts[0] == "login":
                self.handle_login_get(query)
                return
            if len(parts) == 2 and parts[0] == "oauth" and parts[1] == "callback":
                self.handle_oauth_callback(query)
                return
            if len(parts) == 1 and parts[0] == "logout":
                self.handle_logout_get()
                return
            self.handle_main_domain(parts, query)
            return

        # 2. *.pages_subdomain — must be explicitly registered in DB
        if self.app.pages_subdomain_label(host) is not None:
            match = self.app.resolve_domain(host)
            if match is None:
                self.send_bootstrap_error(
                    HTTPStatus.NOT_FOUND, "Repository Not Found",
                    f"No repository has registered '{html.escape(host)}' as a domain.",
                )
                return
            self.serve_site(match[0], match[1], parts)
            return

        # 3. Fully custom domain
        match = self.app.resolve_domain(host)
        if match is not None:
            self.serve_site(match[0], match[1], parts)
            return

        self.send_bootstrap_error(
            HTTPStatus.NOT_FOUND, "Unknown Host", "This hostname is not configured on this server."
        )

    def do_POST(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path.strip("/")
        host = parse_host(self.headers.get("Host", ""))
        parts = [urllib.parse.unquote(p) for p in path.split("/") if p]

        if not self.app.is_main_domain(host):
            self.send_bootstrap_error(HTTPStatus.NOT_FOUND, "Not Found", "This route does not exist.")
            return

        if len(parts) == 3 and parts[0] == "edit":
            if not self.require_edit_login():
                return
            self.handle_repo_settings_post(parts[1], parts[2])
            return

        if not path:
            self.handle_deploy_post()
            return

        self.send_bootstrap_error(HTTPStatus.NOT_FOUND, "Not Found", "This route does not exist.")

    # --- main domain -------------------------------------------------------

    def handle_main_domain(self, parts: list[str], query: dict) -> None:
        if not parts:
            self.send_html(HTTPStatus.OK, self.app.render_landing_page())
            return
        if len(parts) == 1 and parts[0] == "edit":
            if not self.require_edit_login():
                return
            self.send_bootstrap_error(
                HTTPStatus.NOT_FOUND, "Repository Required",
                "Open a specific repository settings page at /edit/USERNAME/REPOSITORY.",
            )
            return
        if len(parts) == 3 and parts[0] == "edit":
            if not self.require_edit_login():
                return
            self.handle_repo_settings_get(parts[1], parts[2], query)
            return
        self.send_bootstrap_error(HTTPStatus.NOT_FOUND, "Not Found", "This route does not exist.")

    # --- deploy webhook ----------------------------------------------------

    def handle_deploy_post(self) -> None:
        try:
            content_length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self.send_bootstrap_error(HTTPStatus.BAD_REQUEST, "Invalid Request", "Content-Length is invalid.")
            return
        try:
            payload = json.loads(self.rfile.read(content_length) or b"{}")
        except json.JSONDecodeError:
            self.send_bootstrap_error(HTTPStatus.BAD_REQUEST, "Invalid JSON", "Request body must be valid JSON.")
            return

        repository = payload.get("repository", {})
        if not isinstance(repository, dict):
            self.send_bootstrap_error(HTTPStatus.BAD_REQUEST, "Invalid Payload", "Missing repository object.")
            return

        full_name = str(repository.get("full_name", "")).strip()
        name_parts = full_name.split("/", 1)
        if len(name_parts) != 2 or not name_parts[0] or not name_parts[1]:
            self.send_bootstrap_error(
                HTTPStatus.BAD_REQUEST, "Missing repository.full_name",
                "Provide JSON with repository.full_name like owner/repository.",
            )
            return

        owner, repo = name_parts
        site = self.app.db.get_site(owner, repo)
        if site is None:
            self.send_text(HTTPStatus.OK, "OK (not configured)")
            return

        branch = site["branch"] or str(payload.get("ref", "")).replace("refs/heads/", "")
        threading.Thread(target=self.app.safe_refresh, args=(owner, repo, branch), daemon=True).start()
        self.send_text(HTTPStatus.OK, "OK")

    # --- settings ----------------------------------------------------------

    def handle_repo_settings_get(self, owner: str, repo: str, query: dict) -> None:
        try:
            settings = self.app.get_site_settings(owner, repo)
        except NotFoundException:
            self.send_bootstrap_error(HTTPStatus.NOT_FOUND, "Repository Not Found", "This repository does not exist.")
            return
        except Exception as exc:
            self.send_bootstrap_error(HTTPStatus.BAD_GATEWAY, "Failed to Load Settings", str(exc))
            return

        current_user = self.current_edit_user()
        if current_user is None:
            self.redirect(self.app.oauth_login_url(self.path))
            return

        self.send_html(
            HTTPStatus.OK,
            self.app.render_settings_page(
                owner, repo, settings, current_user,
                query.get("success", [""])[0],
                query.get("error", [""])[0],
            ),
        )

    def handle_repo_settings_post(self, owner: str, repo: str) -> None:
        try:
            content_length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self.redirect_with_message(owner, repo, error="Content-Length is invalid.")
            return

        form = urllib.parse.parse_qs(
            self.rfile.read(content_length).decode("utf-8"), keep_blank_values=True
        )

        pages_enabled = "pages_enabled" in form
        branch = form.get("branch", [""])[0].strip() if pages_enabled else ""
        root_folder = form.get("root_folder", [""])[0].strip() if pages_enabled else ""
        auto_update = "auto_update" in form and pages_enabled
        domains = self._parse_domains(form.get("domains", [""])[0]) if pages_enabled else []

        try:
            self.app.save_site_settings(owner, repo, pages_enabled, branch, root_folder, auto_update, domains)
        except NotFoundException:
            self.redirect_with_message(owner, repo, error="Repository not found.")
            return
        except Exception as exc:
            self.redirect_with_message(owner, repo, error=f"Could not save settings: {exc}")
            return

        self.redirect_with_message(
            owner, repo,
            success=f"Pages settings {'updated' if pages_enabled else 'disabled'} successfully.",
        )

    def _parse_domains(self, raw: str) -> list[str]:
        seen: set[str] = set()
        result: list[str] = []
        for chunk in raw.replace(",", "\n").splitlines():
            d = chunk.strip().lower()
            if d and d not in seen:
                seen.add(d)
                result.append(d)
        return result

    def redirect_with_message(self, owner: str, repo: str, success: str = "", error: str = "") -> None:
        qs = urllib.parse.urlencode({k: v for k, v in {"success": success, "error": error}.items() if v})
        loc = f"/edit/{urllib.parse.quote(owner)}/{urllib.parse.quote(repo)}"
        self.redirect(f"{loc}?{qs}" if qs else loc)

    # --- OAuth -------------------------------------------------------------

    def handle_login_get(self, query: dict) -> None:
        next_path = query.get("next", ["/"])[0] or "/"
        if self.current_edit_user() is not None:
            self.redirect(next_path)
            return
        state = token_urlsafe(24)
        with self.app.cache_guard:
            self.app.oauth_state_cache[state] = next_path if next_path.startswith("/") else "/"
        metadata = self.app.oauth_metadata()
        client = self.app.oauth_client(state=state)
        url, _ = client.create_authorization_url(metadata["authorization_endpoint"], state=state)
        self.redirect(url)

    def handle_oauth_callback(self, query: dict) -> None:
        state = query.get("state", [""])[0]
        code = query.get("code", [""])[0]
        error = query.get("error", [""])[0]

        if error:
            self.send_bootstrap_error(HTTPStatus.UNAUTHORIZED, "Login Failed", f"OAuth error: {error}.")
            return
        if not state or not code:
            self.send_bootstrap_error(HTTPStatus.BAD_REQUEST, "Invalid Callback", "Missing OAuth state or code.")
            return

        with self.app.cache_guard:
            next_path = self.app.oauth_state_cache.pop(state, None)
        if next_path is None:
            self.send_bootstrap_error(HTTPStatus.BAD_REQUEST, "Invalid State", "OAuth state missing or expired.")
            return

        metadata = self.app.oauth_metadata()
        client = self.app.oauth_client(state=state)
        try:
            client.fetch_token(metadata["token_endpoint"], code=code, grant_type="authorization_code")
            userinfo = client.get(metadata["userinfo_endpoint"]).json()
        except Exception as exc:
            self.send_bootstrap_error(HTTPStatus.BAD_GATEWAY, "Login Failed", f"Could not complete login: {exc}")
            return

        sid = self.app.create_edit_session(userinfo if isinstance(userinfo, dict) else {"sub": "forgejo-user"})
        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", next_path)
        self.send_header("Set-Cookie", self._build_session_cookie(sid))
        self.end_headers()

    def handle_logout_get(self) -> None:
        sid = self._read_cookie("tuxforge_pages_session")
        if sid:
            self.app.delete_edit_session(sid)
        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", "/")
        self.send_header("Set-Cookie", self._clear_session_cookie())
        self.end_headers()

    # --- session helpers ---------------------------------------------------

    def current_edit_user(self) -> dict | None:
        sid = self._read_cookie("tuxforge_pages_session")
        return self.app.get_edit_session(sid) if sid else None

    def require_edit_login(self) -> bool:
        if self.current_edit_user() is not None:
            return True
        self.redirect(self.app.oauth_login_url(self.path))
        return False

    def _read_cookie(self, name: str) -> str:
        raw = self.headers.get("Cookie", "")
        if not raw:
            return ""
        c = SimpleCookie()
        c.load(raw)
        m = c.get(name)
        return m.value if m else ""

    def _build_session_cookie(self, sid: str) -> str:
        parts = [f"tuxforge_pages_session={sid}", "HttpOnly", "Path=/", "SameSite=Lax"]
        if self.app.public_url.startswith("https://"):
            parts.append("Secure")
        return "; ".join(parts)

    def _clear_session_cookie(self) -> str:
        parts = [
            "tuxforge_pages_session=",
            "Expires=Thu, 01 Jan 1970 00:00:00 GMT",
            "Max-Age=0", "HttpOnly", "Path=/", "SameSite=Lax",
        ]
        if self.app.public_url.startswith("https://"):
            parts.append("Secure")
        return "; ".join(parts)

    def redirect(self, location: str) -> None:
        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", location)
        self.end_headers()

    # --- file serving ------------------------------------------------------

    def serve_site(self, owner: str, repo: str, parts: list[str]) -> None:
        site = self.app.db.get_site(owner, repo)
        if site is None:
            self.send_bootstrap_error(HTTPStatus.NOT_FOUND, "Site Not Found", "This site is not configured.")
            return
        root = self.app.publish_dir(owner, repo, site["root_folder"] or "")
        if not root.exists():
            self.send_bootstrap_error(
                HTTPStatus.NOT_FOUND, "Site Not Found", "This repository has not been deployed yet."
            )
            return
        self._serve_from_root(root, parts)

    def _serve_from_root(self, root: Path, parts: list[str]) -> None:
        target = root.joinpath(*parts) if parts else root
        target = self._normalize(root, target)
        if target is None:
            self.send_bootstrap_error(HTTPStatus.FORBIDDEN, "Forbidden", "Access outside published site.")
            return
        if target.is_dir():
            index = target / "index.html"
            if index.is_file():
                self._serve_file(index, HTTPStatus.OK)
                return
            self._serve_404(root, "The requested page was not found.")
            return
        if target.is_file():
            self._serve_file(target, HTTPStatus.OK)
            return
        self._serve_404(root, "The requested file was not found.")

    def _normalize(self, root: Path, target: Path) -> Path | None:
        try:
            rr = root.resolve()
            rt = target.resolve()
        except FileNotFoundError:
            rr = root.resolve()
            rt = target.parent.resolve() / target.name
        if os.path.commonpath([str(rr), str(rt)]) != str(rr):
            return None
        return rt

    def _serve_404(self, root: Path, fallback: str) -> None:
        p = root / "404.html"
        if p.is_file():
            self._serve_file(p, HTTPStatus.NOT_FOUND)
        else:
            self.send_bootstrap_error(HTTPStatus.NOT_FOUND, "Not Found", fallback)

    def _serve_file(self, path: Path, status: HTTPStatus) -> None:
        content_type = mimetypes.guess_type(str(path))[0] or "application/octet-stream"
        stat = path.stat()
        etag = f'W/"{stat.st_mtime_ns:x}-{stat.st_size:x}"'
        last_modified = formatdate(stat.st_mtime, usegmt=True)

        if self.headers.get("If-None-Match") == etag:
            self.send_response(HTTPStatus.NOT_MODIFIED)
            self.send_header("ETag", etag)
            self.send_header("Last-Modified", last_modified)
            self.end_headers()
            return

        ims = self.headers.get("If-Modified-Since")
        if ims:
            try:
                if stat.st_mtime <= parsedate_to_datetime(ims).timestamp():
                    self.send_response(HTTPStatus.NOT_MODIFIED)
                    self.send_header("ETag", etag)
                    self.send_header("Last-Modified", last_modified)
                    self.end_headers()
                    return
            except Exception:
                pass

        cc = "no-cache" if content_type.startswith("text/html") else "public, max-age=300, stale-while-revalidate=60"
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(stat.st_size))
        self.send_header("Cache-Control", cc)
        self.send_header("ETag", etag)
        self.send_header("Last-Modified", last_modified)
        self.end_headers()
        with path.open("rb") as fh:
            shutil.copyfileobj(fh, self.wfile)

    # --- response helpers --------------------------------------------------

    def send_html(self, status: HTTPStatus, body: str) -> None:
        data = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def send_text(self, status: HTTPStatus, body: str) -> None:
        data = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def send_bootstrap_error(self, status: HTTPStatus, title: str, message: str) -> None:
        self.send_html(status, self.app.render_error_page(int(status), title, message))

    def log_message(self, format: str, *args) -> None:
        return


# ---------------------------------------------------------------------------
# Server
# ---------------------------------------------------------------------------

class Server(ThreadingHTTPServer):
    def __init__(self, addr: tuple[str, int], handler: type[BaseHTTPRequestHandler], app: RepoServer):
        self.app = app
        super().__init__(addr, handler)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> int:
    load_dotenv()

    try:
        gitea_url        = get_env("GITEA_URL")
        token            = get_env("GITEA_TOKEN")
        main_domain      = get_env("MAIN_DOMAIN")
        public_url       = get_env("PUBLIC_URL")
        oauth_client_id  = get_env("FORGEJO_OAUTH_CLIENT_ID")
        oauth_client_secret = get_env("FORGEJO_OAUTH_CLIENT_SECRET")

        pages_subdomain  = os.getenv("PAGES_SUBDOMAIN", f"pages.{main_domain}").strip() or f"pages.{main_domain}"
        instance_name    = os.getenv("INSTANCE_NAME", "Tuxforge Pages").strip() or "Tuxforge Pages"
        preferred_branch = os.getenv("GITEA_BRANCH_NAME", "pages").strip() or "pages"
        port             = int(os.getenv("WEB_PORT", "8080"))
        clone_root       = Path(os.getenv("PAGES_ROOT", "./pages")).expanduser().resolve()
        db_path          = Path(os.getenv("PAGES_DB", "./pages.db")).expanduser().resolve()
        logo_url         = os.getenv("LOGO_URL", "https://git.tuxworld.nl/assets/img/hero.png").strip() or "https://git.tuxworld.nl/assets/img/hero.png"
        favicon_url      = os.getenv("FAVICON_URL", "").strip() or logo_url
        templates_dir    = Path(os.getenv("TEMPLATES_DIR", "./templates")).expanduser().resolve()
        verify_ssl       = parse_bool("GITEA_VERIFY_SSL", default=True)
        webhook_url      = os.getenv("PAGES_WEBHOOK_URL", "").strip() or f"https://{main_domain}"
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    db = Database(db_path)
    app = RepoServer(
        gitea_url, token, verify_ssl, clone_root, db,
        main_domain, pages_subdomain,
        instance_name, preferred_branch, logo_url, favicon_url,
        public_url, oauth_client_id, oauth_client_secret,
        webhook_url, templates_dir,
    )
    server = Server(("0.0.0.0", port), RequestHandler, app)
    print(f"Listening on      http://0.0.0.0:{port}")
    print(f"Main domain:      {main_domain}")
    print(f"Pages subdomain:  {pages_subdomain}")
    print(f"Clone root:       {clone_root}")
    print(f"Database:         {db_path}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
