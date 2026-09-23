#!/usr/bin/env python3
"""Persistent, local Lean checks using leanclient 0.13.2 and the pinned toolchain.

Install once: python -m pip install --target Scratch/lean-lsp-deps leanclient==0.13.2
Start one bounded session per independent editing stream:
  python scripts/lean-lsp-check.py start --session root
  python scripts/lean-lsp-check.py check Scratch/LocalLeanSmoke.lean --session root --timeout 300
  python scripts/lean-lsp-check.py close Scratch/LocalLeanSmoke.lean --session root
  python scripts/lean-lsp-check.py stop --session root
Use `serve` instead of `start` to keep the helper in the foreground.

Checks read disk but never write Lean files; --text-file checks an alternative
buffer for the target file. Two documents are kept open per session by default.
Close and reopen a file after rebuilding an imported module. Dependency builds
and cache downloads are disabled. Within one session, checks are serialized;
the root, transport, sampler and decider sessions run independently.
An explicit waitForDiagnostics reply is required; silence never means success.
Logs and the authenticated loopback endpoint descriptor live in ignored Scratch.
This is an iteration helper; `lean-local.ps1 Build/Validate` remains the final check.
"""

from __future__ import annotations

import argparse
from collections import OrderedDict
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import importlib.metadata
import json
import logging
import os
from pathlib import Path
import secrets
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request


ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / "Scratch"
STATE = SCRATCH / "lean-lsp-state.json"
LOG = SCRATCH / "lean-lsp-check.log"
PIN = "0.13.2"


def fingerprint() -> str:
    digest = hashlib.sha256()
    for name in ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"):
        path = ROOT / name
        if path.exists():
            digest.update(name.encode())
            digest.update(path.read_bytes())
    return digest.hexdigest()


def configure(threads: int) -> None:
    """Only this helper and its descendants inherit these environment settings."""
    config_path = SCRATCH / "lean-local-config.json"
    config = json.loads(config_path.read_text(encoding="utf-8-sig")) if config_path.exists() else {}
    profile = Path(os.environ.get("USERPROFILE", Path.home()))
    elan = Path(config.get("elanHome") or os.environ.get("ELAN_HOME") or profile / ".elan")
    cache = Path(config.get("mathlibCacheDir") or os.environ.get("MATHLIB_CACHE_DIR")
                 or profile / "MIPRECache" / "mathlib")
    os.environ["ELAN_HOME"] = str(elan.resolve())
    os.environ["MATHLIB_CACHE_DIR"] = str(cache.resolve())
    os.environ["LEAN_NUM_THREADS"] = str(threads)
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    suffix = ".exe" if os.name == "nt" else ""
    # `elan run` without --install refuses a missing toolchain. The resulting
    # PATH selects its real Lake binary, so shims cannot silently install one.
    prefix = subprocess.run(
        [str(elan / "bin" / ("elan" + suffix)), "run", toolchain, "lean", "--print-prefix"],
        cwd=ROOT, capture_output=True, text=True, check=True, timeout=30,
        creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0,
    ).stdout.strip()
    lake = Path(prefix) / "bin" / ("lake" + suffix)
    if not lake.is_file():
        raise RuntimeError(f"Pinned Lake binary missing: {lake}")
    os.environ["PATH"] = str(lake.parent) + os.pathsep + os.environ.get("PATH", "")
    os.environ["LAKE"] = str(lake)
    os.environ["ELAN_TOOLCHAIN"] = toolchain
    count = int(os.environ.get("GIT_CONFIG_COUNT", "0"))
    if not 0 <= count < 2**31 - 1:
        raise ValueError("Invalid GIT_CONFIG_COUNT")
    os.environ[f"GIT_CONFIG_KEY_{count}"] = "core.longpaths"
    os.environ[f"GIT_CONFIG_VALUE_{count}"] = "true"
    os.environ["GIT_CONFIG_COUNT"] = str(count + 1)


def position(text: str, offset: int) -> dict:
    prefix = text[:offset]
    return {"line": prefix.count("\n"),
            "character": len(prefix.rsplit("\n", 1)[-1].encode("utf-16-le")) // 2}


def edit(old: str, new: str) -> dict:
    """Send only the changed span, preserving Lean's earlier command snapshots."""
    start = 0
    limit = min(len(old), len(new))
    while start < limit and old[start] == new[start]:
        start += 1
    suffix = 0
    while suffix < limit - start and old[-1 - suffix] == new[-1 - suffix]:
        suffix += 1
    end_old, end_new = len(old) - suffix, len(new) - suffix
    return {"range": {"start": position(old, start), "end": position(old, end_old)},
            "text": new[start:end_new]}


class Checker:
    def __init__(self, base_client, max_open_files):
        self.base_client = base_client
        self.client = None
        self.documents = OrderedDict()
        self.versions = {}
        self.diagnostics = {}
        self.config_hash = fingerprint()
        self.lock = threading.Lock()
        self.max_open_files = max_open_files
        self.current = None

    def close(self):
        if self.client is not None:
            try:
                self.client.close()
            finally:
                self.client = None
        self.documents.clear()
        self.diagnostics.clear()

    def close_file(self, filename):
        path = (ROOT / filename).resolve()
        if not path.is_relative_to(ROOT):
            raise ValueError("Expected a file within this repository.")
        uri = path.as_uri()
        if uri in self.documents:
            self.client._send_notification("textDocument/didClose", {"textDocument": {"uri": uri}})
            del self.documents[uri]
            self.diagnostics = {key: value for key, value in self.diagnostics.items() if key[0] != uri}

    def incomplete(self):
        if self.current is None:
            return {}
        current = dict(self.current)
        current["elapsed_seconds"] = round(time.monotonic() - current.pop("started"), 3)
        uri = current.pop("uri")
        current["diagnostics"] = self.diagnostics.get((uri, current["version"]), [])
        return current

    def on_diagnostics(self, message):
        p = message["params"]
        key = (p["uri"], p.get("version"))
        if p.get("isIncremental", False):
            self.diagnostics.setdefault(key, []).extend(p["diagnostics"])
        else:
            self.diagnostics[key] = p["diagnostics"]

    def check(self, request):
        self.current = None
        if fingerprint() != self.config_hash:
            raise RuntimeError("Project configuration changed; stop and restart this helper.")
        path = (ROOT / request["file"]).resolve()
        if not path.is_relative_to(ROOT) or path.suffix != ".lean" or not path.is_file():
            raise ValueError("Expected an existing .lean file within this repository.")
        timeout = float(request.get("timeout", 300))
        if not 0 < timeout <= 3600:
            raise ValueError("Timeout must be between 0 and 3600 seconds.")
        started = time.monotonic()
        text = request.get("text")
        if text is None:
            text = path.read_text(encoding="utf-8-sig")
        text = text.replace("\r\n", "\n")
        uri = path.as_uri()
        self.current = {"file": str(path.relative_to(ROOT)), "uri": uri, "version": None,
                        "sha256": hashlib.sha256(text.encode()).hexdigest(), "started": started}
        if self.client is None:
            # Instantiate explicitly so even an initialization timeout can close
            # the subprocess that the library has already spawned.
            self.client = self.base_client.__new__(self.base_client)
            self.client.request_timeout = timeout
            self.client.__init__(str(ROOT), initial_build=False, prevent_cache_get=True)
            self.client._register_notification_handler(
                "textDocument/publishDiagnostics", self.on_diagnostics)
        if uri not in self.documents:
            if len(self.documents) >= self.max_open_files:
                oldest, _ = self.documents.popitem(last=False)
                self.client._send_notification("textDocument/didClose", {"textDocument": {"uri": oldest}})
                self.diagnostics = {key: value for key, value in self.diagnostics.items() if key[0] != oldest}
            # Reopening a URI must not reuse an old version number: late
            # diagnostics from its discarded worker must remain distinguishable.
            version = self.versions.get(uri, 0) + 1
            self.current["version"] = version
            self.client._send_notification("textDocument/didOpen", {
                "dependencyBuildMode": "never",
                "textDocument": {"uri": uri, "languageId": "lean4", "version": version, "text": text}})
        else:
            old, version = self.documents[uri]
            self.current["version"] = version
            if old != text:
                version += 1
                self.current["version"] = version
                self.diagnostics = {key: value for key, value in self.diagnostics.items() if key[0] != uri}
                self.client._send_notification("textDocument/didChange", {
                    "textDocument": {"uri": uri, "version": version}, "contentChanges": [edit(old, text)]})
        self.documents[uri] = (text, version)
        self.versions[uri] = version
        self.documents.move_to_end(uri)
        remaining = timeout - (time.monotonic() - started)
        if remaining <= 0:
            raise TimeoutError("Lean initialization consumed the check timeout.")
        self.client._send_request_sync("textDocument/waitForDiagnostics",
                                       {"uri": uri, "version": version}, timeout=remaining)
        diagnostics = self.diagnostics.get((uri, version), [])
        # This exact version's explicit protocol acknowledgment is the completion
        # barrier. Lean emits no diagnostics notification for some clean files.
        success = not any(item.get("severity") == 1 for item in diagnostics)
        return {"success": success, "completed": True, "exit_code": 0 if success else 1,
                "file": str(path.relative_to(ROOT)), "version": version,
                "sha256": hashlib.sha256(text.encode()).hexdigest(),
                "elapsed_seconds": round(time.monotonic() - started, 3), "diagnostics": diagnostics}


def serve(threads, max_open_files):
    SCRATCH.mkdir(exist_ok=True)
    sys.path.insert(0, str(SCRATCH / "lean-lsp-deps"))
    if importlib.metadata.version("leanclient") != PIN:
        raise RuntimeError(f"Install leanclient=={PIN} as documented in --help.")
    from leanclient.base_client import BaseLeanLSPClient

    class LocalClient(BaseLeanLSPClient):
        def _send_request_sync(self, method, params, timeout=None):
            return super()._send_request_sync(method, params,
                timeout=self.request_timeout if timeout is None else timeout)

    configure(threads)
    logging.basicConfig(filename=LOG, level=logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", encoding="utf-8")
    checker = Checker(LocalClient, max_open_files)
    token = secrets.token_urlsafe(32)

    class Handler(BaseHTTPRequestHandler):
        def do_POST(self):
            if not secrets.compare_digest(self.headers.get("Authorization", ""), "Bearer " + token):
                self.send_error(403)
                return
            if not checker.lock.acquire(blocking=False):
                self.send_error(409, "A Lean check is already running.")
                return
            result = {}
            action = None
            try:
                size = int(self.headers.get("Content-Length", "0"))
                if not 0 < size <= 8 * 1024 * 1024:
                    raise ValueError("Invalid request length.")
                request = json.loads(self.rfile.read(size))
                action = request["action"]
                if action == "check":
                    result = checker.check(request)
                elif action == "status":
                    result = {"success": True, "pid": os.getpid(), "root": str(ROOT),
                              "open_files": len(checker.documents), "exit_code": 0}
                elif action == "close":
                    checker.close_file(request["file"])
                    result = {"success": True, "exit_code": 0}
                elif action == "stop":
                    checker.close()
                    result = {"success": True, "exit_code": 0}
                    threading.Thread(target=server.shutdown, daemon=True).start()
                else:
                    raise ValueError("Unknown action.")
            except Exception as exc:
                logging.exception("Lean check failed")
                result = {**(checker.incomplete() if action == "check" else {}),
                          "success": False, "completed": False,
                          "exit_code": 124 if isinstance(exc, TimeoutError) else 2,
                          "error": str(exc) or ("Lean check timed out." if isinstance(exc, TimeoutError)
                                                else type(exc).__name__)}
                try:
                    checker.close()
                except Exception:
                    logging.exception("Closing failed Lean client")
            finally:
                checker.lock.release()
            logging.info("Result: %s", json.dumps(result, ensure_ascii=False))
            body = json.dumps(result, ensure_ascii=False).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, fmt, *args):
            logging.info(fmt, *args)

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    # Exclusive creation prevents two helpers for this checkout. A stale file
    # requires explicit removal after verifying its PID is no longer running.
    try:
        with STATE.open("x", encoding="utf-8") as output:
            json.dump({"port": server.server_port, "token": token, "pid": os.getpid(), "root": str(ROOT)}, output)
    except Exception:
        server.server_close()
        raise
    print(f"Lean checker ready (PID {os.getpid()}); endpoint stored in {STATE}", flush=True)
    try:
        server.serve_forever()
    finally:
        checker.close()
        server.server_close()
        STATE.unlink(missing_ok=True)


def main():
    global STATE, LOG
    # Windows redirected consoles commonly default to a legacy code page, while
    # Lean diagnostics contain mathematical Unicode identifiers.
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("action", choices=("start", "serve", "check", "close", "status", "stop"))
    parser.add_argument("file", nargs="?")
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--threads", type=int, choices=range(1, 257), default=4, metavar="N")
    parser.add_argument("--session", choices=("default", "root", "transport", "sampler", "decider"), default="default")
    parser.add_argument("--max-open-files", type=int, choices=range(1, 5), default=2, metavar="N")
    parser.add_argument("--text-file", type=Path, help="Check this buffer without modifying the target file")
    args = parser.parse_args()
    if args.session != "default":
        STATE = SCRATCH / f"lean-lsp-{args.session}-state.json"
        LOG = SCRATCH / f"lean-lsp-{args.session}-check.log"
    if args.action == "start":
        if STATE.exists():
            raise RuntimeError(f"Session already has a state file: {STATE}; use status or stop first.")
        SCRATCH.mkdir(exist_ok=True)
        startup_log = LOG.with_name(LOG.stem + "-startup.log")
        with startup_log.open("ab") as output:
            process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "serve",
                "--session", args.session, "--threads", str(args.threads),
                "--max-open-files", str(args.max_open_files)], cwd=ROOT,
                stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT,
                creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0)
        deadline = time.monotonic() + 35
        while not STATE.exists() and process.poll() is None and time.monotonic() < deadline:
            time.sleep(0.05)
        if not STATE.exists():
            if process.poll() is None:
                process.terminate()
            raise RuntimeError(f"Helper did not start; inspect {startup_log}")
        print(json.dumps({"success": True, "pid": process.pid, "session": args.session, "log": str(LOG)}))
        return 0
    if args.action == "serve":
        serve(args.threads, args.max_open_files)
        return 0
    if args.action in ("check", "close") and not args.file:
        parser.error(f"{args.action} requires a Lean file")
    state = json.loads(STATE.read_text(encoding="utf-8"))
    if state.get("root") != str(ROOT):
        raise RuntimeError("Checker belongs to a different repository.")
    request = {"action": args.action, "file": args.file, "timeout": args.timeout}
    if args.text_file:
        request["text"] = args.text_file.read_text(encoding="utf-8-sig")
    message = urllib.request.Request(f"http://127.0.0.1:{int(state['port'])}/",
        data=json.dumps(request).encode(), headers={"Authorization": "Bearer " + state["token"],
                                                   "Content-Type": "application/json"}, method="POST")
    # Local control traffic must not follow a user's HTTP proxy configuration.
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    with opener.open(message, timeout=args.timeout + 15) as response:
        result = json.load(response)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return result["exit_code"]


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, importlib.metadata.PackageNotFoundError) as error:
        print(f"Lean checker: {error}", file=sys.stderr)
        raise SystemExit(2)
