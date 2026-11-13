"""Live, process-local publication of successive committed game candidates.

No persisted verdict is accepted. The first pass calls the complete native
collector; subsequent passes reuse its results only under identical bindings.
This deliberately conservative Linux-only protocol never rebases or commits.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import site
import sysconfig
import subprocess
import sys

import push
import status
from rompath import rom_path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_pin(path):
    path = Path(path)
    return (str(path.resolve()), digest(path.read_bytes()))


def tree_pin(root, *, snapshot=False, exclude=()):
    """Bind all inputs, including nonstandard profile artifacts, not just headers."""
    root = Path(root)
    records = {}
    if not root.exists():
        return records
    if root.is_file():
        return {".": file_pin(root)}
    for directory, directories, files in os.walk(root, followlinks=False):
        here = Path(directory)
        directories[:] = [name for name in directories if name not in exclude]
        if snapshot and here == root:
            directories[:] = [name for name in directories if name != "build"]
        for name in directories:
            if (here / name).is_symlink():
                raise ValueError("session refuses directory symlinks in pinned inputs")
        for name in sorted(files):
            path = here / name
            relative = path.relative_to(root).as_posix()
            if snapshot and path.is_symlink():
                raise ValueError("session refuses symlinks in committed inputs")
            # Snapshot paths change when an identical commit is re-archived.
            records[relative] = digest(path.read_bytes()) if snapshot else file_pin(path)
    return records


def object_pin(value):
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def runtime_pin():
    """Pin Python's search trees, toolkit, selected binaries and native libraries.

    Only the toolkit, standard library and capstone are verifier dependencies.
    Pin their possible resolutions on every allowed search path, including
    startup customization and bytecode. Refuse broad/custom search roots.
    Environment values are represented only by an opaque combined digest.
    """
    if sys.platform != "linux":
        raise ValueError("publication sessions currently require Linux runtime pinning")
    import match
    import capstone
    stdlib = Path(sysconfig.get_path("stdlib")).resolve()
    capstone_root = Path(capstone.__file__).resolve().parent
    executables = [sys.executable, "/bin/sh", match.DEFAULT_CC,
                   match.DEFAULT_CPP, match.DEFAULT_AS, match.DEFAULT_OBJCOPY,
                   match.DEFAULT_LD, "git", "tar", "mkdir", "mktemp", "rm", "rmdir"]
    resolved = []
    for command in executables:
        path = shutil.which(os.path.expandvars(command))
        if path is None:
            raise ValueError(f"cannot pin required executable: {command}")
        resolved.append(path)
    cc1 = subprocess.run([resolved[3], "-print-prog-name=cc1"],
                         capture_output=True, text=True, check=True).stdout.strip()
    if not Path(cc1).is_file():
        raise ValueError("cannot pin the preprocessor's cc1")
    resolved.append(cc1)
    # Child-only stdlib extensions must bind their dependencies too, even when
    # this leader has not imported them. This is bounded to native Python inputs.
    resolved += [str(path) for root in (stdlib / "lib-dynload", capstone_root)
                 for path in root.rglob("*.so")]
    libraries = set()
    for path in resolved:
        result = subprocess.run(["ldd", path], capture_output=True, text=True)
        if result.returncode and "not a dynamic executable" not in result.stderr + result.stdout and \
                "statically linked" not in result.stderr + result.stdout:
            raise ValueError(f"cannot pin executable libraries: {path}")
        for line in result.stdout.splitlines():
            if "not found" in line:
                raise ValueError("unresolved native runtime library")
            libraries.update(re.findall(r"(?:=>\s+|^\s*)(/\S+)", line))
    for line in Path("/proc/self/maps").read_text().splitlines():
        fields = line.split(None, 5)
        if len(fields) == 6 and fields[5].startswith("/"):
            libraries.add(fields[5])
    allowed = {stdlib, stdlib / "lib-dynload", Path(push.KIT).resolve(), capstone_root.parent,
               *(Path(path).resolve() for path in site.getsitepackages()),
               Path(site.getusersitepackages()).resolve()}
    trees = {str(stdlib): object_pin(tree_pin(stdlib, exclude=("site-packages", "dist-packages"))),
             str(Path(push.KIT)): object_pin(tree_pin(push.KIT)),
             str(capstone_root): object_pin(tree_pin(capstone_root))}
    for entry in sys.path:
        if not entry:
            raise ValueError("session refuses current-directory Python search paths; run push.py directly")
        path = Path(entry).resolve()
        if path.suffix == ".zip" and path.parent == stdlib.parent:
            trees[str(path)] = object_pin(tree_pin(path))
            continue
        if path not in allowed or path in (Path.home(), Path("/"), Path.cwd()):
            raise ValueError("session refuses unbounded/custom Python search paths")
        if path in (stdlib, stdlib / "lib-dynload", Path(push.KIT).resolve()):
            continue
        # Pin directory membership and every possible stdlib/capstone resolution;
        # unrelated package bodies cannot affect native verifier imports.
        children = sorted(path.iterdir()) if path.exists() else []
        trees[str(path) + ":members"] = object_pin([p.name for p in children])
        for child in children:
            if child.stem in sys.stdlib_module_names or child.stem in (
                    "capstone", "sitecustomize", "usercustomize", "__pycache__") or \
                    child.suffix in (".pth", ".py"):
                trees[str(child)] = object_pin(tree_pin(child))
    # Existing loaded startup modules outside those trees are also inputs.
    for module in list(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if filename and Path(filename).is_file():
            resolved_file = Path(filename).resolve()
            if not any(resolved_file.is_relative_to(root) for root in
                       (stdlib, Path(push.KIT).resolve(), capstone_root)):
                trees[str(resolved_file)] = object_pin(file_pin(filename))
    if sys.pycache_prefix:
        for root in (stdlib, Path(push.KIT).resolve(), capstone_root):
            cached = Path(sys.pycache_prefix) / str(root).lstrip("/")
            trees[str(cached)] = object_pin(tree_pin(cached, exclude=("site-packages", "dist-packages")))

    return {
        "environment": object_pin(dict(os.environ)),
        "python": (sys.version, sys.implementation.cache_tag, list(sys.path)),
        "trees": trees,
        "tools": object_pin(tree_pin(push.KIT)),
        "binaries": {path: file_pin(path) for path in sorted(set(resolved) | libraries)},
    }


def context_independent_preprocessing(root):
    """Conservative session-only admission; native dependency checks still run.

    Translate trigraphs and splice physical lines before scanning. Token pasting
    and universal character escapes are refused, so context tokens cannot be
    synthesized indirectly. False positives in comments/strings are deliberate.
    """
    trigraphs = dict(zip("=/'()!<>-", "#\\^[]|{}~"))
    for directory in (Path(root) / "src", Path(root) / "include"):
        for path in directory.rglob("*"):
            if not path.is_file() or (directory.name == "src" and path.suffix not in (".c", ".h")):
                continue
            text = path.read_text()
            for suffix, replacement in trigraphs.items():
                text = text.replace("??" + suffix, replacement)
            text = re.sub(r"\\[ \t]*\r?\n", "", text)
            text = text.replace("%:", "#")
            tokens = r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|/\*.*?\*/|//[^\n]*'
            text = re.sub(tokens, lambda token: " " if token[0].startswith(("/*", "//"))
                          else token[0], text, flags=re.S)
            if re.search(r"#\s*#|\\[uU]|__has_[A-Za-z_]*|__(?:DATE|TIME|TIMESTAMP|FILE|BASE_FILE|FILE_NAME|COUNTER)__", text):
                raise ValueError("session refuses context-dependent preprocessing or token synthesis")


def snapshot_parts(root):
    context_independent_preprocessing(root)
    manifest = tree_pin(root, snapshot=True)
    sources = {}
    for name in manifest:
        path = Path(name)
        if path.parts[0] == "src" and path.suffix == ".c":
            if not re.fullmatch(r"[0-9A-F]{8}", path.stem) or path.stem in sources:
                raise ValueError("session requires unique canonical source addresses")
            sources[path.stem] = name
    text_entries = []
    for line in (Path(root) / "symbols/functions.txt").read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            text_entries.append(int(line.split()[0], 16))
    if len(text_entries) != len(set(text_entries)):
        raise ValueError("duplicate text function-index entries")
    entries = json.loads((Path(root) / "config/functions.json").read_text())
    addresses = [int(entry["rom"], 16) for entry in entries]
    if len(addresses) != len(set(addresses)):
        raise ValueError("duplicate function-index entries")
    for address in sources:
        if int(address, 16) not in addresses or int(address, 16) not in text_entries:
            raise ValueError(f"source {address} has no unique indexed entry")
    bindings = {}
    for address, source in sources.items():
        report = f"docs/match/{address}.md"
        if report not in manifest:
            raise ValueError(f"source {address} has no committed match report")
        bindings[source] = (manifest[source], manifest[report])
    shared = {name: value for name, value in manifest.items()
              if name not in sources.values() and
              not re.fullmatch(r"docs/match/[0-9A-F]{8}\.md", name) and
              name not in ("README.md", "docs/status.md")}
    # Unused reports are also immutable shared dependencies. Newly added reports
    # may only accompany a new addressed source.
    reports = {name: value for name, value in manifest.items()
               if re.fullmatch(r"docs/match/[0-9A-F]{8}\.md", name)}
    return manifest, shared, bindings, reports


def check_complete_bodies(results):
    bodies = sorted(body for result in results.values() for body in result[3])
    for index, (address, size, _) in enumerate(bodies):
        if not isinstance(size, int) or size <= 0:
            raise ValueError(f"{address:08X}: missing complete verified body extent")
        if index and address < bodies[index - 1][0] + bodies[index - 1][1]:
            raise ValueError(f"{address:08X}: overlapping complete verified bodies")


class VerificationSession:
    """The only result store is this object's live, freshly populated memory."""
    def __init__(self, repo, branch, remote, base, *, jobs=1, worker_processes=0):
        self.repo, self.branch, self.remote = repo, branch, remote
        self.base = base
        self.jobs, self.worker_processes = jobs, worker_processes
        self.pid = os.getpid()
        self.runtime = runtime_pin()
        self.rom = file_pin(rom_path(repo))
        self.shared = self.bindings = self.reports = None
        self.results = {}
        self.verified = None
        self.lease = push.capture_force_lease(repo, remote, branch)
        if self.lease is None:
            raise ValueError("cannot establish exact destination lease")

    def authenticate(self):
        if os.getpid() != self.pid:
            raise ValueError("publication session cannot cross a process boundary")
        if runtime_pin() != self.runtime or file_pin(rom_path(self.repo)) != self.rom:
            self.results.clear()
            self.verified = None
            raise ValueError("publication runtime, tool, environment or ROM changed; restart session")

    def capture(self, expected):
        snapshot = push.publish_snapshot(self.repo, self.branch, require_clean=False)
        if snapshot is None or snapshot[1] != expected:
            raise ValueError("candidate is not the captured current branch HEAD")
        return snapshot

    def history(self):
        remote, separator, branch = self.base.partition("/")
        if not separator or not remote or not branch or branch.startswith("-"):
            raise ValueError("session base must be REMOTE/BRANCH")
        code, _ = push.git("fetch", "--no-tags", remote, f"refs/heads/{branch}", repo=self.repo)
        if code:
            raise ValueError("could not fetch session base")
        code, text = push.git("rev-parse", "--verify", "FETCH_HEAD^{commit}", repo=self.repo)
        if code or not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", text.strip()):
            raise ValueError("could not pin session base")
        base = text.strip()
        if not push.check_history(self.repo, self.remote, self.branch,
                                  base=(base, self.base)):
            raise ValueError("candidate is not linear and current with session base")
        return remote, branch, base

    def verify(self, expected):
        self.verified = None
        self.authenticate()
        snapshot = self.capture(expected)
        self.history()
        if not push.check_no_rom_data(self.repo, commit=expected):
            raise ValueError("candidate tracks forbidden game data")
        tree = push.committed_tree(self.repo, expected)
        if tree is None:
            raise ValueError("could not archive candidate")
        previous_rom = os.environ.get("FFTA_ROM")
        try:
            if (Path(tree) / "build").exists():
                raise ValueError("session refuses committed build inputs")
            manifest, shared, bindings, reports = snapshot_parts(tree)
            if shared.get("baserom.bin") != self.rom[1]:
                raise ValueError("snapshot ROM differs from pinned ROM")
            if self.shared is not None:
                added = bindings.keys() - self.bindings.keys()
                removed_parked = {name for name in self.shared.keys() - shared.keys()
                                  if any(name in (f"Parked/{Path(source).stem}/README.md",
                                                  f"Parked/{Path(source).stem}/{Path(source).stem}.c")
                                         for source in added)}
                expected_shared = {name: value for name, value in self.shared.items()
                                   if name not in removed_parked}
                if shared != expected_shared:
                    raise ValueError("shared committed dependency changed; restart session")
                if not self.bindings.keys() <= bindings.keys():
                    raise ValueError("candidate removed or moved a verified source")
                added_reports = {f"docs/match/{Path(path).stem}.md"
                                 for path in bindings.keys() - self.bindings.keys()}
                if reports.keys() - self.reports.keys() - added_reports:
                    raise ValueError("unowned report addition is not additive publication")
                if not self.reports.keys() <= reports.keys():
                    raise ValueError("candidate removed a report")
                # Reports can contain profile helper bindings. If an existing
                # source/report changes, invalidate the whole native result set.
                if any(bindings[path] != value for path, value in self.bindings.items()) or \
                        any(reports[path] != value for path, value in self.reports.items()):
                    self.results.clear()
            results = dict(self.results)
            reused = len(results)
            os.environ["FFTA_ROM"] = str(Path(tree) / "baserom.bin")
            progress = {}
            counts = status.collect(tree, True, jobs=self.jobs,
                                    worker_processes=self.worker_processes,
                                    progress=progress, _publication_results=results)
            tf, mf, tb, mb, problems, lf, lb = counts
            if problems:
                raise ValueError("native verification failed: " + "; ".join(problems))
            check_complete_bodies(results)
            if not push.check_plausible(tree) or not push.check_reports(tree):
                raise ValueError("native plausibility/report gate failed")
            badge = push.badge_base(self.repo) or os.environ.get("FFTA_BADGE_BASE") or ""
            block, _, _ = status.render(tf, mf, tb, mb, problems, badge_base=badge,
                                        late_f=lf, late_b=lb, progress=progress or None)
            readme = (Path(tree) / "README.md").read_text()
            start, end = readme.find(status.START), readme.find(status.END)
            current = readme[start:end + len(status.END)] if 0 <= start < end else ""
            status_file = Path(tree) / "docs/status.md"
            progress_ok = current.strip() == block.strip() and (
                not status_file.exists() or status_file.read_text().strip() == block.strip())
            if tree_pin(tree, snapshot=True) != manifest:
                raise ValueError("committed snapshot mutated during verification")
        finally:
            if previous_rom is None:
                os.environ.pop("FFTA_ROM", None)
            else:
                os.environ["FFTA_ROM"] = previous_rom
            shutil.rmtree(tree, ignore_errors=True)
        self.authenticate()
        self.capture(expected)
        self.shared, self.bindings, self.reports = shared, bindings, reports
        self.results = results
        if progress_ok:
            self.verified = snapshot
        return {"event": "verified" if progress_ok else "progress-stale",
                "commit": expected, "reused": reused, "fresh": len(results) - reused,
                "snapshot_sha256": object_pin(manifest),
                "runtime_sha256": object_pin(self.runtime), "rom_sha256": self.rom[1],
                "status_block": block}

    def publish(self, expected):
        self.authenticate()
        snapshot = self.capture(expected)
        if self.verified != snapshot:
            raise ValueError("commit has not passed every gate in this live session")
        remote, branch, base = self.history()
        # Recheck the destination and upstream immediately before publication;
        # the actual destination update remains protected by the current exact lease.
        if push.capture_force_lease(self.repo, self.remote, self.branch) != self.lease:
            raise ValueError("destination changed since the session lease was captured")
        code, output = push.git("ls-remote", "--exit-code", "--refs", remote,
                                f"refs/heads/{branch}", repo=self.repo)
        if code or output.strip() != f"{base}\trefs/heads/{branch}":
            raise ValueError("upstream base changed before publication")
        self.authenticate()
        self.capture(expected)
        if not push.do_push(self.repo, self.remote, self.branch, force=True,
                            lease=self.lease, commit=expected):
            raise ValueError("conditional native push failed")
        if not os.environ.get("FFTA_PUSH_DRY"):
            self.lease = (self.lease[0], expected)


def emit(event):
    print(json.dumps(event, sort_keys=True), flush=True)


def run_session(args):
    repo = os.path.abspath(args.repo or push.DEFAULT_REPO)
    if not push.is_checkout_root(repo):
        raise ValueError("publication session requires a game checkout root")
    session = VerificationSession(repo, args.branch, args.remote, args.session_base,
                                  jobs=args.jobs, worker_processes=args.worker_processes or 0)
    snapshot = push.publish_snapshot(repo, args.branch, require_clean=False)
    if snapshot is None:
        raise ValueError("could not capture initial candidate")
    emit(session.verify(snapshot[1]))
    emit({"event": "ready", "protocol": "verify COMMIT | push COMMIT | quit"})
    for line in sys.stdin:
        fields = line.split()
        if fields == ["quit"]:
            return 0
        try:
            if len(fields) != 2 or fields[0] not in ("verify", "push") or \
                    not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", fields[1]):
                raise ValueError("expected verify COMMIT, push COMMIT, or quit")
            if fields[0] == "verify":
                emit(session.verify(fields[1]))
            else:
                session.publish(fields[1])
                emit({"event": "dry-run" if os.environ.get("FFTA_PUSH_DRY") else "pushed",
                      "commit": fields[1]})
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            emit({"event": "refused", "error": str(error)})
    return 0
