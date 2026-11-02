#!/usr/bin/env python3
"""Archive only this project's compiled artifacts, recording verification status."""

from __future__ import annotations

from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess


ROOT = Path(__file__).resolve().parents[2]


def command(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verification-status", choices=("passed", "partial"), required=True)
    args = parser.parse_args()
    graph_path = ROOT / "build/dependency-graph.json"
    try:
        meta = json.loads(graph_path.read_text())["meta"]
    except (FileNotFoundError, json.JSONDecodeError, KeyError):
        if args.verification_status == "passed":
            raise
        meta = {}
    commit = command("git", "rev-parse", "HEAD")
    if args.verification_status == "passed" and (
        not meta.get("buildChecked") or not meta.get("sourceMatchesCommit")
        or meta.get("gitCommit") != commit
    ):
        raise RuntimeError("The graph must come from a full build of the current committed sources")
    if not (ROOT / ".lake/build").is_dir():
        raise RuntimeError("The local project build directory is missing")
    destination = ROOT / "build/ci/cache"
    destination.mkdir(parents=True, exist_ok=True)
    archive = destination / "project-build.tar.gz"
    # Passing only .lake/build excludes all dependency sources and caches in
    # .lake/packages. Tar also preserves executable modes and relative paths.
    subprocess.run(
        ["tar", "-I", "gzip -1", "-cf", str(archive), ".lake/build"],
        cwd=ROOT, check=True,
    )
    fingerprint = digest(archive)
    record = {
        "gitCommit": commit,
        "createdAtUtc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "system": platform.system(),
        "machine": platform.machine(),
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "leanVersion": command("lake", "env", "lean", "--version"),
        "registeredSourceSha256": meta.get("sourceSha256"),
        "registeredModuleCount": meta.get("registeredModuleCount"),
        "configurationSha256": {
            name: digest(ROOT / name)
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
        },
        "archive": archive.name,
        "archiveSha256": fingerprint,
        "archiveBytes": archive.stat().st_size,
        "archiveRoot": ".lake/build",
        "dependencyCachesIncluded": False,
        "verificationStatus": args.verification_status,
        "verification": (
            "The full registered-module build, make audit, and dependency-graph packaging succeeded."
            if args.verification_status == "passed" else
            "At least one verification step failed or was skipped. This is a partial build cache; "
            "it does not certify the source commit. Rebuild and rerun all checks after restoring."
        ),
    }
    (destination / "project-build.json").write_text(json.dumps(record, indent=2) + "\n")
    (destination / "SHA256SUMS").write_text(f"{fingerprint}  {archive.name}\n")
    print(f"Archived {archive.stat().st_size / 1048576:.1f} MiB from .lake/build only")
    print(f"Source commit: {commit}; SHA-256: {fingerprint}")


if __name__ == "__main__":
    main()
