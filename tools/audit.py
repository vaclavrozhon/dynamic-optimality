#!/usr/bin/env python3
"""Build and audit every tracked Lean module registered in the root Lake file.

The generated old-style Lean driver retains private declarations and selects
audit targets by originating module, rather than by declaration namespace.
Heavy commands are sequential. Callers may hold the repository's external
build lock; this runner intentionally does not acquire that lock again.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from dependency_graph.export import ROOT, import_frontier, inventory


WORK = ROOT / "build" / "audit"


def run_command(args: list[str], log: Path, *, stream: bool = False) -> None:
    print(f"Running {' '.join(args[:3])}; log: {log.relative_to(ROOT)}", flush=True)
    with log.open("w") as output:
        if stream:
            process = subprocess.Popen(
                args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            assert process.stdout is not None
            for line in process.stdout:
                output.write(line)
                output.flush()
                print(line, end="", flush=True)
            status = process.wait()
        else:
            status = subprocess.run(
                args, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
            ).returncode
    if status:
        if not stream:
            print("\n".join(log.read_text(errors="replace").splitlines()[-60:]), file=sys.stderr)
        raise RuntimeError(f"Lean command failed ({status}); see {log}")


def endpoint_commands() -> list[str]:
    """Keep the existing endpoint lists authoritative, preserving their order."""
    commands = []
    seen = set()
    for filename in ("AuditAll.lean", "AuditDynamicOptimality.lean"):
        for line in (ROOT / filename).read_text().splitlines():
            match = re.fullmatch(r"\s*#print\s+axioms\s+([\w.']+)\s*", line)
            if match and match[1] not in seen:
                commands.append(f"#print axioms {match[1]}")
                seen.add(match[1])
            elif re.match(r"\s*#print\s+axioms\b", line):
                raise RuntimeError(f"Unsupported endpoint command in {filename}: {line}")
    if not commands:
        raise RuntimeError("The public endpoint audit lists are empty")
    return commands


def prepare_driver(modules: list[dict], *, use_frontier: bool = True) -> Path:
    manifest = WORK / "manifest.json"
    manifest.write_text(json.dumps({"modules": modules}, indent=2) + "\n")
    # A preparation-only run must also work before new modules have compiler
    # metadata. The real audit computes the compact frontier after building.
    frontier = import_frontier(modules) if use_frontier else [entry["module"] for entry in modules]
    helper = (ROOT / "tools/lean_audit/Audit.lean").read_text()
    if not helper.startswith("import Lean\n"):
        raise RuntimeError("The audit helper must begin with import Lean")
    helper = helper.removeprefix("import Lean\n")
    endpoints = endpoint_commands()
    driver = WORK / "Driver.lean"
    driver.write_text(
        "import Lean\n" + "".join(f"import {name}\n" for name in frontier)
        + "\nset_option stderrAsMessages false\nset_option maxHeartbeats 0\n"
        + helper + "\n" + "\n".join(endpoints)
        + "\n\nrun_cmd do\n  Lean.Elab.Command.liftCoreM <| LeanAudit.auditRegistered "
        + json.dumps(str(manifest)) + "\n"
    )
    print(
        f"Prepared {len(frontier)} imports covering {len(modules)} registered modules, "
        f"with {len(endpoints)} distinct endpoint diagnostics.", flush=True,
    )
    return driver


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--prepare-only", action="store_true",
        help="Write a driver importing the full source inventory; do not build or audit",
    )
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    modules, tracked, excluded = inventory()
    if not modules:
        raise RuntimeError("No registered tracked modules were found")
    print(
        f"Audit inventory: {len(modules)} registered modules in {len(tracked)} tracked Lean files; "
        f"{len(excluded)} tooling/audit files outside the libraries.", flush=True,
    )
    if not args.prepare_only:
        run_command(["lake", "build", *(entry["module"] for entry in modules)], WORK / "build.log")
    driver = prepare_driver(modules, use_frontier=not args.prepare_only)
    if args.prepare_only:
        print(f"Driver prepared at {driver.relative_to(ROOT)}. No build or audit was performed.")
        return
    run_command(["lake", "env", "lean", str(driver)], WORK / "audit.log", stream=True)
    print("Full registered-module build and axiom audit passed.", flush=True)


if __name__ == "__main__":
    main()
