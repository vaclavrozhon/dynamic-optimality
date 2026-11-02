#!/usr/bin/env python3
"""Export direct Lean declaration dependencies from all registered local modules.

Uses only the Python standard library and the repository's pinned Lean/Lake.
Run from any directory; output paths are relative to the repository root.
The normal command builds every registered tracked Lean module first, including
modules not reachable from the public result imports. No source-text dependency
approximation or external Mathlib/Lean nodes are used.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import fcntl
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / "build" / "dependency-graph"
LOCK = "/tmp/dynamic-optimality-lean-build.lock"


def command(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def group_for(path: str) -> str:
    if path.startswith(("splay/", "interface/")):
        return "Splay"
    if path.startswith("chacha/") or path.startswith("ChaCha"):
        return "Cha-Cha"
    if path.startswith("greedy/"):
        return "Greedy"
    if path.startswith("multisplay/"):
        return "MultiSplay"
    if path.startswith("DynamicOptimality"):
        return "Shared"
    return "Other"


def inventory() -> tuple[list[dict], list[str], list[str]]:
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    tracked = sorted(filter(None, command("git", "ls-files", "-z", "--", "*.lean").split("\0")))
    modules: dict[str, dict] = {}
    registered_files = set()
    for library in config["lean_lib"]:
        source = PurePosixPath(library.get("srcDir", "."))
        roots = library.get("roots", [library["name"]])
        if library.get("globs"):
            raise RuntimeError("Explicit Lake globs need inventory support before exporting this project")
        for file in tracked:
            try:
                relative = PurePosixPath(file).relative_to(source)
            except ValueError:
                continue
            module = ".".join(relative.with_suffix("").parts)
            if not any(module == root or module.startswith(root + ".") for root in roots):
                continue
            if module in modules and modules[module]["file"] != file:
                raise RuntimeError(f"Ambiguous registered module {module}: {file}")
            modules[module] = {
                "module": module, "file": file, "group": group_for(file),
                "library": library["name"],
            }
            registered_files.add(file)
    return ([modules[name] for name in sorted(modules)], tracked,
            sorted(set(tracked) - registered_files))


def run_lean(args: list[str], log: Path) -> None:
    print(f"Running {' '.join(args[:3])}; log: {log.relative_to(ROOT)}", flush=True)
    with open(LOCK, "a") as lock, log.open("w") as stream:
        fcntl.flock(lock, fcntl.LOCK_EX)
        result = subprocess.run(args, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print("\n".join(log.read_text(errors="replace").splitlines()[-60:]), file=sys.stderr)
        raise RuntimeError(f"Lean command failed ({result.returncode}); see {log}")


def import_frontier(modules: list[dict]) -> list[str]:
    """Read compiler-produced module imports, then remove redundant direct imports.

    Keep the generated import driver compact. Every local module must still be
    reachable from the retained imports, and the
    Lean exporter independently verifies the actual loaded-module set afterward.
    This optimization changes no declaration or dependency coverage.
    """
    names = {module["module"] for module in modules}
    dependencies = {}
    imported = set()
    for name in sorted(names):
        artifact = ROOT / ".lake/build/lib/lean" / Path(*name.split("."))
        metadata = json.loads(artifact.with_suffix(".ilean").read_text())
        if metadata["module"] != name:
            raise RuntimeError(f"Wrong module metadata in {artifact}")
        dependencies[name] = {entry[0] for entry in metadata["directImports"] if entry[0] in names}
        imported.update(dependencies[name])
    frontier = sorted(names - imported)
    reachable, pending = set(), list(frontier)
    while pending:
        name = pending.pop()
        if name not in reachable:
            reachable.add(name)
            pending.extend(dependencies[name])
    if reachable != names:
        raise RuntimeError("Compiler import metadata does not cover every registered module")
    return frontier


def sources_match_commit(modules: list[dict]) -> bool:
    result = subprocess.run(
        ["git", "diff", "--quiet", "HEAD", "--", *(module["file"] for module in modules)], cwd=ROOT
    )
    if result.returncode not in (0, 1):
        raise RuntimeError("Unable to compare registered Lean sources with the recorded commit")
    return result.returncode == 0


def validate(graph: dict, modules: list[dict]) -> None:
    nodes, edges, meta = graph["nodes"], graph["edges"], graph["meta"]
    assert [node["id"] for node in nodes] == list(range(len(nodes))), "Nonconsecutive node ids"
    assert len({node["name"] for node in nodes}) == len(nodes), "Duplicate Lean declaration names"
    by_module = {module["module"]: module for module in modules}
    for node in nodes:
        assert node["file"] == by_module[node["module"]]["file"], "Wrong source provenance"
        assert node["line"] is None or node["line"] >= 1, "Source lines must be one-based"
    pairs = set()
    for source, target, mask in edges:
        assert 0 <= source < len(nodes) and 0 <= target < len(nodes), "Dangling graph edge"
        assert mask in (1, 2, 3), "Invalid edge kind"
        assert (source, target) not in pairs, "Duplicate dependency pair"
        pairs.add((source, target))
    assert len(nodes) == meta["nodeCount"] and len(edges) == meta["edgeCount"]
    assert not meta["unresolvedConstants"], "Elaborated expression references an unavailable constant"
    assert set(meta["loadedModules"]) == set(by_module), "Some registered modules were not imported"
    assert sum(node["externalReferences"] for node in nodes) == meta["externalReferenceCount"]
    # Cross-check real public theorem references, rather than just JSON shape.
    names = {node["name"]: node["id"] for node in nodes}
    public = "DynamicOptimality.Results.splay"
    if public in names:
        assert any(source == names[public] and mask & 2 for source, _, mask in edges), (
            "The public Splay theorem has no local proof dependency: theorem bodies may be missing"
        )
    assert any(node["private"] for node in nodes), "Private declarations were not loaded"
    assert any(node["kind"] == "recursor" for node in nodes), "Generated recursors were not loaded"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="build/dependency-graph.json", help="Graph JSON destination")
    parser.add_argument("--skip-build", action="store_true", help="Reuse existing .olean files (development only)")
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    modules, tracked, excluded = inventory()
    manifest_path = WORK / "manifest.json"
    manifest_path.write_text(json.dumps({"modules": modules}, indent=2) + "\n")
    print(f"Found {len(modules)} registered modules in {len(tracked)} tracked Lean sources; "
          f"{len(excluded)} sources are outside the configured libraries.", flush=True)
    if not args.skip_build:
        run_lean(["lake", "build", *(module["module"] for module in modules)], WORK / "build.log")
    frontier = import_frontier(modules)
    print(f"Using {len(frontier)} compiler-derived direct imports, covering all {len(modules)} modules.", flush=True)
    body = (ROOT / "tools/dependency_graph/Export.lean").read_text()
    assert body.startswith("import Lean\n")
    body = body.removeprefix("import Lean\n")
    raw_path = WORK / "declarations.jsonl"
    driver = WORK / "Driver.lean"
    driver.write_text(
        "import Lean\n" + "".join(f"import {module}\n" for module in frontier)
        + "\nset_option stderrAsMessages false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
        + body
        + "\nrun_cmd do\n  let env ← getEnv\n  Lean.Elab.Command.liftIO <| "
        + f"DependencyGraph.exportGraph env {json.dumps(str(manifest_path))} {json.dumps(str(raw_path))}\n"
    )
    run_lean(["lake", "env", "lean", str(driver.relative_to(ROOT))], WORK / "export.log")
    nodes, edges, statistics = [], [], None
    with raw_path.open() as stream:
        for line in stream:
            record = json.loads(line)
            if "node" in record:
                nodes.append(record["node"])
            elif "edge" in record:
                edges.append(record["edge"])
            elif "statistics" in record:
                statistics = record["statistics"]
            else:
                raise RuntimeError("Unknown export record")
    if statistics is None:
        raise RuntimeError("Export was incomplete: no final statistics record")
    nodes.sort(key=lambda node: node["id"])
    edges.sort()
    source_hash = hashlib.sha256()
    for module in modules:
        source_hash.update(module["file"].encode() + b"\0")
        source_hash.update((ROOT / module["file"]).read_bytes() + b"\0")
    meta = {
        "schemaVersion": 1,
        "gitCommit": command("git", "rev-parse", "HEAD"),
        "exportedAtUtc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "leanVersion": command("lake", "env", "lean", "--version"),
        "sourceSha256": source_hash.hexdigest(),
        "sourceMatchesCommit": sources_match_commit(modules),
        "trackedLeanSourceCount": len(tracked),
        "registeredModuleCount": len(modules),
        "directImportCount": len(frontier),
        "importFrontier": frontier,
        "excludedModules": [],
        "unregisteredSources": [
            {"file": file, "reason": "Not a module in any configured local Lean library"}
            for file in excluded
        ],
        "scope": "All declarations of every tracked Lean module registered in lakefile.toml, "
                 "including private and generated declarations, whether or not reachable from public results.",
        "edgeDirection": "declaration -> referenced declaration",
        "edgeMasks": {"1": "type", "2": "proof or value", "3": "both"},
        "referenceSemantics": "Direct elaborated expression references, including structure names in "
                              "projection expressions and recursor rule bodies; no transitive closure. "
                              "External dependencies are counted per source/target pair but excluded as nodes.",
        "generatedFlag": "Display heuristic: Lean internal-detail name after private-name demangling, "
                         "missing direct declaration source range, or kernel recursor.",
        "buildChecked": not args.skip_build,
        **statistics,
    }
    meta["moduleCount"] = len(meta["loadedModules"])
    meta["modulesWithoutDeclarations"] = sorted(set(meta["loadedModules"]) - set(meta["modulesWithDeclarations"]))
    meta["kindCounts"] = dict(sorted(Counter(node["kind"] for node in nodes).items()))
    meta["groupCounts"] = dict(sorted(Counter(node["group"] for node in nodes).items()))
    meta["selfReferenceCount"] = sum(source == target for source, target, _ in edges)
    meta["edgeMaskCounts"] = dict(sorted(Counter(str(mask) for _, _, mask in edges).items()))
    graph = {"meta": meta, "nodes": nodes, "edges": edges}
    validate(graph, modules)
    output = ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(json.dumps(graph, ensure_ascii=False, separators=(",", ":")) + "\n")
    temporary.replace(output)
    print(f"Wrote {output}: {len(nodes):,} declarations, {len(edges):,} local direct dependencies; "
          f"{meta['externalReferenceCount']:,} external references.", flush=True)


if __name__ == "__main__":
    main()
