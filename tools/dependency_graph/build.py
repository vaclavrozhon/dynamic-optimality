#!/usr/bin/env python3
"""Package the exported Lean graph as one offline, interactive HTML file."""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import base64
import hashlib
import json
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parents[2]
MARKER = "<!-- GRAPH_DATA -->"


def validate(graph: dict) -> None:
    """Reject lost endpoints or ambiguous edges before publishing a snapshot."""
    if not isinstance(graph.get("meta"), dict):
        raise ValueError("Graph metadata is missing")
    nodes, edges = graph["nodes"], graph["edges"]
    names = set()
    for expected, node in enumerate(nodes):
        if type(node["id"]) is not int or node["id"] != expected:
            raise ValueError("Node IDs must be consecutive integers in array order")
        if node["name"] in names:
            raise ValueError(f"Duplicate declaration name: {node['name']}")
        names.add(node["name"])
        for field in ("name", "label", "kind", "module", "file", "group"):
            if not isinstance(node.get(field), str):
                raise ValueError(f"Node {expected} lacks string field {field}")
        source = PurePosixPath(node["file"])
        if source.is_absolute() or ".." in source.parts:
            raise ValueError(f"Source path must be repository-relative: {source}")
    pairs = set()
    for edge in edges:
        if len(edge) != 3 or any(type(value) is not int for value in edge):
            raise ValueError(f"Invalid edge: {edge}")
        source, target, mask = edge
        if not (0 <= source < len(nodes) and 0 <= target < len(nodes)):
            raise ValueError(f"Edge endpoint outside graph: {edge}")
        if mask not in (1, 2, 3):
            raise ValueError(f"Invalid dependency-kind mask: {edge}")
        pair = (source, target)
        if pair in pairs:
            raise ValueError(f"Duplicate directed edge: {edge}")
        pairs.add(pair)


def loader(payload: bytes, plain: bool) -> str:
    if plain:
        # A declaration name must never be able to close the script element.
        escaped = payload.decode("utf-8").replace("<", "\\u003c")
        return (
            '<script id="graph-data" type="application/json">'
            + escaped
            + "</script>\n<script>window.LEAN_GRAPH_READY = Promise.resolve("
            + 'JSON.parse(document.getElementById("graph-data").textContent));</script>'
        )
    encoded = base64.b64encode(gzip.compress(payload, compresslevel=9, mtime=0)).decode("ascii")
    return (
        '<script id="graph-payload" type="application/octet-stream">'
        + encoded
        + "</script>\n"
        + """<script>
window.LEAN_GRAPH_READY = (async () => {
  if (typeof DecompressionStream === "undefined") {
    throw new Error("This browser cannot decompress the graph. Use a current browser, " +
      "or rebuild the HTML with tools/dependency_graph/build.py --plain.");
  }
  const encoded = document.getElementById("graph-payload");
  const binary = atob(encoded.textContent.trim());
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
  encoded.remove();
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
  return await new Response(stream).json();
})();
</script>"""
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=ROOT / "build/dependency-graph.json")
    parser.add_argument("--template", type=Path, default=ROOT / "tools/dependency_graph/viewer.html")
    parser.add_argument("--output", type=Path, default=ROOT / "docs/dependency-graph.html")
    parser.add_argument("--summary", type=Path, default=ROOT / "docs/dependency-graph-summary.json")
    parser.add_argument("--plain", action="store_true", help="Embed plain JSON instead of compressed data")
    args = parser.parse_args()
    graph = json.loads(args.data.read_text())
    validate(graph)
    payload = json.dumps(graph, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    template = args.template.read_text()
    if template.count(MARKER) != 1:
        raise ValueError(f"Viewer must contain exactly one {MARKER} marker")
    html = template.replace(MARKER, loader(payload, args.plain))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(html)
    summary = {
        "meta": graph["meta"],
        "nodes": len(graph["nodes"]),
        "edges": len(graph["edges"]),
        "modules": len({node["module"] for node in graph["nodes"]}),
        "kinds": dict(sorted(Counter(node["kind"] for node in graph["nodes"]).items())),
        "groups": dict(sorted(Counter(node["group"] for node in graph["nodes"]).items())),
        "generated": sum(bool(node.get("generated")) for node in graph["nodes"]),
        "typeEdges": sum(bool(edge[2] & 1) for edge in graph["edges"]),
        "valueEdges": sum(bool(edge[2] & 2) for edge in graph["edges"]),
        "selfEdges": sum(edge[0] == edge[1] for edge in graph["edges"]),
        "jsonSha256": hashlib.sha256(payload).hexdigest(),
        "jsonBytes": len(payload),
        "htmlBytes": args.output.stat().st_size,
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n")
    print(f"Wrote {args.output}: {summary['nodes']:,} declarations, "
          f"{summary['edges']:,} directed edges, {summary['htmlBytes'] / 1048576:.1f} MiB")
    print(f"Graph SHA-256: {summary['jsonSha256']}")


if __name__ == "__main__":
    main()
