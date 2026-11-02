# Explore the Lean dependency graph

Open the [interactive graph](https://vaclavrozhon.github.io/dynamic-optimality/proof-atlas.html) on the [project website](https://vaclavrozhon.github.io/dynamic-optimality/). You can also download [dependency-graph.html](https://github.com/vaclavrozhon/dynamic-optimality/raw/refs/heads/main/docs/dependency-graph.html) and open the saved file in a current browser. It is one self-contained HTML file: the graph data, drawing code, and spring simulation are included. It works offline and needs no server or account.

The current snapshot contains **63,301 declarations**, including **39,429 theorems**, and **541,073 direct dependency edges** across all **2,225 registered modules**. Ten modules contain no declarations; the module overview therefore has 2,215 nodes. See the [verification record](verification-review-2026-11-02.txt).

The graph contains the declarations from every tracked Lean module registered in this repository's `lakefile.toml`, including private declarations and generated helpers. It covers modules outside the import closure of the main public results as well. Lean, Mathlib, and other external-library declarations are omitted; references to them are counted in the metadata. Root audit scripts and the exporter itself are tooling outside the mathematical libraries.

## What an edge means

A directed edge `A → B` means that declaration `A` directly references declaration `B` in its elaborated type, proof, or definition. The edge filter distinguishes **type** references from **proof/value** references. A pair with both kinds has one edge carrying both labels.

Dependencies come from Lean's compiled expressions, not searches through source text. Primitive structure projections also contribute a reference to their structure type; recursor reduction-rule bodies are included. A recursor is the elimination or recursion principle Lean generates for an inductive type. Constructor lists and other declaration metadata do not create additional type/value edges. Transitive dependencies are not added as direct edges. Self references are retained, so the graph need not be acyclic.

The default module overview groups declarations by their source module. An edge between two modules represents one or more actual declaration references crossing that boundary. Use the prominent **Modules** and **Declarations** buttons to change the level of detail. **Neighborhood** shows the chosen declaration and nearby dependencies. Selecting a declaration and switching to modules highlights its containing module; switching back retains the declaration selection. Colors identify Splay, Greedy, Cha-Cha, MultiSplay, and shared infrastructure; they describe source ownership, not a theorem's logical strength.

The **Start with a result** strip opens the main algorithm bounds, including Cha-Cha with Splay auxiliaries, and the funnel, colored-walk, rectangle-separation, and entropy results. Stars mark those statements, their canonical proof endpoints, and their containing modules. Supporting model equivalence, online geometric simulation, NCA closure, normal form, and the MultiSplay obstruction have diamond markers. These are curated navigation markers; they do not change the exported dependencies or certify a theorem independently of Lean. Result shortcuts clear conflicting filters so the selected statement is visible.

Search for a full declaration name, such as:

```text
DynamicOptimality.Results.splay
DynamicOptimality.Results.splay_refined
DynamicOptimality.Results.greedy
DynamicOptimality.Results.chacha
DynamicOptimality.Results.chacha_splay
DynamicOptimality.Results.multisplay
DynamicOptimality.Results.funnel_shuffle
DynamicOptimality.Results.colored_shuffle
DynamicOptimality.Results.geometric_online
DynamicOptimality.Results.bst_models_equivalent
```

The Cha-Cha endpoint is `DynamicOptimality.Results.chacha`. A selected node shows its dependencies, declarations using it, and a link to the source at the recorded Git commit. The graph layout is a visual aid: springs pull related nodes together, while repulsion separates them. Distances, positions, and apparent clusters are not additional mathematical claims.

Choose **Declarations** to see the whole graph, or filter **Declaration kind → Theorems**. Zoom with **− / +** or the scroll wheel; **Fit** frames the current graph. Pan by dragging the background, and move a node by dragging it. Canvas labels are shortened; hovering or selecting reveals the full name. **PNG** saves the current view. Large views initially draw a counted sample of edges while the simulation still uses every edge; **Draw every visible edge** disables that drawing sample. Node and dependency counts are never reduced silently.

Hovering over or selecting a node highlights **all incident edges in the current filtered view**, including edges omitted from the background drawing sample. Outgoing arrows show declarations it uses; incoming arrows show declarations that use it. The status bar reports the hovered node's incident-edge count. Moving away removes the hover highlighting while retaining the selected node's highlighting.

Private declarations keep their exact Lean names as identifiers; their displayed names omit Lean's private-name prefix. The generated-helper flag is a display heuristic based on internal names, missing direct source ranges, and recursor kind. All declarations remain included by default; filtering generated helpers changes only the view.

## Rebuild the snapshot

From the repository root on a Unix-like system, with the pinned Lean toolchain and Python 3.11 or later:

```sh
make graph
```

This builds every registered, tracked local module, reads its elaborated declarations, validates the graph, and writes the standalone HTML. Heavy Lean commands use `/tmp/dynamic-optimality-lean-build.lock`; use the same lock for other concurrent builds or audits.

The generated Lean driver imports a minimal set of entry modules derived from the compiler's direct-import metadata. The exporter checks that their import closure covers every registered local module and verifies the complete module set again after loading the Lean environment. This reduces redundant direct imports without dropping declarations.

The steps can also be run separately:

```sh
python3 tools/dependency_graph/export.py
python3 tools/dependency_graph/build.py
```

The exporter writes `build/dependency-graph.json`; temporary drivers and logs go into `build/dependency-graph/`. Those intermediates are ignored by Git. The viewer template is [viewer.html](../tools/dependency_graph/viewer.html), the Lean extractor is [Export.lean](../tools/dependency_graph/Export.lean), and the packager is [build.py](../tools/dependency_graph/build.py). No JavaScript packages or network resources are needed by the viewer.

The compressed HTML uses the browser's `DecompressionStream` API. For a browser without it, rebuild with `python3 tools/dependency_graph/build.py --plain` to embed uncompressed JSON instead. The larger file contains the same graph.

[dependency-graph-summary.json](dependency-graph-summary.json) records the declaration and edge counts, module coverage, source commit, source fingerprint, graph fingerprint, and external-reference counts. If registered Lean sources have uncommitted changes, the viewer reports that source links lead to the last committed version. The graph is a snapshot: rerun `make graph` after changing the Lean sources. Extraction and visualization supplement the repository's theorem statements and axiom audits; they are not a separate proof of correctness.
