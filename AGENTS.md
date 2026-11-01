# Working on the formalization

Prefer Czech in conversation with the user. Write documentation and Lean comments in English unless preserving an existing document's language. Be candid about proved results, hypotheses, counterexamples, and unfinished bridges. Prioritize mathematical understanding and proofs; use experiments only to answer a concrete stated question.

## Preserve the mathematical scope

- Read [README.md](README.md) and [FORMALIZATION.md](FORMALIZATION.md) before changing a public endpoint.
- Reuse the existing `DynamicOptimality.BST`, `RawTree`, `OPT`, `Competitive`, `SearchRotation`, and `OnlineBST` interfaces. Do not introduce a replacement optimum or silently change an algorithm's cost model.
- The completed Tango² target permits free computation and mathematical bookkeeping, with fixed noncomputable choices per current state and request. It charges the initial search depth plus one and actual ordinary rotations. A bounded local controller is a separate task.
- Classical MultiSplay's composed bound is exported by `MultiSplay.Online.competitive`. It constructs its actual comparator. Any further theorem assuming a cheap comparator, representation invariant, or simulator remains an intermediate result until that assumption is proved for the actual algorithm.
- Check quantifier order and uniformity of constants, exact tree endpoints and key sets, initialization costs, repeated requests, and empty cases. Finite examples supplement general proofs.

## Proof integrity

- Do not use `sorry`, `admit`, new axioms, opaque unproved assumptions, `unsafe` proof shortcuts, or `native_decide`. Kernel-checked `decide` is permitted for genuinely finite statements.
- The accepted logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Classical choice does not excuse an unproved existence statement or dependence on future requests.
- Preserve checked modules and their proofs. Keep speculative developments separate from completed public claims and explain material changes to the theorem's scope.
- Do not modify dependency sources or commit dependency and build caches. Use the pinned root Lean/Mathlib project and retain source paths declared in `lakefile.toml`.

## Verification and collaboration

- Run commands from the repository root. Use targeted `lake build` checks during development, then `make audit` before claiming a completed verified change. Report exactly which checks passed; do not treat a build, source hash, or pending process as a completed axiom audit.
- Serialize heavy Lean work: one build, cache operation, or audit at a time across all agents and terminals. The Makefile does not provide an internal lock; coordinate before starting a process. Memory pressure can make concurrent runs expensive.
- When delegation is authorized, assign separate file ownership and agree on interfaces before editing shared modules. Do not overwrite another contributor's work.
- Use `rg` for source searches. Keep changes focused and avoid introducing tests that merely repeat a definition. Verify mathematical properties and relevant boundary cases instead.
- Keep this source snapshot independent of the original workspace. Do not initialize or modify its old Git repositories, publish, push, or select a license without authorization for that action.

The root audits intentionally remain outside Lean's `module` system so their namespace scan can include private declarations. Preserve that coverage when changing audit code. Follow [docs/PROVENANCE.txt](docs/PROVENANCE.txt) for source history and licensing status.
