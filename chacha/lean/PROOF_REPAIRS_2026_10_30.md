# Corrections made while formalizing the imported manuscript

**Scope note, 1 November 2026.** References below to a required bounded local
implementation describe the stronger imported paper model. The user has
since selected the abstract BST model charging search depth plus one plus
actual rotations, with free computation. A fixed noncomputable online
strategy is sufficient for this target. See the
[proof guide](../../docs/chacha-proof-guide/guide.pdf) for the current scope
and the separation between mathematical repairs and modeling changes.

The imported archive is preserved unchanged. These corrections concern
proof text, not the theorem statements.

## Absent guard in the strengthened split lemma

In the proof of the strengthened robust rectangle split bound, the
absent-guard branch sets `x_guard = p'.x - 1`. Then the supposedly empty
strip `(x_guard, p.x] × (p.time, infinity)` contains `p'` itself.
Use `x_guard = p'.x`, as in the finite-guard branch. The open horizontal
boundary excludes `p'`. `MixedGuard.lean` checks this corrected strip and
the subsequent rectangle construction.

## Order of the reversed mixed-turn triple

In the last bullet of the proof of Lemma `phi-2-bound`, the text asserts
that either `(p', p, q)` or `(q, h', h)` is a turn when the two internal
pairs have the same direction. The latter order is incorrect. For example,
keys `p'=1, p=2, q=10, h=3, h'=4` make both displayed triples monotone.
The intended second triple is `(q, h, h')` in forward time, equivalently
`(reverse h', reverse h, reverse q)` in reversed time. This has its middle
point at `h`, and produces the stated reversed mixed-turn charge at `h'`.
With repeated keys, the formal proof uses the last occurrence of `h`'s key
before `h'`, as required by the next-different definition in reversed time.

## First-visit secondary flips

The proof of Lemma `implementation-flips` says that a secondary bit flips
at most once on its first visit because it initially points UP. The
algorithm instead initializes genuine preferences rightward (DOWN).
The claimed first-visit bound is false with that initialization.

A concrete counterexample has four ordered leaves `0,1,2,3`, all primary
preferences initially rightward, and the first request equal to `0`.
The actual head-switch depths are `0,1`. The genuine secondary interval
`[0,2)`, split at depth `1`, receives UP followed by DOWN. Its initialized
DOWN bit therefore flips twice. Both the exit list and the two flips are
kernel-checked by `Secondary.first_visit_can_flip_twice` in
`OwnerFlipBound.lean`.

The replacement per-owner argument uses exact compression of monotone
write blocks. With arbitrary initialized preferences, it proves at most
twice the regular LCA alternations, twice the number of mixed blocks, and
an additive three per genuine memory bit (`Secondary.owner_flip_bound`).
`Secondary.actual_access_mixed_bound` bounds mixed secondary intervals
per request by the actual primary flips, and `Secondary.memoryCount_bound`
bounds their owner multiplicities. `Secondary.secondary_flip_bound` in
`SecondaryFlipBound.lean` now sums these ingredients for the concrete
persistent-memory implementation and proves the claimed constants.
`Dyadic.memoryLCA_eq_lcaBound` in `MemoryCountAssembly.lean` identifies its
tree-based count with the dyadic count in the rectangle theorem.

## Implementation variants and their correspondence to the paper

The three items above repair proof statements; the sharp lower-bound issue
recorded below is an additional statement-level correction. The following choices
instead change the implementation of a paper operation while retaining
its specified effect. They do not license replacing the final algorithm
by a conditional simulation theorem.

- **Order of secondary repairs.** The manuscript searches down a secondary
  reference and repairs its preferred paths on the return journey. The
  formal implementation repeatedly repairs the first wrong preferred
  edge from the root. `SecondaryHeads.lean` and
  `ObservedSecondaryAccess.lean` connect this order to the same interval
  update and exact preferred-edge flip count. This avoids a stack of
  pending departures. A bounded local controller still has to realize
  the proved traces; this change alone does not establish that controller.
- **Balanced auxiliary trees.** The paper uses red-black trees. The
  formalization uses the weight-balanced trees in `Std.DTreeMap`, whose
  balancing operations and invariants can be reused. The checked split,
  join, and access costs are logarithmic in the same component size.
  Their shapes and numerical constants differ. The input separator order,
  preferred-path partition, and original-key leaf word are unchanged.
- **Completion accounting.** `CompletedDepthAccounting.lean` retains the
  paper's extra completion root and actual final access. It proves that
  this access preserves every genuine memory bit and contributes at most
  a constant per request. The main count therefore continues to use the
  genuine secondary intervals from `MemoryCountAssembly.lean`.
- **Initialization trace.** `SourceInitialization.lean` proves a generic
  linear transformation between decorated full trees with equal leaf
  words, by rotation to a common right spine. This is useful for charging
  an initial layout but does not replace the appendix's requirement to
  compute the initial records locally. In particular, its target records
  are supplied to the trace theorem; local construction remains a
  separate obligation.

The imported manuscript remains unchanged. The final BST theorem must
still establish online local execution and use the shared BST optimum.

## Robust-family lower bound used in the competitive comparison

The paper's potential already uses the maximum size of a robust independent
rectangle family. `RobustCountingBound.lean` retains that smaller maximum
through the telescoping argument instead of enlarging it to the maximum
of all independent rectangles. It proves the stronger count
`abstractWork + 6 <= m + 13 * robustBound + 6n`.

`RobustBSTLowerBound.lean` proves `robustBound(X) <= 2 * pointerCost`
for every ordered BST execution, including repeated keys. Thus this route
suffices for the competitive comparison. It does not prove the paper's
separately cited lower bound for the larger ordinary independent-rectangle
maximum. That statement remains a distinct proof obligation.

The geometric argument follows the horizontal-witness method: each robust
family of one orientation receives distinct horizontally adjacent pairs in
an arborally satisfied superset. `RobustPrivateCut.lean` handles shared
endpoint columns explicitly. The BST-to-geometry argument maintains a max
heap of last-touch times, reusing the existing `PriorityHull` machinery;
`BSTHistory.lean` proves that each actual hull access preserves satisfaction.
The fictitious initial row is removed before counting, so the bound has no
additive initial-tree term. `SharedOPTBound.lean` then uses the existing
37-factor pointer realization of the common splay/Tango optimum, giving
`robustBound(X) <= 74 * OPT(X)`.

## Sharp ordinary-rectangle inequality with repeated keys

`RepeatedKeyRectangleExample.lean` checks the requests `5, 0, 10, 5` at
times `0, 1, 2, 3`. The five pairs of times
`(0,1), (0,2), (1,2), (1,3), (2,3)` define input-free, pairwise independent
rectangles under the manuscript's open-corner definition. A BST rooted at
5 with children 0 and 10 serves this word with pointer costs `1,2,2,1`,
for a total of six. Consequently the displayed inequality
`OPT >= rectangleBound/2 + m` fails in the shared ordinary pointer model:
its right-hand side is at least `5/2 + 4 = 6.5`.

The issue is the repeated column at key 5. It allows non-defining rectangle
corners to meet on a vertical boundary without violating the open-corner
independence condition. The example does not contradict an asymptotic
ordinary-rectangle lower bound. It does rule out using the displayed sharp
inequality unchanged in the formal comparison. The robust-family route
above is proved directly for repeated keys and avoids this problem. No
imported manuscript file has been altered.
