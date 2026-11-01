Greedy in the shared Lean project
================================

Run from the repository root:

    lake build Greedy
    lake env lean AuditGreedy.lean

For the complete shared project, run `lake build`.

The root Lake project uses the same Lean and Mathlib 4.32.1 environment
as Splay and Tango squared. The 168 older Greedy modules retain their
source locations and import names. Six libraries register those sources:
GreedyGeometry, GreedyFringe, GreedyAccess, GreedyHistory, GreedyAccounting,
and GreedyPorts. The public Greedy entry point imports them and the new
modules here. Historical adjacent .olean files are not build inputs.

Completed theorem (31 October 2026)
-----------------------------------

Greedy.competitive : Greedy.Target

The theorem in Greedy/Competitive.lean is unconditional. It proves
DynamicOptimality.Competitive Greedy.cost Greedy.loglogFactor, using the
same attained offline optimum as the Splay and Tango developments.
There is one positive universal constant C such that, for every positive
universe size n, every initial BST, and every request sequence,

    Greedy.cost initial requests
      <= C * (DynamicOptimality.OPT requests + n) * Greedy.loglogFactor n.

Greedy.cost counts actual geometric touches, including the requested key,
starting from the negative depths of the prescribed initial BST.
Greedy.loglogFactor is the base-two upper logarithm applied twice, with
each input stabilized at two; it has order 1 + log log n.
The constants are deliberately unoptimized.

The public intermediate theorem Greedy.cost_le_bounded_trace proves

    Greedy.cost initial requests
      <= 32000 * (n + trace.cost) * contractedGap H,

where trace is an actual shared ComparisonTrace, H bounds all comparator
heights, each comparator rotation has depth at most one, and
contractedGap H = 1 + ceil(log_2(H+1)). Trace cost is its request count
plus its rotation count. Greedy.bounded_comparison discharges the premise
of ComparisonReduction.target_of_bounded_comparison. That reduction uses
the proved Splay polylogarithmic-height normal form to obtain the final
log-log factor and the common OPT; no normal-form axiom is introduced.

Proof organization
------------------

Write m for the request count, r for the comparator rotation count,
N = 2*n+1 for the external-record count, and K = contractedGap H for the
label range. A membership consists of an actual record in a growing or
frozen block. Its ticket is the pair (family, immutable join time).
A created block instance retains its own immutable instance identifier.

Execution.exists_shared_run constructs the literal Greedy run from the
common comparison trace. Every state satisfies the geometric and naming
invariants. The exact identity is 2*cost = 2*m + links, and the number of
created instances is at most 2*m + 99*r. Comparator changes retain their
actual refinement rotations and fresh administrative allocators.

InitializedJoint.exists_journal_history constructs one chronological
entry/label journal together with a sparse label history. All numerical
rows concern these same witnesses, including ordinary entries (at most
N+11*r), positive and negative label variation, boundary links, equal-label
internal links, entry deficits, and the two signed memory shifts.

ClosedInstances, RunBirthJournal, and InstanceCharge derive the lifetime
charges from actual creations, splits, transfers, and deletions.
IncomingExcess and OutgoingExcess bound the two boundary excesses;
DepartureAmounts supplies positive variation and boundary nondrop charges.
FamilyOrder and ClosedFamilies ensure that processed fragments cannot
recover a removed historical crossing. RunShiftTelescope then bounds the
actual creator shift by six times total label variation.

WinnerTickets.initialized_total_le_four proves that a literal membership
wins internally at most four times in the whole execution. TicketJournal
tracks the current membership pointer through initialization, every
administrative operation, and every physical link. Its paired win/entry
observations erase to the same plain journal, and access_remaining
identifies their counts with the geometric family win counts.

WinnerCredit and CreditCensus use a current-deficit potential: each
record's deficit is weighted by the number of its ticket's remaining
internal wins. Entries inject at most four entry deficits; label changes
inject at most four times downward variation; a win releases its current
deficit. This proves the internal-link inequality with an additional
initial reserve of at most 4*N. It replaces separate historical winner
windows in this part of the manuscript's accounting argument.

LinearLedger.with_initial_credit absorbs that reserve without increasing
the coefficient 239. ActualLedger.execution_link_bound assembles all
proved rows and obtains

    links <= 239*K * (3*N + births + 33*r).

The birth budget and exact touch/link identity give the bounded comparator
theorem above. Competitive.lean completes the common-OPT comparison.

Validation and sources
----------------------

AuditGreedy.lean prints the axioms of the final and intermediate theorems
and audits every imported Greedy, GreedyForest, and GreedyMerge declaration,
including private declarations. It rejects sorryAx and every axiom other
than Lean's standard propext, Classical.choice, and Quot.sound.

Validation on 31 October 2026: the complete shared `lake build` succeeded
(9921 jobs). AuditGreedy checked 8839 declarations, including private ones,
and found no nonstandard axioms. AuditDynamicOptimality independently
checked 28845 shared, Splay, and Tango declarations with the same result.
The final Greedy.competitive theorem uses only propext, Classical.choice,
and Quot.sound.

The older conditional quadratic finite-accounting theorem remains available
as a historical result. It is not the endpoint used to claim the new bound.

The original working manuscript was ../sosa-paper/main.pdf, with arguments
in accounting.tex, administration.tex, and assembly.tex. That historical
manuscript is not included in this proof-source snapshot.
