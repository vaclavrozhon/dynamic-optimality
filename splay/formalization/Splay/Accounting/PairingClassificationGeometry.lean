import Splay.Accounting.PairingSlotOccurrence
import Splay.Accounting.BoundaryPairingMove

namespace Splay.Accounting

open Splay.Tree.BST

namespace PassPairingClassification

variable
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}

/--
The transcript slot of every internal pass charge is one of the two actual
pairing occurrences contributed by a concrete zig-zig.
-/
theorem internalCharge_slot_mem_pairings
    (classification :
      PassPairingClassification transcript params
        initial final operations)
    (charge : PairingSlot × Interface.ActivitySlot operations)
    (member : charge ∈ classification.internalCharges) :
    charge.1 ∈ firstPairings kinds ++ secondPairings kinds := by
  have classifiedMember :
      charge.1 ∈
    classification.importantSlots ++
          classification.unimportantSlots ++
            classification.internalCharges.map Prod.fst := by
    simp only [List.mem_append, List.mem_map]
    exact Or.inr ⟨charge, member, rfl⟩
  exact classification.slots_partition.mem_iff.mp classifiedMember

/--
Every internal charge has the exact chronological splay geometry selected by
its slot: request number and key, request pre/post trees, local step number,
double-rotation pre/post trees, contextual depth, `DoubleRotationAt`, true
zig-zig orientation, and phase.
-/
theorem internalCharge_geometry
    (classification :
      PassPairingClassification transcript params
        initial final operations)
    (charge : PairingSlot × Interface.ActivitySlot operations)
    (member : charge ∈ classification.internalCharges) :
    Nonempty (PairingSlotOccurrence transcript charge.1) :=
  exists_pairingSlotOccurrence transcript charge.1
    (classification.internalCharge_slot_mem_pairings charge member)

end PassPairingClassification

namespace BoundaryPassPairingClassification

variable
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}

/-- An important boundary move's slot belongs to the concrete transcript. -/
theorem importantMove_slot_mem_pairings
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    move.slot ∈ firstPairings kinds ++ secondPairings kinds := by
  have mappedMember :
      move.slot ∈
        classification.importantMoves.map BoundaryPairingMove.slot :=
    List.mem_map.mpr ⟨move, member, rfl⟩
  have importantMember :
      move.slot ∈
        classification.passClassification.importantSlots := by
    rw [← classification.importantSlots_eq]
    exact mappedMember
  have classifiedMember :
      move.slot ∈
        classification.passClassification.importantSlots ++
          classification.passClassification.unimportantSlots ++
            classification.passClassification.internalCharges.map
              Prod.fst := by
    exact
      List.mem_append_left _
        (List.mem_append_left _ importantMember)
  exact
    classification.passClassification.slots_partition.mem_iff.mp
      classifiedMember

/--
An important delete/insert move carries the exact splay zig-zig geometry of
the slot to which that move is assigned.
-/
theorem importantMove_geometry
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    Nonempty (PairingSlotOccurrence transcript move.slot) :=
  exists_pairingSlotOccurrence transcript move.slot
    (classification.importantMove_slot_mem_pairings move member)

/--
An unimportant boundary move's slot belongs to the concrete transcript.
-/
theorem unimportantMove_slot_mem_pairings
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.unimportantMoves) :
    move.slot ∈ firstPairings kinds ++ secondPairings kinds := by
  have mappedMember :
      move.slot ∈
        classification.unimportantMoves.map BoundaryPairingMove.slot :=
    List.mem_map.mpr ⟨move, member, rfl⟩
  have unimportantMember :
      move.slot ∈
        classification.passClassification.unimportantSlots := by
    rw [← classification.unimportantSlots_eq]
    exact mappedMember
  have classifiedMember :
      move.slot ∈
        classification.passClassification.importantSlots ++
          classification.passClassification.unimportantSlots ++
            classification.passClassification.internalCharges.map
              Prod.fst := by
    exact
      List.mem_append_left _
        (List.mem_append_right _ unimportantMember)
  exact
    classification.passClassification.slots_partition.mem_iff.mp
      classifiedMember

/--
An unimportant delete/insert move carries the exact splay zig-zig geometry
of the slot to which that move is assigned.
-/
theorem unimportantMove_geometry
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.unimportantMoves) :
    Nonempty (PairingSlotOccurrence transcript move.slot) :=
  exists_pairingSlotOccurrence transcript move.slot
    (classification.unimportantMove_slot_mem_pairings move member)

/--
The internal charges nested inside a boundary classification retain the same
exact chronological splay geometry.
-/
theorem internalCharge_geometry
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (charge :
      PairingSlot ×
        Interface.ActivitySlot (Lazy.eraseOperations events))
    (member :
      charge ∈
        classification.passClassification.internalCharges) :
    Nonempty (PairingSlotOccurrence transcript charge.1) :=
  classification.passClassification.internalCharge_geometry charge member

end BoundaryPassPairingClassification

end Splay.Accounting
