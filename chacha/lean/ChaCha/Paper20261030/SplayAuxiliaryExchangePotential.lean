import ChaCha.Paper20261030.SplayAuxiliaryPotential

/-!
# Potential of a prepared primary-path exchange

The active root auxiliary is split by an ordinary splay, the exposed old
and incoming tails are splayed at their boundary, and their roles are
exchanged. Only one new root rank is introduced. Both old potentials are
retained, including the parked tail; no auxiliary is reinitialized.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open MultiSplay.Auxiliary

variable {κ : Type*} [DecidableEq κ]

theorem splay_exchange_amortized {before leftPart suffix incoming : RawTree κ}
    {pivot : κ} {rotations capacity : Nat}
    (execution : Splay pivot before (.node leftPart pivot suffix) rotations)
    (unique : before.inorder.Nodup) (fits : before.size ≤ capacity)
    (joined : (ChaCha.MTR.Tree.node leftPart pivot incoming).size ≤ capacity) :
    rotations+2*(potential (.node leftPart pivot incoming)+potential suffix) ≤
      2*(potential before+potential incoming)+8*Nat.log 2 capacity+1 := by
  have access := splay_amortized_capacity execution unique fits
  have newRank : rank (.node leftPart pivot incoming) ≤ Nat.log 2 capacity := Nat.log_mono_right joined
  simp only [potential] at access ⊢
  omega

/-- Three actual bottom-up splays implement the exposed exchange. The
same boundary key is splayed in two distinct physical auxiliaries. -/
theorem exposed_exchange_amortized {before leftPart suffix incoming oldTail newTail : RawTree κ}
    {pivot boundary : κ} {splitWork oldWork incomingWork capacity : Nat}
    (split : Splay pivot before (.node leftPart pivot suffix) splitWork)
    (oldExpose : Splay boundary suffix (.node .empty boundary oldTail) oldWork)
    (incomingExpose : Splay boundary incoming (.node .empty boundary newTail) incomingWork)
    (unique : before.inorder.Nodup) (incomingUnique : incoming.inorder.Nodup)
    (fits : before.size ≤ capacity) (incomingFits : incoming.size ≤ capacity)
    (joined : (ChaCha.MTR.Tree.node leftPart pivot (.node .empty boundary newTail)).size ≤ capacity) :
    splitWork+oldWork+incomingWork+
        2*(potential (.node leftPart pivot (.node .empty boundary newTail))+
          potential (.node .empty boundary oldTail)) ≤
      2*(potential before+potential incoming)+20*Nat.log 2 capacity+3 := by
  have splitBound := splay_amortized_capacity split unique fits
  have parts := nodup_node (split.inorder_eq ▸ unique)
  have suffixFits : suffix.size ≤ capacity := by
    have same := split.size_eq
    simp only [ChaCha.MTR.Tree.size] at same
    omega
  have oldBound := splay_amortized_capacity oldExpose parts.2.1 suffixFits
  have incomingBound := splay_amortized_capacity incomingExpose incomingUnique incomingFits
  have newRank : rank (.node leftPart pivot (.node .empty boundary newTail)) ≤ Nat.log 2 capacity :=
    Nat.log_mono_right joined
  simp only [potential] at splitBound oldBound incomingBound ⊢
  omega

end ChaCha.Paper20261030.SplayAuxiliary
