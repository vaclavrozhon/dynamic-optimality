import ChaCha.Paper20261030.GlobalPrimaryOnlineState

set_option autoImplicit false

/-! An explicit initial maintained state for any perfect primary tree.
Unlike the choice of a future physical transition, initialization of
these logical components is an ordinary computable definition. -/

namespace ChaCha.Paper20261030.OnlineSpecification

open ColoredStorage PreferredProjection Secondary SecondaryDecomposition LocalReferences

variable {α : Type*} [DecidableEq α] {h : Nat}

def initialState (reference : DepthTree 0 h) (primary : PrefRouter α)
    (perfect : primary.Perfect (h+1)) : State reference primary.leaves := {
  memory := MemoryState.initial primary
  perfect := perfect
  components := initialComponents (completedDepth reference) primary perfect (fun _ => true)
  valid := initialComponents_valid _ _ _ _
  word := rfl }

theorem initialState_tree_word (reference : DepthTree 0 h) (primary : PrefRouter α)
    (perfect : primary.Perfect (h+1)) (distinct : primary.leaves.Nodup) :
    (initialState reference primary perfect).tree.inorder = primary.leaves :=
  (initialState reference primary perfect).tree_word distinct

theorem initialState_bounded (reference : DepthTree 0 h) (primary : PrefRouter α)
    (perfect : primary.Perfect (h+1)) :
    GapBST.Storage.Bounded 5 (initialState reference primary perfect).physical :=
  GapBST.Storage.encode_bounded (physicalState_bounded _ _)

theorem canonicalState_eq_initialState (reference : DepthTree 0 h) :
    canonicalState reference = initialState reference (Dyadic.canonical (h+1) 0)
      (Dyadic.canonical_perfect _ _) := rfl

end ChaCha.Paper20261030.OnlineSpecification
