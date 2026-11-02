import MultiSplay.GlobalSplay

/-!
# Physical checkpoints of the classical switch

The pivot is splayed in its component, followed by its stopped guard
splays. Their chronological order is retained. The resulting physical
tree already contains the old tail and incoming component in their exact
slots: marking the former and unmarking the latter changes component
membership, not physical edges. The equations below expose those slots
without rebuilding or rotating any opaque foreign subtree.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open ChaCha.MTR.Tree (graft size)

variable {α : Type*}

theorem pivot_then_left_right {pivot : α} {whole left right left' right' : RawTree α}
    {pivotWork leftWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
    (leftRotations : Rotations left left' leftWork)
    (rightRotations : Rotations right right' rightWork) :
    Rotations whole (.node left' pivot right') (pivotWork + leftWork + rightWork) := by
  exact ((splay_rotations pivotSplay).append
    (leftRotations.plug [.left pivot right])).append
    (rightRotations.plug [.right left' pivot])

theorem pivot_then_right_left {pivot : α} {whole left right left' right' : RawTree α}
    {pivotWork leftWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
    (rightRotations : Rotations right right' rightWork)
    (leftRotations : Rotations left left' leftWork) :
    Rotations whole (.node left' pivot right') (pivotWork + rightWork + leftWork) := by
  exact ((splay_rotations pivotSplay).append
    (rightRotations.plug [.right left pivot])).append
    (leftRotations.plug [.left pivot right'])

/-- The left-to-right switch physically consists of the pivot splay,
the stopped lower-guard splay, then the stopped upper-guard splay. -/
theorem leftToRight_embedded {whole left right a old b : RawTree α}
    {lower pivot upper : α} {pivotWork leftWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
    (lowerSplay : Auxiliary.Splay lower left (.node a lower old) leftWork)
    (upperSplay : Auxiliary.Splay upper right (.node .empty upper b) rightWork)
    (gaps : Nat → RawTree α) (start : Nat) (ancestors : List (Pointer.Frame α)) :
    Rotations (Pointer.plug (graft whole gaps start) ancestors)
      (Pointer.plug (graft (.node (.node a lower old) pivot (.node .empty upper b)) gaps start) ancestors)
      (pivotWork + leftWork + rightWork) :=
  (rotations_graft (pivot_then_left_right pivotSplay
    (splay_rotations lowerSplay) (splay_rotations upperSplay)) gaps start).plug ancestors

/-- Reflection reverses the guard order as well as their orientations. -/
theorem rightToLeft_embedded {whole left right a old b : RawTree α}
    {lower pivot upper : α} {pivotWork leftWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
    (upperSplay : Auxiliary.Splay upper right (.node old upper b) rightWork)
    (lowerSplay : Auxiliary.Splay lower left (.node a lower .empty) leftWork)
    (gaps : Nat → RawTree α) (start : Nat) (ancestors : List (Pointer.Frame α)) :
    Rotations (Pointer.plug (graft whole gaps start) ancestors)
      (Pointer.plug (graft (.node (.node a lower .empty) pivot (.node old upper b)) gaps start) ancestors)
      (pivotWork + rightWork + leftWork) :=
  (rotations_graft (pivot_then_right_left pivotSplay
    (splay_rotations upperSplay) (splay_rotations lowerSplay)) gaps start).plug ancestors

/-- The old tail stays physically attached below the lower guard. The
incoming component is exactly the pre-existing first right gap payload. -/
theorem leftToRight_payloads (a old b : RawTree α) (lower pivot upper : α)
    (gaps : Nat → RawTree α) (start : Nat) :
    graft (.node (.node a lower old) pivot (.node .empty upper b)) gaps start =
      .node (.node (graft a gaps start) lower (graft old gaps (start + a.size + 1))) pivot
        (.node (gaps (start + a.size + old.size + 2)) upper
          (graft b gaps (start + a.size + old.size + 3))) := by
  simp only [graft, size]
  congr 3 <;> omega

/-- The reflected equation exposes the incoming gap below the lower
guard and the unchanged old tail below the upper guard. -/
theorem rightToLeft_payloads (a old b : RawTree α) (lower pivot upper : α)
    (gaps : Nat → RawTree α) (start : Nat) :
    graft (.node (.node a lower .empty) pivot (.node old upper b)) gaps start =
      .node (.node (graft a gaps start) lower (gaps (start + a.size + 1))) pivot
        (.node (graft old gaps (start + a.size + 2)) upper
          (graft b gaps (start + a.size + old.size + 3))) := by
  simp only [graft, size]
  congr 3 <;> omega

end MultiSplay.Global
