import MultiSplay.ComparatorPrimaryAccess

/-! # Variable terminal depths without additional physical keys

The fixed global depth alphabet may extend beyond a component's actual
terminal depth. These extra depths have no real exit and are projected to
the existing virtual color. They create no physical node. The projection
uses no bounded virtual header: all source records are ghost information
in the accepted model, while the resulting ordinary BST and its charged
preparation are explicit.
-/

namespace MultiSplay.ComparatorPrimary

open ChaCha
open Paper20261030
open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical

/-- A longer depth alphabet still names exactly the actual exits. -/
theorem portAt_extended_word {β : Type*} (start : Nat) (ports : List β)
    (count : Nat) (longEnough : ports.length ≤ count) :
    (List.range' start count).filterMap (portAt start ports) = ports := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le longEnough
  induction extra with
  | zero => simpa only [Nat.add_zero] using portAt_word start ports
  | succ extra ih =>
      rw [← Nat.add_assoc,← List.range'_append_1,List.filterMap_append,ih (by omega)]
      have absent : portAt start ports (start + (ports.length + extra)) = none := by
        simp only [portAt,if_pos (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
        exact List.getElem?_eq_none (by omega)
      simp only [List.range'_one,List.filterMap_cons,absent,List.filterMap_nil,List.append_nil]

/-- The header is empty because the full mathematical source is maintained
separately. The two real routing wings use the proved packed projection. -/
def projected {ρ : Type*} (start : Nat) (primary : PrefRouter Nat) (source : Source Nat ρ) :
    Source Nat (List (Option (PackedPrimary.Datum ρ))) :=
  component (graftWing (collapsed ρ) (PackedPrimary.liftWing (PackedPrimary.plan start primary source).left))
    (graftWing (collapsed ρ) (PackedPrimary.liftWing (PackedPrimary.plan start primary source).right))
    primary.terminal []

theorem projected_leaves {ρ : Type*} (start : Nat) (primary : PrefRouter Nat) (source : Source Nat ρ)
    (ports : source.shape.leaves.filterMap (portAt start (exits primary)) = exits primary) :
    (projected start primary source).shape.leaves = gapWord primary := by
  obtain ⟨leftWord,rightWord⟩ := PackedPrimary.plan_words start primary source ports
  rw [projected,PrimaryPhysical.component_leaves,graftWing_leaves,graftWing_leaves,
    PackedPrimary.liftWing_word,PackedPrimary.liftWing_word,leftWord,rightWord]
  simp only [collapsed,Source.shape,RouterProjection.Router.leaves,← List.map_eq_flatMap]
  rfl

def projectedTree {lower upper : Nat} {ρ : Type*} (state : EndpointEncoding.State)
    (reference : DynamicOptimality.BST lower upper) (start : Nat) (source : Source Nat ρ) :
    DynamicOptimality.RawTree Nat := GapBST.gaps (projected start (routing state reference) source)

theorem projectedTree_inorder {lower upper : Nat} {ρ : Type*} (state : EndpointEncoding.State)
    (reference : DynamicOptimality.BST lower upper) (start : Nat) (source : Source Nat ρ)
    (ports : source.shape.leaves.filterMap (portAt start (exits (routing state reference))) =
      exits (routing state reference)) :
    (projectedTree state reference start source).inorder =
      (ClassicalSwitch.preferred state reference.toRaw).inorder := by
  have words := (GapBST.gaps_word (projected start (routing state reference) source)).trans
    ((projected_leaves start (routing state reference) source ports).trans (gapWord_routing state reference))
  have prefixes := congrArg List.dropLast words
  simpa only [projectedTree,List.dropLast_append_cons,List.dropLast_singleton,List.append_nil] using prefixes

theorem projected_rearranges {ρ : Type*} (start : Nat) (primary : PrefRouter Nat)
    {before after : Source Nat ρ} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    SourcePointer.Rearranges (projected start primary before) (projected start primary after)
      (68*budget+12) := by
  have left := PackedPrimary.left_payload_rearranges start primary (collapsed ρ) execution
  have right := PackedPrimary.right_payload_rearranges start primary (collapsed ρ) execution
  exact (component_rearranges primary.terminal [] [] left right).mono (by omega)

theorem projected_program {lower upper : Nat} {ρ : Type*} (state : EndpointEncoding.State)
    (reference : DynamicOptimality.BST lower upper) (start : Nat)
    {before after : Source Nat ρ} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    ∃ work ≤ 816 * budget + 156,
      CommonForest.Program [projectedTree state reference start before] []
        [projectedTree state reference start after] work := by
  obtain ⟨work,bound,run⟩ := ComparatorGap.rearranges_program (projected_rearranges start (routing state reference) execution)
  exact ⟨work,by omega,run⟩

/-- The fixed global suffix directly projects to the actual component,
even when this preferred path reaches an external gap above global depth `b`. -/
theorem stable_projected_inorder {lower upper a b : Nat} (state : EndpointEncoding.State)
    (primary : DynamicOptimality.BST lower upper) (reference : DepthTree a b)
    (start : Nat) (valid : a ≤ start ∧ start ≤ b) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (BoundaryObservations.Tagged SecondaryDecomposition.Payload))
    (represented : PathDecomposition.Represents SecondaryDecomposition.followsRight
      (SecondaryDecomposition.suffixSource reference (ComparatorStableSuffix.bits start memory) start valid) component)
    (withinHeight : start + (exits (routing state primary)).length ≤ b) :
    (projectedTree state primary start (ComparatorRecords.erase (BoundaryObservations.closed component))).inorder =
      (ClassicalSwitch.preferred state primary.toRaw).inorder := by
  apply projectedTree_inorder
  rw [stable_leaf_word reference start valid memory component represented]
  exact portAt_extended_word start _ _ (by omega)

end MultiSplay.ComparatorPrimary
