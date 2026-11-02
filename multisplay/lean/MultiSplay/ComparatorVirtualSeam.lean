import MultiSplay.ComparatorVirtualProjection
import MultiSplay.ComparatorStableSeams

/-! # A leading virtual sentinel does not add a physical key

The optional leading depth leaf is colored virtual. Its fork record is
owned by the virtual projection as well, so neither real routing wing
changes, even at the level of stored record lists. Thus attaching this
mathematical leaf is literal equality of the original-key component before
the separately charged balanced seam operation.
-/

namespace MultiSplay.ComparatorPrimary

open ChaCha
open Paper20261030
open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical

local instance virtualSeamColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem virtual_owner {ρ : Type*} (colors : Nat → Option Bool) (key : Nat) (record : ρ)
    (right : Source Nat ρ) (virtual : colors key = none) :
    owner colors (.leaf key record) right = none := by
  unfold owner
  split
  · rename_i overlap
    have member := (Finset.mem_inter.mp (Finset.min'_mem _ overlap)).1
    simpa only [Source.support,virtual,Finset.mem_singleton] using member
  · apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_union_left _ (by simp only [Source.support,virtual,Finset.mem_singleton]))
    · change (⊥ : WithBot Bool) ≤ _
      exact bot_le

theorem packed_virtual_left {ρ : Type*} (colors : Nat → Option Bool) (key : Nat)
    (rootRecord leafRecord : ρ) (right : Source Nat ρ) (virtual : colors key = none) (side : Bool) :
    packed colors (some side) (.fork rootRecord (.leaf key leafRecord) right) = packed colors (some side) right := by
  simp only [packed,pack,virtual,virtual_owner colors key leafRecord right virtual,
    reduceCtorEq,if_false,Stored.join]

set_option backward.isDefEq.respectTransparency false in
theorem projected_virtual_left {ρ : Type*} (start : Nat) (primary : PrefRouter Nat) (key : Nat)
    (rootRecord leafRecord : ρ) (right : Source Nat ρ) (beforeStart : key < start) :
    projected start primary (.fork rootRecord (.leaf key leafRecord) right) = projected start primary right := by
  have virtual : PackedPrimary.color start primary key = none := by
    simp only [PackedPrimary.color,portAt,if_neg (by omega : ¬start ≤ key),Option.map_none]
  have wings : ∀ side, PackedPrimary.wing start primary side (.fork rootRecord (.leaf key leafRecord) right) =
      PackedPrimary.wing start primary side right := by
    intro side
    unfold PackedPrimary.wing
    rw [packed_virtual_left (PackedPrimary.color start primary) key rootRecord leafRecord right virtual side]
  simp only [projected,PackedPrimary.plan,wings]

theorem projectedTree_virtual_left {lower upper : Nat} {ρ : Type*}
    (state : EndpointEncoding.State) (reference : DynamicOptimality.BST lower upper) (start key : Nat)
    (rootRecord leafRecord : ρ) (right : Source Nat ρ) (beforeStart : key < start) :
    projectedTree state reference start (.fork rootRecord (.leaf key leafRecord) right) =
      projectedTree state reference start right := by
  rw [projectedTree,projected_virtual_left start _ key rootRecord leafRecord right beforeStart]
  rfl

/-- The incoming stable tail is converted to the prepared sentinel form
inside its own original-key component. The existing depth separator is
virtual here; the initial actual BST is exactly the old component. -/
theorem attach_original_program {lower upper a b : Nat} (state : EndpointEncoding.State)
    (primary : DynamicOptimality.BST lower upper) (reference : DepthTree a b)
    (start d : Nat) (earlier : start ≤ d) (valid : a ≤ d ∧ d < b)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (BoundaryObservations.Tagged SecondaryDecomposition.Payload))
    (represented : PathDecomposition.Represents SecondaryDecomposition.followsRight
      (SecondaryDecomposition.suffixSource reference (ComparatorStableSuffix.bits (d+1) memory)
        (d+1) ⟨by omega,by omega⟩) component) :
    ∃ out : AuxiliaryComponent Nat Nat (BoundaryObservations.Tagged SecondaryDecomposition.Payload),
      PathDecomposition.Represents SecondaryDecomposition.followsRight
        (SecondaryDecomposition.suffixSource reference
          (Secondary.intervalUpdate d (ComparatorStableSuffix.bits start memory)) d ⟨valid.1,by omega⟩) out ∧
      ∃ work ≤ 816 * (7215 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 178) + 156,
        CommonForest.Program
          [projectedTree state primary (d+1) (ComparatorRecords.erase (BoundaryObservations.closed component))] []
          [projectedTree state primary (d+1) (ComparatorRecords.erase (BoundaryObservations.closed out))] work := by
  obtain ⟨pivot,out,_,_,_,outRep,run⟩ := ComparatorStableSuffix.attach_stable_charged
    reference start d earlier valid memory component represented
  obtain ⟨work,bound,program⟩ := projected_program state primary (d+1) (run.mapRecords (fun _ => ()))
  refine ⟨out,outRep,work,bound,?_⟩
  simpa only [ComparatorRecords.erase,Source.mapRecords,SecondaryDecomposition.terminalLeaf,
    projectedTree_virtual_left state primary (d+1) d () () _ (by omega)] using program

end MultiSplay.ComparatorPrimary
