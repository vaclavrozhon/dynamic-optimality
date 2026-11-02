import ChaCha.Paper20261030.SeparatorPath
import ChaCha.Paper20261030.PathInitialization

/-!
# A balanced separator auxiliary from the actual reference path

Every reference vertex carries its split, preference, separator key, and
an initially zero size cache. The path initializer balances the current
preferred path in place and repairs those caches. The result has exactly
the separator-ordered record word; its original off-path references and
endpoint remain in their corresponding gaps.
-/

namespace ChaCha.Paper20261030.SeparatorPath

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

abbrev Cached := NodeRecord Nat (fun _ => Record)

def followsRight (record : Cached) : Bool := record.2.2.2

def source : {a b : Nat} → DepthTree a b → (DepthSplit → Bool) → Source Nat Cached
  | _,_,.leaf a,_ => .leaf a (0,⟨a,(⟨a,a,a⟩,false)⟩)
  | a,b,.node cut _ _ l r,preference =>
      .fork (0,⟨cut,(⟨a,cut,b⟩,preference ⟨a,cut,b⟩)⟩)
        (source l preference) (source r preference)

theorem source_shape {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (source reference preference).shape = LocalReferences.depthReference reference := by
  induction reference <;> simp_all [source,Source.shape,LocalReferences.depthReference]

theorem skeleton_word {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (fromRecordTree (PathPorts.skeleton followsRight (source reference preference))).toListModel =
      word reference preference := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : preference ⟨a,cut,b⟩ <;>
      simp [source,PathPorts.skeleton,followsRight,hp,fromRecordTree,Impl.toListModel,word,ihl,ihr]

theorem skeleton_size {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (PathPorts.skeleton followsRight (source reference preference)).size =
      (word reference preference).length := by
  rw [← actualSize_fromRecordTree,actualSize_length,skeleton_word]

def balancedAuxiliary {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :=
  PathPorts.auxiliary followsRight (source reference preference)

theorem balancedAuxiliary_word {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (balancedAuxiliary reference preference).impl.toListModel = word reference preference := by
  rw [balancedAuxiliary,PathPorts.auxiliary_word,skeleton_word]

theorem balancedAuxiliary_ordered {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) : (balancedAuxiliary reference preference).impl.Ordered := by
  simpa only [Impl.Ordered,balancedAuxiliary_word,Nat.compare_eq_lt] using keys_increasing reference preference

theorem balancedAuxiliary_height {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    height (balancedAuxiliary reference preference).impl ≤
      3 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) := by
  have hh := PathPorts.auxiliary_height followsRight (source reference preference)
  rw [skeleton_size] at hh
  have hm := Nat.clog_monotone 2 (Nat.add_le_add_right (word_length reference preference) 1)
  exact hh.trans (by omega)

theorem initialize_path {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (ancestors : List (SourcePointer.Frame Nat Cached)) :
    ∃ (reads : List Cached) (cost : Nat),
      SourcePointer.Trace ⟨source reference preference,ancestors⟩ reads
        ⟨PathPorts.balancedSource followsRight (source reference preference),ancestors⟩ cost ∧
      cost ≤ (990 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 81) *
        (word reference preference).length := by
  obtain ⟨reads,cost,trace,hcost⟩ := PathPorts.balance_charged followsRight (source reference preference) ancestors
  rw [skeleton_size] at hcost
  have hm := Nat.clog_monotone 2 (Nat.add_le_add_right (word_length reference preference) 1)
  refine ⟨reads,cost,trace,hcost.trans ?_⟩
  exact Nat.mul_le_mul_right _ (by omega)

end ChaCha.Paper20261030.SeparatorPath
