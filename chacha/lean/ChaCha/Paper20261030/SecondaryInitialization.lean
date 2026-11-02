import ChaCha.Paper20261030.AuxiliaryComponents
import ChaCha.Paper20261030.SeparatorInitialization

/-!
# Initializing all secondary auxiliaries in an existing reference tree

Initialize the two child references, then insert their parent separator
into the preferred child's balanced auxiliary. The other child remains
one hanging port. This constructs every preferred-path auxiliary using
actual reads, child excursions, and charged insertions. If the reference
height is at most `K`, the total cost is at most
`(495 clog 2 (K+1) + 81)` times its number of internal vertices.

The input is the existing separator-decorated secondary reference. The
additional compilation and original-key initialization remain separate.
-/

namespace ChaCha.Paper20261030.SeparatorPath

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata RouterProjection

def initializeReference : {a b : Nat} → DepthTree a b → (DepthSplit → Bool) →
    AuxiliaryComponent Nat Nat (fun _ => Record)
  | _,_,.leaf a,_ => AuxiliaryComponent.terminal (.leaf a (0,⟨a,(⟨a,a,a⟩,false)⟩))
  | a,b,.node cut _ _ l r,preference =>
      let left := initializeReference l preference
      let right := initializeReference r preference
      if preference ⟨a,cut,b⟩ then
        AuxiliaryComponent.prepend cut (⟨a,cut,b⟩,true) left.tree right
      else AuxiliaryComponent.append left cut (⟨a,cut,b⟩,false) right.tree

theorem initialize_word {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (initializeReference reference preference).core.toListModel = word reference preference := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : preference ⟨a,cut,b⟩ <;>
      simp only [initializeReference,word,hp,Bool.false_eq_true,if_false,if_true,
        AuxiliaryComponent.prepend_word,AuxiliaryComponent.append_word,ihl,ihr]

theorem initialize_ordered {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (initializeReference reference preference).core.Ordered := by
  simpa only [Impl.Ordered,initialize_word,Nat.compare_eq_lt] using keys_increasing reference preference

theorem initialize_size {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (initializeReference reference preference).core.size = (word reference preference).length := by
  rw [size_eq_length _ (initializeReference reference preference).balanced,initialize_word]

theorem initialize_size_bound {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (initializeReference reference preference).core.size ≤ (LocalReferences.depthReference reference).height := by
  rw [initialize_size]
  exact word_length reference preference

theorem initialize_charged {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool)
    (K : Nat) (hheight : (LocalReferences.depthReference reference).height ≤ K) :
    SourcePointer.Rearranges (source reference preference) (initializeReference reference preference).tree
      ((495 * Nat.clog 2 (K + 1) + 81) * (b - a)) := by
  induction reference with
  | leaf a => exact SourcePointer.rearranges_refl _ _
  | @node a b cut ha hb l r ihl ihr =>
    have hl : (LocalReferences.depthReference l).height ≤ K := by
      simp only [LocalReferences.depthReference,Router.height] at hheight; omega
    have hr : (LocalReferences.depthReference r).height ≤ K := by
      simp only [LocalReferences.depthReference,Router.height] at hheight; omega
    have hleft := ihl hl
    have hright := ihr hr
    have read : SourcePointer.Rearranges
        (source (.node cut ha hb l r) preference)
        (source (.node cut ha hb l r) preference) 1 :=
      fun rest => ⟨_,1,.read (.nil _),le_rfl⟩
    have prepared := (read.trans hleft.left).trans hright.right
    cases hp : preference ⟨a,cut,b⟩
    · have inserted := AuxiliaryComponent.append_charged (initializeReference l preference) cut
        (⟨a,cut,b⟩,false) (initializeReference r preference).tree 0
      simp only [source,hp] at prepared
      have full := prepared.trans inserted
      simp only [initializeReference,source,hp,Bool.false_eq_true,if_false]
      apply full.mono
      have hm := Nat.clog_monotone 2
        (Nat.add_le_add_right ((initialize_size_bound l preference).trans hl) 1)
      have hs : b - a = (cut - a) + (b - (cut + 1)) + 1 := by omega
      rw [hs,Nat.mul_add,Nat.mul_add,Nat.mul_one]
      omega
    · have inserted := AuxiliaryComponent.prepend_charged cut (⟨a,cut,b⟩,true)
        (initializeReference l preference).tree (initializeReference r preference) 0
      simp only [source,hp] at prepared
      have full := prepared.trans inserted
      simp only [initializeReference,source,hp,if_true]
      apply full.mono
      have hm := Nat.clog_monotone 2
        (Nat.add_le_add_right ((initialize_size_bound r preference).trans hr) 1)
      have hs : b - a = (cut - a) + (b - (cut + 1)) + 1 := by omega
      rw [hs,Nat.mul_add,Nat.mul_add,Nat.mul_one]
      omega

theorem initialize_leaves {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (initializeReference reference preference).tree.shape.leaves = List.range' a (b + 1 - a) := by
  obtain ⟨reads,cost,trace,_⟩ := initialize_charged reference preference
    (LocalReferences.depthReference reference).height le_rfl []
  have he := trace.leaves.symm
  simpa only [SourcePointer.Cursor.tree,SourcePointer.plug,source_shape,LocalReferences.depthReference_leaves] using he

end ChaCha.Paper20261030.SeparatorPath
