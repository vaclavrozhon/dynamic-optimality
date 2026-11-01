import MultiSplay.JoinAttachment
import Splay.Accounting.ArticleRelocationUnbroken

/-! # Transport of the full cross-side unbroken-block invariant -/

namespace MultiSplay.UnbrokenEmbedding

open Splay.Tree (BST)
open Splay.Rank (Snapshot External)
open Splay.Lazy (Block Element HeapView)
open Splay.Lazy.Canonical
open Splay.Accounting

variable {n m : Nat}

theorem iff_unbroken (offset depth : Nat) (fits : offset+n ≤ m)
    (before : Snapshot n) (after : Snapshot m) (small : Splay.Tree.BST 0 n) (big : Splay.Tree.BST 0 m)
    (children : ∀ owner side, (canonicalHeapView after big).topDown (RankEmbedding.external offset fits owner) side =
      ((canonicalHeapView before small).topDown owner side).map (RankEmbedding.external offset fits))
    (edges : ∀ x edge, incomingEdge? before small x = some edge →
      incomingEdge? after big (RankEmbedding.external offset fits x) = some (RankEmbedding.edge offset depth fits edge))
    (block : Block n) (assigned : List (Element n))
    (valid : block.StructurallyValid (canonicalHeapView before small) assigned) :
    canonicalBlockCrossSideUnbroken after big (BlockEmbedding.block (RankEmbedding.external offset fits) block) ↔
      canonicalBlockCrossSideUnbroken before small block := by
  let e := RankEmbedding.external offset fits
  have memberNotRoot : ∀ x ∈ block.elements, x ≠ canonicalRoot before small :=
    fun _ member => BlockEmbedding.member_ne_root _ block assigned valid member
  have parentNotRoot : ∀ x owner, canonicalParent before small x = some owner → x ≠ canonicalRoot before small := by
    intro x owner parent same
    have rootParent := (canonicalHeapView before small).root_parent
    change canonicalParent before small (canonicalRoot before small) = none at rootParent
    rw [same, rootParent] at parent
    cases parent
  constructor
  · intro unbroken x xMem z zMem y parent opposite between
    have localMember : y ∈ (canonicalHeapView before small).topDown block.owner (canonicalSide before small y) :=
      (canonicalHeapView before small).mem_topDown_iff.mpr ⟨parent, rfl⟩
    have globalMember : e y ∈ (canonicalHeapView after big).topDown (e block.owner) (canonicalSide before small y) := by
      rw [children]
      exact List.mem_map.mpr ⟨y, localMember, rfl⟩
    obtain ⟨globalParent, globalSide⟩ := (canonicalHeapView after big).mem_topDown_iff.mp globalMember
    apply unbroken (e x) (List.mem_map.mpr ⟨x, xMem, rfl⟩) (e z) (List.mem_map.mpr ⟨z, zMem, rfl⟩) (e y) globalParent
      (fun same => opposite (globalSide.symm.trans same))
    exact (JoinAttachment.between_iff offset depth fits before after small big edges x y z
      (memberNotRoot x xMem) (parentNotRoot y block.owner parent) (memberNotRoot z zMem)).mpr between
  · intro unbroken x xMem z zMem y parent opposite between
    obtain ⟨oldX, oldXMem, rfl⟩ := List.mem_map.mp xMem
    obtain ⟨oldZ, oldZMem, rfl⟩ := List.mem_map.mp zMem
    have globalMember : y ∈ (canonicalHeapView after big).topDown (e block.owner) (canonicalSide after big y) :=
      (canonicalHeapView after big).mem_topDown_iff.mpr ⟨parent, rfl⟩
    rw [children] at globalMember
    obtain ⟨oldY, oldYMem, oldYEq⟩ := List.mem_map.mp globalMember
    obtain ⟨localParent, localSide⟩ := (canonicalHeapView before small).mem_topDown_iff.mp oldYMem
    have localOpposite : canonicalSide before small oldY ≠ block.side := fun same => opposite (localSide.symm.trans same)
    apply unbroken oldX oldXMem oldZ oldZMem oldY localParent localOpposite
    rw [← oldYEq] at between
    exact (JoinAttachment.between_iff offset depth fits before after small big edges oldX oldY oldZ
      (memberNotRoot oldX oldXMem) (parentNotRoot oldY block.owner localParent) (memberNotRoot oldZ oldZMem)).mp between

end MultiSplay.UnbrokenEmbedding
