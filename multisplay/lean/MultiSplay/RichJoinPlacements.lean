import MultiSplay.RichJoin
import MultiSplay.UniqueBlockPlacement

/-! # Exactly one growing interval per side after a common join -/

namespace MultiSplay.RichJoin

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

theorem oneGrowingPerSide (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) (aGrowing : a.OneGrowingPerSide) (bGrowing : b.OneGrowingPerSide) :
    (state left right sl sr a b).OneGrowingPerSide := by
  intro owner side
  let property := fun block : Block (0 + l + 1 + r) =>
    block.mode = .growing ∧ block.owner = owner ∧ block.side = side
  change ∃! id : Fin (state left right sl sr a b).blocks.length,
    property ((state left right sl sr a b).blocks.get id)
  dsimp only [state]
  rcases JoinIntervals.cases_element l r owner with ⟨original, eq⟩ | eq | ⟨original, eq⟩
  · subst owner
    apply UniqueBlockPlacement.append_left
    · apply UniqueBlockPlacement.append_left
      · apply UniqueBlockPlacement.map _ (BlockEmbedding.block (leftEmbedding l r))
          (fun block => block.mode = .growing ∧ block.owner = original ∧ block.side = side) property
        · intro block
          have injective : Function.Injective (leftEmbedding l r) := RankEmbedding.external_injective _ _
          simp only [property, BlockEmbedding.block, injective.eq_iff]
        · exact aGrowing original side
      · intro block member fields
        obtain ⟨originalBlock, _, rfl⟩ := List.mem_map.mp member
        exact JoinIntervals.disjoint l r original originalBlock.owner fields.2.1.symm
    · intro block member fields
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals exact JoinIntervals.left_ne_pivot l r original fields.2.1.symm
  · subst owner
    apply UniqueBlockPlacement.append_right
    · cases side with
      | left =>
          refine ⟨⟨0, by simp⟩, by simp [property, rootBlock], ?_⟩
          intro id fields
          fin_cases id <;> simp_all [property, rootBlock]
      | right =>
          refine ⟨⟨1, by simp⟩, by simp [property, rootBlock], ?_⟩
          intro id fields
          fin_cases id <;> simp_all [property, rootBlock]
    · intro block member fields
      rcases List.mem_append.mp member with leftMem | rightMem
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp leftMem
        exact JoinIntervals.left_ne_pivot l r original.owner fields.2.1
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp rightMem
        exact JoinIntervals.right_ne_pivot l r original.owner fields.2.1
  · subst owner
    apply UniqueBlockPlacement.append_left
    · apply UniqueBlockPlacement.append_right
      · apply UniqueBlockPlacement.map _ (BlockEmbedding.block (rightEmbedding l r))
          (fun block => block.mode = .growing ∧ block.owner = original ∧ block.side = side) property
        · intro block
          have injective : Function.Injective (rightEmbedding l r) := RankEmbedding.external_injective _ _
          simp only [property, BlockEmbedding.block, injective.eq_iff]
        · exact bGrowing original side
      · intro block member fields
        obtain ⟨originalBlock, _, rfl⟩ := List.mem_map.mp member
        exact JoinIntervals.disjoint l r originalBlock.owner original fields.2.1
    · intro block member fields
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals exact JoinIntervals.right_ne_pivot l r original fields.2.1.symm

end MultiSplay.RichJoin
