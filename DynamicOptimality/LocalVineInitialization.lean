import DynamicOptimality.LocalProgramComposition
import ChaCha.BoundaryPotential

/-! The appendix's first initialization sweep as an actual local program.
It repeatedly rotates away a left child and otherwise advances right.
A single depth counter returns the cursor to the root. No key records are
changed, and the charged reads, rotations, and moves have linear cost. -/

namespace DynamicOptimality.LocalVineInitialization

open ChaCha.MTR
open ChaCha.Paper20261030.Auxiliary
open LocalProgram
open Tree.BoundaryPotential (rightVine)

variable {α ρ : Type*}

inductive State where
  | scan (depth : Nat)
  | rotate (depth : Nat)
  | down (depth : Nat)
  | up (depth : Nat)

def program : Program State α ρ
  | .scan depth => .read (fun view =>
      if view.leftEmpty then (if view.rightEmpty then .up depth else .down depth) else .rotate depth)
  | .rotate depth => .nav .rotateRight (.scan depth)
  | .down depth => .nav .right (.scan (depth+1))
  | .up 0 => .halt
  | .up (depth+1) => .nav .up (.up depth)

private def leftSize {κ : Type*} : RawTree κ → Nat
  | .empty => 0
  | .node left _ _ => left.size

theorem normalize_prefix (tree : RawTree (NodeRecord α (fun _ => ρ))) (nonempty : tree ≠ .empty)
    (depth : Nat) (outside : List (Pointer.Frame (NodeRecord α (fun _ => ρ)))) :
    ∃ reads cost, Steps program (.scan depth) ⟨tree,outside⟩ (.up depth) ⟨rightVine tree.inorder,outside⟩ reads cost ∧
      cost+2*tree.rightLength+2 ≤ 5*tree.size := by
  cases tree with
  | empty => exact False.elim (nonempty rfl)
  | node left entry right =>
    cases left with
    | empty =>
      cases right with
      | empty =>
        refine ⟨[entry],1,?_,by simp [Tree.rightLength,Tree.size]⟩
        apply Steps.next (entry := some entry) (cost := 0)
        · apply Step.read (view := ⟨entry,true,true⟩) <;> rfl
        exact .nil _ _
      | node rl re rr =>
        obtain ⟨reads,cost,run,bound⟩ := normalize_prefix (.node rl re rr) (by simp) (depth+1) (.right .empty entry::outside)
        have back : Steps program (.up (depth+1))
            ⟨rightVine (ChaCha.MTR.Tree.node rl re rr).inorder,.right .empty entry::outside⟩ (.up depth)
            ⟨.node .empty entry (rightVine (ChaCha.MTR.Tree.node rl re rr).inorder),outside⟩ [] 1 := by
          apply Steps.next (entry := none) (cost := 0)
          · apply Step.nav (action := .up) <;> rfl
          exact .nil _ _
        refine ⟨entry::reads,cost+3,?_,?_⟩
        · have body := run.append back
          simp only [List.append_nil] at body
          apply Steps.next (entry := some entry) (cost := cost+2)
          · apply Step.read (view := ⟨entry,true,false⟩) <;> rfl
          apply Steps.next (entry := none) (cost := cost+1)
          · apply Step.nav (action := .right) <;> rfl
          simpa only [Tree.inorder,List.nil_append,List.singleton_append,rightVine] using body
        · simp only [Tree.rightLength,Tree.size] at bound ⊢
          omega
    | node a pivot b =>
      obtain ⟨reads,cost,run,bound⟩ := normalize_prefix (.node a pivot (.node b entry right)) (by simp) depth outside
      refine ⟨entry::reads,cost+2,?_,?_⟩
      · apply Steps.next (entry := some entry) (cost := cost+1)
        · apply Step.read (view := ⟨entry,false,empty right⟩) <;> rfl
        apply Steps.next (entry := none) (cost := cost)
        · apply Step.nav (action := .rotateRight) <;> rfl
        simpa only [Tree.inorder,List.append_assoc] using run
      · simp only [Tree.rightLength,Tree.size] at bound ⊢
        omega
termination_by (tree.size,leftSize tree)
decreasing_by all_goals simp_all [Tree.size,leftSize]; omega

theorem normalize (tree : RawTree (NodeRecord α (fun _ => ρ))) (nonempty : tree ≠ .empty) :
    ∃ reads cost, Run program (.scan 0) (.atRoot tree) (.up 0) (.atRoot (rightVine tree.inorder)) reads cost ∧
      cost ≤ 5*tree.size := by
  obtain ⟨reads,cost,run,bound⟩ := normalize_prefix tree nonempty 0 []
  exact ⟨reads,cost,run.run rfl,by omega⟩

end DynamicOptimality.LocalVineInitialization
