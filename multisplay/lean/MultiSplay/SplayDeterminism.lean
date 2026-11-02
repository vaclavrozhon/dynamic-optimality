import MultiSplay.SplayPointer
import Mathlib.Data.List.Nodup

/-! # Uniqueness of standard splaying on distinct physical keys -/

namespace MultiSplay.Auxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder rootKey)

variable {α : Type*} {key : α}

theorem nodup_node {left right : RawTree α} {pivot : α}
    (unique : (inorder (.node left pivot right)).Nodup) :
    (inorder left).Nodup ∧ (inorder right).Nodup ∧
      pivot ∉ inorder left ∧ pivot ∉ inorder right ∧
      List.Disjoint (inorder left) (inorder right) := by
  simpa [inorder, List.nodup_append', List.disjoint_append_left, List.disjoint_append_right,
    and_assoc, and_left_comm, and_comm] using unique

theorem Double.member {a b : RawTree α} (step : Double key a b) : key ∈ inorder a := by
  induction step <;> simp_all [inorder]

theorem Double.not_root {a b : RawTree α} (step : Double key a b)
    (unique : (inorder a).Nodup) : rootKey a ≠ some key := by
  intro root
  cases step with
  | leftLeft | rightRight | leftRight | rightLeft =>
      simp only [rootKey, Option.some.injEq] at root
      subst_vars
      simp [inorder, List.nodup_append'] at unique
  | leftContext inside pivot right =>
      have present := inside.member
      have absent := (nodup_node unique).2.2.1
      simp only [rootKey, Option.some.injEq] at root
      exact absent (root ▸ present)
  | rightContext left pivot inside =>
      have present := inside.member
      have absent := (nodup_node unique).2.2.2.1
      simp only [rootKey, Option.some.injEq] at root
      exact absent (root ▸ present)

theorem root_member {tree : RawTree α} (root : rootKey tree = some key) : key ∈ inorder tree := by
  cases tree with
  | empty => simp [rootKey] at root
  | node left pivot right =>
      simp only [rootKey, Option.some.injEq] at root
      subst pivot
      simp [inorder]

theorem Double.not_child {left right target : RawTree α} {pivot : α}
    (step : Double key (.node left pivot right) target)
    (unique : (inorder (.node left pivot right)).Nodup) :
    rootKey left ≠ some key ∧ rootKey right ≠ some key := by
  have parts := nodup_node unique
  cases step with
  | leftLeft a b c d y z =>
      constructor
      · intro root
        have absent := (nodup_node parts.1).2.2.1
        simp only [rootKey, Option.some.injEq] at root
        rw [root] at absent
        exact absent (by simp [inorder])
      · intro root
        exact List.disjoint_left.mp parts.2.2.2.2 (by simp [inorder]) (root_member root)
  | rightRight a b c d x y =>
      constructor
      · intro root
        exact List.disjoint_left.mp parts.2.2.2.2 (root_member root) (by simp [inorder])
      · intro root
        have absent := (nodup_node parts.2.1).2.2.2.1
        simp only [rootKey, Option.some.injEq] at root
        rw [root] at absent
        exact absent (by simp [inorder])
  | leftRight a b c d x z =>
      constructor
      · intro root
        have absent := (nodup_node parts.1).2.2.2.1
        simp only [rootKey, Option.some.injEq] at root
        rw [root] at absent
        exact absent (by simp [inorder])
      · intro root
        exact List.disjoint_left.mp parts.2.2.2.2 (by simp [inorder]) (root_member root)
  | rightLeft a b c d x z =>
      constructor
      · intro root
        exact List.disjoint_left.mp parts.2.2.2.2 (root_member root) (by simp [inorder])
      · intro root
        have absent := (nodup_node parts.2.1).2.2.1
        simp only [rootKey, Option.some.injEq] at root
        rw [root] at absent
        exact absent (by simp [inorder])
  | leftContext inside pivot right =>
      exact ⟨inside.not_root parts.1, fun root =>
        List.disjoint_left.mp parts.2.2.2.2 inside.member (root_member root)⟩
  | rightContext left pivot inside =>
      exact ⟨fun root => List.disjoint_left.mp parts.2.2.2.2 (root_member root) inside.member,
        inside.not_root parts.2.1⟩

theorem Double.deterministic {a b c : RawTree α} (first : Double key a b)
    (second : Double key a c) (unique : (inorder a).Nodup) : b = c := by
  induction first generalizing c with
  | leftLeft a b c d y z =>
      cases second with
      | leftLeft => rfl
      | rightRight | leftRight | rightLeft => simp [inorder, List.nodup_append'] at unique
      | leftContext inside _ _ => exact False.elim ((inside.not_child (nodup_node unique).1).1 rfl)
      | rightContext _ _ inside =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 (by simp [inorder]) inside.member)
  | rightRight a b c d x y =>
      cases second with
      | rightRight => rfl
      | leftLeft | leftRight | rightLeft => simp [inorder, List.nodup_append'] at unique
      | leftContext inside _ _ =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 inside.member (by simp [inorder]))
      | rightContext _ _ inside => exact False.elim ((inside.not_child (nodup_node unique).2.1).2 rfl)
  | leftRight a b c d x z =>
      cases second with
      | leftRight => rfl
      | leftLeft | rightRight | rightLeft => simp [inorder, List.nodup_append'] at unique
      | leftContext inside _ _ => exact False.elim ((inside.not_child (nodup_node unique).1).2 rfl)
      | rightContext _ _ inside =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 (by simp [inorder]) inside.member)
  | rightLeft a b c d x z =>
      cases second with
      | rightLeft => rfl
      | leftLeft | rightRight | leftRight => simp [inorder, List.nodup_append'] at unique
      | leftContext inside _ _ =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 inside.member (by simp [inorder]))
      | rightContext _ _ inside => exact False.elim ((inside.not_child (nodup_node unique).2.1).1 rfl)
  | leftContext inside pivot right ih =>
      cases second with
      | leftLeft => exact False.elim ((inside.not_child (nodup_node unique).1).1 rfl)
      | leftRight => exact False.elim ((inside.not_child (nodup_node unique).1).2 rfl)
      | rightRight | rightLeft =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 inside.member (by simp [inorder]))
      | leftContext other _ _ => exact congrArg (fun tree => ChaCha.MTR.Tree.node tree pivot right) (ih other (nodup_node unique).1)
      | rightContext _ _ other =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 inside.member other.member)
  | rightContext left pivot inside ih =>
      cases second with
      | rightRight => exact False.elim ((inside.not_child (nodup_node unique).2.1).2 rfl)
      | rightLeft => exact False.elim ((inside.not_child (nodup_node unique).2.1).1 rfl)
      | leftLeft | leftRight =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 (by simp [inorder]) inside.member)
      | rightContext _ _ other => exact congrArg (fun tree => ChaCha.MTR.Tree.node left pivot tree) (ih other (nodup_node unique).2.1)
      | leftContext other _ _ =>
          exact False.elim (List.disjoint_left.mp (nodup_node unique).2.2.2.2 other.member inside.member)

theorem Step.not_root {a b : RawTree α} {cost : Nat} (step : Step key a b cost)
    (unique : (inorder a).Nodup) : rootKey a ≠ some key := by
  cases step with
  | zigLeft | zigRight =>
      intro root
      simp only [rootKey, Option.some.injEq] at root
      subst_vars
      simp [inorder, List.nodup_append'] at unique
  | double step => exact step.not_root unique

theorem Step.deterministic {a b c : RawTree α} {x y : Nat}
    (first : Step key a b x) (second : Step key a c y)
    (unique : (inorder a).Nodup) : b = c ∧ x = y := by
  cases first with
  | zigLeft =>
      cases second with
      | zigLeft => exact ⟨rfl, rfl⟩
      | zigRight => simp [inorder, List.nodup_append'] at unique
      | double step => exact False.elim ((step.not_child unique).1 rfl)
  | zigRight =>
      cases second with
      | zigRight => exact ⟨rfl, rfl⟩
      | zigLeft => simp [inorder, List.nodup_append'] at unique
      | double step => exact False.elim ((step.not_child unique).2 rfl)
  | double step =>
      cases second with
      | zigLeft => exact False.elim ((step.not_child unique).1 rfl)
      | zigRight => exact False.elim ((step.not_child unique).2 rfl)
      | double other => exact ⟨step.deterministic other unique, rfl⟩

/-- Standard splaying fixes both the final physical shape and its exact
rotation count. Distinctness is required only of the input keys. -/
theorem Splay.deterministic {a b c : RawTree α} {x y : Nat}
    (first : Splay key a b x) (second : Splay key a c y)
    (unique : (inorder a).Nodup) : b = c ∧ x = y := by
  induction first generalizing c y with
  | done left right =>
      cases second with
      | done => exact ⟨rfl, rfl⟩
      | next step rest => exact False.elim (step.not_root unique rfl)
  | next step rest ih =>
      cases second with
      | done => exact False.elim (step.not_root unique rfl)
      | next other later =>
          obtain ⟨rfl, rfl⟩ := step.deterministic other unique
          obtain ⟨same, work⟩ := ih later (step.inorder_eq ▸ unique)
          exact ⟨same, by omega⟩

theorem Splay.member {a b : RawTree α} {cost : Nat} (execution : Splay key a b cost) : key ∈ inorder a := by
  rw [execution.inorder_eq]
  exact root_member execution.root_after

/-- Every supplied standard splay transcript has the shared pointer-model
implementation, including a single initial descent and the final access. -/
theorem Splay.pointer {a b : RawTree α} {rotations : Nat} (execution : Splay key a b rotations)
    (unique : (inorder a).Nodup) (outer : List (ChaCha.MTR.Pointer.Frame α)) :
    ChaCha.MTR.Pointer.Trace ⟨a, outer⟩ [key] ⟨b, outer⟩ (3*rotations+1) := by
  obtain ⟨result, count, run, physical⟩ := exists_pointer_splay execution.member
  obtain ⟨rfl, rfl⟩ := execution.deterministic run unique
  exact physical outer

end MultiSplay.Auxiliary
