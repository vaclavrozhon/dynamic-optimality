import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! # A three-way partition retaining multiplicities -/

namespace MultiSplay.ListPartition

theorem three {α : Type*} (values : List α) (first second third : α → Prop)
    [DecidablePred first] [DecidablePred second] [DecidablePred third]
    (disjoint : ∀ x, second x → ¬ first x)
    (remaining : ∀ x, third x ↔ ¬ second x ∧ ¬ first x) :
    ((values.filter (fun x => decide (first x))) ++ (values.filter (fun x => decide (second x))) ++
      (values.filter (fun x => decide (third x)))).Perm values := by
  classical
  have two := List.filter_append_perm (fun x => decide (second x)) (values.filter (fun x => !decide (first x)))
  have secondEq : (values.filter (fun x => !decide (first x))).filter (fun x => decide (second x)) =
      values.filter (fun x => decide (second x)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    have h := disjoint x
    by_cases p : first x <;> by_cases q : second x <;> simp_all
  have thirdEq : (values.filter (fun x => !decide (first x))).filter (fun x => !decide (second x)) =
      values.filter (fun x => decide (third x)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    have h := remaining x
    by_cases p : first x <;> by_cases q : second x <;> simp_all
  rw [secondEq, thirdEq] at two
  simpa only [List.append_assoc] using
    (two.append_left (values.filter (fun x => decide (first x)))).trans (List.filter_append_perm (fun x => decide (first x)) values)

end MultiSplay.ListPartition
