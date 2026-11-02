import MultiSplay.SplayDeterminism
import MultiSplay.CommonForest

/-! # Distinct physical keys determine component selection by domain -/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)

variable {α : Type*}

/-- All currently present keys occur once, across the entire forest.
Empty components are allowed, with arbitrary multiplicity. -/
def UniqueKeys (forest : List (RawTree α)) : Prop := (forest.flatMap inorder).Nodup

theorem UniqueKeys.component {forest : List (RawTree α)} (unique : UniqueKeys forest)
    {tree : RawTree α} (present : tree ∈ forest) : (inorder tree).Nodup :=
  (List.nodup_flatMap.mp unique).1 tree present

theorem UniqueKeys.perm {a b : List (RawTree α)} (unique : UniqueKeys a) (order : a.Perm b) : UniqueKeys b :=
  (order.flatMap_right inorder).nodup_iff.mp unique

theorem inorder_empty {tree : RawTree α} (empty : inorder tree = []) : tree = .empty := by
  cases tree with
  | empty => rfl
  | node left pivot right => simp [inorder] at empty

theorem UniqueKeys.same_domain {forest : List (RawTree α)} (unique : UniqueKeys forest)
    {a b : RawTree α} (first : a ∈ forest) (second : b ∈ forest)
    (same : inorder a = inorder b) : a = b := by
  induction forest with
  | nil => simp at first
  | cons head tail ih =>
      have parts := List.nodup_append'.mp (show (inorder head ++ tail.flatMap inorder).Nodup from unique)
      simp only [List.mem_cons] at first second
      have overlap : ∀ tree ∈ tail, inorder head = inorder tree → head = tree := by
        intro tree member domains
        have empty : inorder head = [] := by
          by_contra nonempty
          obtain ⟨key, present⟩ := List.exists_mem_of_ne_nil (inorder head) nonempty
          exact List.disjoint_left.mp parts.2.2 present
            (List.mem_flatMap.mpr ⟨tree, member, domains ▸ present⟩)
        exact (inorder_empty empty).trans (inorder_empty (domains.symm.trans empty)).symm
      rcases first with rfl | first <;> rcases second with rfl | second
      · rfl
      · exact overlap _ second same
      · exact (overlap _ first same.symm).symm
      · exact ih parts.2.1 first second

theorem UniqueKeys.selection {forest first second : List (RawTree α)} (unique : UniqueKeys forest)
    (left : ∀ tree ∈ first, tree ∈ forest) (right : ∀ tree ∈ second, tree ∈ forest)
    (same : first.map inorder = second.map inorder) : first = second := by
  induction first generalizing second with
  | nil => exact (List.map_eq_nil_iff.mp same.symm).symm
  | cons head tail ih =>
      cases second with
      | nil => simp at same
      | cons other rest =>
          obtain ⟨domains, remaining⟩ := List.cons.inj same
          have heads := unique.same_domain (left head (by simp)) (right other (by simp)) domains
          have tails := ih (fun tree member => left tree (by simp [member]))
            (fun tree member => right tree (by simp [member])) remaining
          simp [heads, tails]

theorem UniqueKeys.cancel_selection {forest first second left right : List (RawTree α)}
    (unique : UniqueKeys forest) (a : forest.Perm (first++left)) (b : forest.Perm (second++right))
    (same : first.map inorder = second.map inorder) : first = second ∧ left.Perm right := by
  have selected := unique.selection
    (fun tree member => a.mem_iff.mpr (List.mem_append_left _ member))
    (fun tree member => b.mem_iff.mpr (List.mem_append_left _ member)) same
  refine ⟨selected, ?_⟩
  subst second
  exact (List.perm_append_left_iff _).mp (a.symm.trans b)

end MultiSplay.CommonForest
