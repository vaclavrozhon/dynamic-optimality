import DynamicOptimality.Funnel.Basic
import Mathlib.Order.Hom.Basic

/-! # Funnels depend on key order, not on the concrete key encoding -/

namespace DynamicOptimality.Funnel

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {m : Nat}

theorem between_relabel (keys : α ↪o β) (a b x : α) :
    Between (keys a) (keys b) (keys x) ↔ Between a b x := by
  simp only [Between, keys.le_iff_le]

theorem visible_relabel (word : Fin m → α) (keys : α ↪o β)
    (active : Finset (Fin m)) (p q : Fin m) :
    Visible (keys ∘ word) active p q ↔ Visible word active p q := by
  simp only [Visible,Function.comp_apply,ne_eq,keys.injective.eq_iff,between_relabel]

theorem switch_relabel (word : Fin m → α) (keys : α ↪o β)
    (active : Finset (Fin m)) (p q r : Fin m) :
    Switch (keys ∘ word) active p q r ↔ Switch word active p q r := by
  simp only [Switch,visible_relabel,Opposite,Function.comp_apply,keys.lt_iff_lt]

theorem count_relabel (word : Fin m → α) (keys : α ↪o β)
    (active : Finset (Fin m)) : count (keys ∘ word) active = count word active := by
  simp only [count,switches,switch_relabel]

theorem edgeCount_relabel (word : Fin m → α) (keys : α ↪o β)
    (active : Finset (Fin m)) : edgeCount (keys ∘ word) active = edgeCount word active := by
  simp only [edgeCount,edges,visible_relabel]

end DynamicOptimality.Funnel
