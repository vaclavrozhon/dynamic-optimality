import DynamicOptimality.Funnel.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Decomposing funnel edge and switch counts by their apex -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

def incoming (word : Fin m → α) (active : Finset (Fin m)) (p : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (Visible word active p)

@[simp] theorem mem_incoming {word : Fin m → α} {active : Finset (Fin m)} {p q : Fin m} :
    q ∈ incoming word active p ↔ Visible word active p q := by simp [incoming]

theorem edgeCount_eq_sum (word : Fin m → α) (active : Finset (Fin m)) :
    edgeCount word active = ∑ p : Fin m, (incoming word active p).card := by
  unfold edgeCount
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.card_bij (fun q _ => (q,p))
  · intro q hq
    exact Finset.mem_filter.mpr ⟨mem_edges.mpr (mem_incoming.mp hq),rfl⟩
  · intro q hq r hr equal
    exact congrArg Prod.fst equal
  · rintro ⟨q,r⟩ member
    obtain ⟨edge,same⟩ := Finset.mem_filter.mp member
    change r = p at same
    subst r
    exact ⟨q,mem_incoming.mpr (mem_edges.mp edge),rfl⟩

end DynamicOptimality.Funnel
