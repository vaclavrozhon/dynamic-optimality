import DynamicOptimality.Funnel.Triangle
import Mathlib.Tactic.DeriveFintype

/-! # The bounded multiplicity of geometric funnel charges -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

private theorem base_apex_not_lt_left {word : Fin m → α} {active : Finset (Fin m)}
    {p q r p' r' : Fin m} (turn : Switch word active p q r)
    (turn' : Switch word active p' q r') (column : word r = word r')
    (left : word q < word p) (right : word p < word r) : ¬ p < p' := by
  intro pp'
  have left' : word q < word p' := by
    rcases turn'.2.2.2.1 with h | h
    · exact h.1
    · have rq : word r < word q := by simpa only [column] using h.1.trans h.2
      exact False.elim ((not_lt_of_ge (left.trans right).le) rq)
  have right' : word p' < word r := by
    rcases turn'.2.2.2.1 with h | h
    · simpa only [column] using h.2
    · exact False.elim ((not_lt_of_ge left'.le) h.2)
  have p'pKey : word p' < word p := by
    apply lt_of_not_ge
    intro h
    exact turn'.1.2.2.2.2 p turn.1.1 turn.1.2.2.1 pp' (Or.inl ⟨left.le,h⟩)
  rcases lt_trichotomy r' p with rp | rp | pr
  · apply turn'.2.1.2.2.2.2 p turn.1.1 rp pp'
    exact Or.inr ⟨p'pKey.le,by simpa only [← column] using right.le⟩
  · have same : word r = word p := column.trans (congrArg word rp)
    exact (ne_of_lt right) same.symm
  · have same := turn'.base_column turn.1.1 turn.1.2.2.1 pr
      (Or.inl ⟨left.le,by simpa only [← column] using right.le⟩)
    exact (ne_of_lt right) (same.trans column.symm)

/-- A fixed earlier base occurrence and a fixed later base column determine
at most one switch apex. This remains true when the column repeats. -/
theorem Switch.base_apex_unique {word : Fin m → α} {active : Finset (Fin m)}
    {p q r p' r' : Fin m} (turn : Switch word active p q r)
    (turn' : Switch word active p' q r') (column : word r = word r') : p = p' := by
  have notBefore : ¬ p < p' := by
    rcases turn.2.2.2.1 with h | h
    · exact base_apex_not_lt_left turn turn' column h.1 h.2
    · exact base_apex_not_lt_left (α := OrderDual α) turn.dual turn'.dual column h.2 h.1
  have notAfter : ¬ p' < p := by
    rcases turn'.2.2.2.1 with h | h
    · exact base_apex_not_lt_left turn' turn column.symm h.1 h.2
    · exact base_apex_not_lt_left (α := OrderDual α) turn'.dual turn.dual column.symm h.2 h.1
  exact le_antisymm (le_of_not_gt notAfter) (le_of_not_gt notBefore)

/-- The three charge slots: an edge at the apex can serve the earlier or
later funnel endpoint; an edge at the base has just one slot. -/
inductive ChargeSlot where
  | apexEarlier | apexLater | base
  deriving DecidableEq, Fintype

def FitsCharge (word : Fin m → α) (turn : Fin m × Fin m × Fin m)
    (edge : Fin m × Fin m) : ChargeSlot → Prop
  | .apexEarlier => edge.2 = turn.1 ∧ word edge.1 = word turn.2.1
  | .apexLater => edge.2 = turn.1 ∧ word edge.1 = word turn.2.2
  | .base => edge.1 = turn.2.1 ∧ word edge.2 = word turn.2.2

theorem charge_unique {word : Fin m → α} {active : Finset (Fin m)}
    {a b : Fin m × Fin m × Fin m} {edge : Fin m × Fin m} {slot : ChargeSlot}
    (ha : Switch word active a.1 a.2.1 a.2.2)
    (hb : Switch word active b.1 b.2.1 b.2.2)
    (fa : FitsCharge word a edge slot) (fb : FitsCharge word b edge slot) : a = b := by
  rcases a with ⟨p,q,r⟩
  rcases b with ⟨p',q',r'⟩
  cases slot with
  | apexEarlier =>
    obtain ⟨pe,qe⟩ := fa
    obtain ⟨pe',qe'⟩ := fb
    have pp' : p = p' := pe.symm.trans pe'
    subst p'
    have qq' : q = q' := ha.1.column_unique hb.1 (qe.symm.trans qe')
    subst q'
    have rr' : r = r' := ha.next_unique hb
    subst r'
    rfl
  | apexLater =>
    obtain ⟨pe,re⟩ := fa
    obtain ⟨pe',re'⟩ := fb
    have pp' : p = p' := pe.symm.trans pe'
    subst p'
    have rr' : r = r' := ha.2.1.column_unique hb.2.1 (re.symm.trans re')
    subst r'
    have qq' : q = q' := ha.prev_unique hb
    subst q'
    rfl
  | base =>
    obtain ⟨qe,re⟩ := fa
    obtain ⟨qe',re'⟩ := fb
    have qq' : q = q' := qe.symm.trans qe'
    subst q'
    have pp' : p = p' := ha.base_apex_unique hb (re.symm.trans re')
    subst p'
    have rr' : r = r' := ha.next_unique hb
    subst r'
    rfl

end DynamicOptimality.Funnel
