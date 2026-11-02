import DynamicOptimality.Funnel.ChargeUniqueness

/-! # Every funnel switch has a monochromatic empty-edge charge -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

def colorClass (active : Finset (Fin m)) (color : Fin m → Bool) (c : Bool) :
    Finset (Fin m) := active.filter (fun p => color p = c)

def MonochromaticEdge (word : Fin m → α) (active : Finset (Fin m))
    (color : Fin m → Bool) (edge : Fin m × Fin m) : Prop :=
  color edge.1 = color edge.2 ∧
    Visible word (colorClass active color (color edge.2)) edge.2 edge.1

private theorem bool_eq_of_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem mono_of_visible {word : Fin m → α} {active : Finset (Fin m)}
    {color : Fin m → Bool} {p q : Fin m} (visible : Visible word active p q)
    (same : color q = color p) : MonochromaticEdge word active color (q,p) := by
  refine ⟨same,visible.restrict (Finset.filter_subset _ _) ?_ ?_⟩
  · exact Finset.mem_filter.mpr ⟨visible.1,rfl⟩
  · exact Finset.mem_filter.mpr ⟨visible.2.1,same⟩

/-- Repeated columns are handled by redirecting an apex charge to the last
occurrence of its color, or a base charge to the first occurrence on the
column. The charge always ends at an actual monochromatic empty rectangle. -/
theorem exists_charge {word : Fin m → α} {active : Finset (Fin m)}
    (color : Fin m → Bool) {p q r : Fin m} (turn : Switch word active p q r) :
    ∃ edge slot, MonochromaticEdge word active color edge ∧
      FitsCharge word (p,q,r) edge slot := by
  by_cases pq : color p = color q
  · exact ⟨(q,p),.apexEarlier,mono_of_visible turn.1 pq.symm,rfl,rfl⟩
  by_cases pr : color p = color r
  · exact ⟨(r,p),.apexLater,mono_of_visible turn.2.1 pr.symm,rfl,rfl⟩
  let column := active.filter (fun s => q < s ∧ s ≤ r ∧ word s = word r)
  have rMember : r ∈ column := Finset.mem_filter.mpr
    ⟨turn.2.1.2.1,turn.2.2.1,le_rfl,rfl⟩
  let sameColor := column.filter (fun s => color s = color p)
  by_cases existsSame : sameColor.Nonempty
  · let s := sameColor.max' existsSame
    have sMember : s ∈ sameColor := Finset.max'_mem _ _
    obtain ⟨sColumn,sColor⟩ := Finset.mem_filter.mp sMember
    obtain ⟨sActive,qs,sr,sKey⟩ := Finset.mem_filter.mp sColumn
    have sp : s < p := sr.trans_lt turn.2.1.2.2.1
    have sVisible : Visible word (colorClass active color (color p)) p s := by
      refine ⟨Finset.mem_filter.mpr ⟨turn.1.1,rfl⟩,
        Finset.mem_filter.mpr ⟨sActive,sColor⟩,sp,?_,?_⟩
      · simpa only [sKey] using turn.2.1.2.2.2.1
      · intro t ht st tp keys
        obtain ⟨tActive,tColor⟩ := Finset.mem_filter.mp ht
        have keys' : Between (word r) (word p) (word t) := by simpa only [sKey] using keys
        by_cases tr : t ≤ r
        · have tKey : word t = word r := by
            rcases lt_or_eq_of_le tr with tr | tr
            · exact turn.base_column tActive (qs.trans st) tr
                ((between_right (word q) (word r)).trans turn.2.2.2.1.between keys')
            · exact congrArg word tr
          have tMember : t ∈ sameColor := Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨tActive,qs.trans st,tr,tKey⟩,tColor⟩
          exact (not_lt_of_ge (Finset.le_max' sameColor t tMember)) st
        · exact turn.2.1.2.2.2.2 t tActive (lt_of_not_ge tr) tp keys'
    exact ⟨(s,p),.apexLater,⟨sColor,sVisible⟩,rfl,sKey⟩
  · let s := column.min' ⟨r,rMember⟩
    have sColumn : s ∈ column := Finset.min'_mem _ _
    obtain ⟨sActive,qs,sr,sKey⟩ := Finset.mem_filter.mp sColumn
    have sNotP : color s ≠ color p := by
      intro h
      exact existsSame ⟨s,Finset.mem_filter.mpr ⟨sColumn,h⟩⟩
    have same : color q = color s := bool_eq_of_ne (Ne.symm pq) sNotP
    have sVisible : Visible word active s q := by
      refine ⟨sActive,turn.1.2.1,qs,?_,?_⟩
      · simpa only [sKey] using turn.2.2.2.1.ne
      · intro t ht qt ts keys
        have tr : t < r := ts.trans_le sr
        have tKey : word t = word r := turn.base_column ht qt tr (by simpa only [sKey] using keys)
        have member : t ∈ column := Finset.mem_filter.mpr ⟨ht,qt,tr.le,tKey⟩
        exact (not_lt_of_ge (Finset.min'_le column t member)) ts
    exact ⟨(q,s),.base,mono_of_visible sVisible same,rfl,sKey⟩

end DynamicOptimality.Funnel
