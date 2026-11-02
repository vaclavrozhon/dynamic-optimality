import DynamicOptimality.Funnel.ChargeExistence

/-!
# Two-color funnel switches are paid by source visibility edges

The bound concerns source *edges*, rather than source funnel switches.
Repeated columns and overlapping source alphabets are both permitted.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

private theorem mono_iff {word : Fin m → α} {active : Finset (Fin m)}
    {color : Fin m → Bool} {edge : Fin m × Fin m} :
    MonochromaticEdge word active color edge ↔
      Visible word (colorClass active color false) edge.2 edge.1 ∨
      Visible word (colorClass active color true) edge.2 edge.1 := by
  constructor
  · rintro ⟨same,visible⟩
    cases h : color edge.2
    · exact Or.inl (by simpa only [h] using visible)
    · exact Or.inr (by simpa only [h] using visible)
  · intro visible
    rcases visible with visible | visible
    all_goals
      have later := (Finset.mem_filter.mp visible.1).2
      have earlier := (Finset.mem_filter.mp visible.2.1).2
      exact ⟨earlier.trans later.symm,by simpa only [later] using visible⟩

theorem two_color_visibility_charge (word : Fin m → α)
    (active : Finset (Fin m)) (color : Fin m → Bool) :
    count word active ≤ 3 *
      (edgeCount word (colorClass active color false) +
       edgeCount word (colorClass active color true)) := by
  classical
  let monoEdges := (edges word (colorClass active color false)) ∪
    (edges word (colorClass active color true))
  have monoMember : ∀ edge, edge ∈ monoEdges ↔ MonochromaticEdge word active color edge := by
    rintro ⟨q,p⟩
    simp only [monoEdges,Finset.mem_union,mem_edges,mono_iff]
  have witnesses : ∀ t : { t // t ∈ switches word active },
      ∃ edge : { edge // edge ∈ monoEdges }, ∃ slot : ChargeSlot,
        FitsCharge word t.val edge.val slot := by
    intro t
    obtain ⟨edge,slot,mono,fits⟩ := exists_charge color (mem_switches.mp t.property)
    exact ⟨⟨edge,(monoMember edge).mpr mono⟩,slot,fits⟩
  choose edge slot fits using witnesses
  let encode (t : { t // t ∈ switches word active }) := (edge t,slot t)
  have injective : Function.Injective encode := by
    intro a b same
    have edgesEqual : edge a = edge b := congrArg Prod.fst same
    have slotsEqual : slot a = slot b := congrArg Prod.snd same
    apply Subtype.ext
    apply charge_unique (mem_switches.mp a.property) (mem_switches.mp b.property) (fits a)
    simpa only [edgesEqual,slotsEqual] using fits b
  have cardBound := Fintype.card_le_of_injective encode injective
  have slotCard : Fintype.card ChargeSlot = 3 := by decide
  have disjoint : Disjoint (edges word (colorClass active color false))
      (edges word (colorClass active color true)) := by
    apply Finset.disjoint_left.mpr
    intro edge hfalse htrue
    have hf := (Finset.mem_filter.mp (mem_edges.mp hfalse).1).2
    have ht := (Finset.mem_filter.mp (mem_edges.mp htrue).1).2
    exact Bool.false_ne_true (hf.symm.trans ht)
  simpa only [count,Fintype.card_prod,Fintype.card_coe,slotCard,
    monoEdges,Finset.card_union_of_disjoint disjoint,Nat.mul_comm,edgeCount] using cardBound

/-- The two-source convention includes every occurrence in exactly one
source; key alphabets need not be disjoint. -/
theorem word_two_color_visibility_charge (word : List α)
    (color : Fin word.length → Bool) :
    wordCount word ≤ 3 *
      (edgeCount word.get (colorClass Finset.univ color false) +
       edgeCount word.get (colorClass Finset.univ color true)) :=
  two_color_visibility_charge word.get Finset.univ color

end DynamicOptimality.Funnel
