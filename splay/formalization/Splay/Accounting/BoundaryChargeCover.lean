import Splay.Accounting.ArticleSourceCredit

namespace Splay.Accounting

/-- A finite covering estimate counts occurrences and needs no injectivity
assumption: multiple covering sources only enlarge the right-hand side. -/
theorem length_le_filter_add_sum_filters {α β : Type*} (rows : List α) (sources : List β)
    (marked : α → Bool) (touches : β → α → Bool)
    (cover : ∀ row ∈ rows, marked row = true ∨ ∃ source ∈ sources, touches source row = true) :
    rows.length ≤ (rows.filter marked).length +
      (sources.map fun source => (rows.filter (touches source)).length).sum := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have tail := ih (fun next member => cover next (List.mem_cons_of_mem _ member))
    have pointwise : ∀ source,
        ((row :: rows).filter (touches source)).length =
          (if touches source row then 1 else 0) + (rows.filter (touches source)).length := by
      intro source
      by_cases selected : touches source row = true <;> simp [selected, Nat.add_comm]
    have sumEq : (sources.map fun source => ((row :: rows).filter (touches source)).length).sum =
        (sources.map fun source => if touches source row then 1 else 0).sum +
          (sources.map fun source => (rows.filter (touches source)).length).sum := by
      simp_rw [pointwise, List.sum_map_add]
    have headPaid : 1 ≤ (if marked row then 1 else 0) +
        (sources.map fun source => if touches source row then 1 else 0).sum := by
      rcases cover row List.mem_cons_self with selected | ⟨source, member, selected⟩
      · simp [selected]
      · have single : (if touches source row then 1 else 0) ≤
            (sources.map fun source => if touches source row then 1 else 0).sum :=
          List.le_sum_of_mem (List.mem_map.mpr ⟨source, member, rfl⟩)
        rw [if_pos selected] at single
        omega
    rw [sumEq]
    by_cases selected : marked row = true <;> simp [selected] at headPaid ⊢ <;> omega

/-- One admissible source either pays a unit of lifetime credit or performs
enough actual internal pairings to pay its at most four boundary losers. -/
theorem boundarySourceDemand_pays {n cutoff rows count : ℕ} {source : Splay.Lazy.Block n}
    (atMostFour : count ≤ 4) (nonempty : 0 < count → 0 < source.elements.length)
    (fraction : source.passCount = 0 ∨ source.elements.length ≤ 8 * rows) :
    cutoff * count ≤ 4 * cutoff * boundarySourceDemand cutoff source rows + 32 * rows := by
  by_cases noCount : count = 0
  · simp [noCount]
  have positive := nonempty (by omega)
  by_cases first : source.passCount = 0
  · simp [boundarySourceDemand, first]
    nlinarith [Nat.mul_le_mul_left cutoff atMostFour]
  have fraction := fraction.resolve_left first
  by_cases within : source.elements.length ≤ cutoff
  · simp [boundarySourceDemand, first, positive, within, fraction]
    nlinarith [Nat.mul_le_mul_left cutoff atMostFour]
  · have paid : cutoff * count ≤ 32 * rows := by
      nlinarith [Nat.mul_le_mul_left cutoff atMostFour]
    exact paid.trans (Nat.le_add_left _ _)

end Splay.Accounting
