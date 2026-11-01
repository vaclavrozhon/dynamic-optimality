import Mathlib

/-!
The creator variation event at time t separates entries joined by t from
entries joined later. A monotone (or reversed) historical join order on a
finite key set realizes that separation by one ordinary inorder key cut.
The set can contain arbitrary deletion holes. This is the missing order
translation between timestamp histories and geometric Cartesian cuts.
-/
namespace GreedyForest.HistoricalCuts

def KeyCrosses (cut a b : ℕ) : Prop :=
  (a < cut ∧ cut ≤ b) ∨ (b < cut ∧ cut ≤ a)

instance (cut a b : ℕ) : Decidable (KeyCrosses cut a b) :=
  inferInstanceAs (Decidable ((a < cut ∧ cut ≤ b) ∨ (b < cut ∧ cut ≤ a)))

def TimeCrosses (time a b : ℕ) : Prop := min a b ≤ time ∧ time < max a b

instance (time a b : ℕ) : Decidable (TimeCrosses time a b) :=
  inferInstanceAs (Decidable (min a b ≤ time ∧ time < max a b))

/-- The event interval uses cut t+1 on integer join times. -/
theorem time_crosses_iff_integer_cut (time a b : ℕ) :
    TimeCrosses time a b ↔ KeyCrosses (time+1) a b := by
  unfold TimeCrosses KeyCrosses
  omega

theorem monotone_join_key_cut (keys : Finset ℕ) (join : ℕ → ℕ) (time : ℕ)
    (hmono : ∀ a ∈ keys, ∀ b ∈ keys, a ≤ b → join a ≤ join b) :
    ∃ cut, ∀ v ∈ keys, join v ≤ time ↔ v < cut := by
  let early := keys.filter (fun v => join v ≤ time)
  by_cases he : early.Nonempty
  · let last := early.max' he
    have hlast : last ∈ early := early.max'_mem he
    have hlast' : last ∈ keys ∧ join last ≤ time := Finset.mem_filter.mp hlast
    refine ⟨last+1, ?_⟩
    intro v hv
    constructor
    · intro hj
      have hearly : v ∈ early := Finset.mem_filter.mpr ⟨hv,hj⟩
      have hle : v ≤ last := early.le_max' v hearly
      omega
    · intro hkey
      have hle : v ≤ last := by omega
      exact (hmono v hv last hlast'.1 hle).trans hlast'.2
  · refine ⟨0, ?_⟩
    intro v hv
    constructor
    · intro hj
      exact (he ⟨v, Finset.mem_filter.mpr ⟨hv,hj⟩⟩).elim
    · omega

theorem antitone_join_key_cut (keys : Finset ℕ) (join : ℕ → ℕ) (time : ℕ)
    (hanti : ∀ a ∈ keys, ∀ b ∈ keys, a ≤ b → join b ≤ join a) :
    ∃ cut, ∀ v ∈ keys, join v ≤ time ↔ cut ≤ v := by
  let early := keys.filter (fun v => join v ≤ time)
  by_cases he : early.Nonempty
  · let first := early.min' he
    have hfirst : first ∈ early := early.min'_mem he
    have hfirst' : first ∈ keys ∧ join first ≤ time := Finset.mem_filter.mp hfirst
    refine ⟨first, ?_⟩
    intro v hv
    constructor
    · intro hj
      have hearly : v ∈ early := Finset.mem_filter.mpr ⟨hv,hj⟩
      exact early.min'_le v hearly
    · intro hkey
      exact (hanti first hfirst'.1 v hv hkey).trans hfirst'.2
  · let cut := keys.sup id + 1
    refine ⟨cut, ?_⟩
    intro v hv
    have hvbound : v ≤ keys.sup id := Finset.le_sup (f:=id) hv
    constructor
    · intro hj
      exact (he ⟨v, Finset.mem_filter.mpr ⟨hv,hj⟩⟩).elim
    · dsimp only [cut]
      omega

theorem time_crosses_iff_key_crosses {join : ℕ → ℕ} {time cut a b : ℕ}
    (ha : join a ≤ time ↔ a < cut) (hb : join b ≤ time ↔ b < cut) :
    TimeCrosses time (join a) (join b) ↔ KeyCrosses cut a b := by
  unfold TimeCrosses KeyCrosses
  omega

theorem time_crosses_iff_key_crosses_reversed {join : ℕ → ℕ} {time cut a b : ℕ}
    (ha : join a ≤ time ↔ cut ≤ a) (hb : join b ≤ time ↔ cut ≤ b) :
    TimeCrosses time (join a) (join b) ↔ KeyCrosses cut a b := by
  unfold TimeCrosses KeyCrosses
  omega

/-- One cut works for every pair of records in the historical family,
including pairs in different split descendants or with holes between
their key positions. Splits need only preserve the historical order. -/
theorem ordered_join_crossings_have_one_key_cut
    (keys : Finset ℕ) (join : ℕ → ℕ) (time : ℕ)
    (horder :
      (∀ a ∈ keys, ∀ b ∈ keys, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ keys, ∀ b ∈ keys, a ≤ b → join b ≤ join a)) :
    ∃ cut, ∀ a ∈ keys, ∀ b ∈ keys,
      TimeCrosses time (join a) (join b) ↔ KeyCrosses cut a b := by
  rcases horder with hm | ha
  · obtain ⟨cut,hc⟩ := monotone_join_key_cut keys join time hm
    exact ⟨cut, fun a hka b hkb => time_crosses_iff_key_crosses (hc a hka) (hc b hkb)⟩
  · obtain ⟨cut,hc⟩ := antitone_join_key_cut keys join time ha
    exact ⟨cut, fun a hka b hkb => time_crosses_iff_key_crosses_reversed (hc a hka) (hc b hkb)⟩

end GreedyForest.HistoricalCuts
