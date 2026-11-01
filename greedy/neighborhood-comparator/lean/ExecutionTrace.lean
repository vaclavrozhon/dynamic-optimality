import ForestLedger
import BlockLifetime

/-!
Finite execution traces for the complete-consolidation accounting theorem.
The trace interface records local operations, membership snapshots, and
block-family histories. It does not assume the final shift inequalities.
-/
namespace GreedyForest.Execution

open scoped BigOperators

variable {Record Edge : Type*} [Fintype Record] [DecidableEq Record]

/-- A chronological membership entry. `none` is an exceptional entry;
`some e` is the membership created by internal bad link e. -/
structure EntryEvent (Record Edge : Type*) where
  record : Record
  creatorLabel : ℤ
  badEdge : Option Edge

def entryBadEdges : List (EntryEvent Record Edge) → List Edge
  | [] => []
  | row :: rest => row.badEdge.toList ++ entryBadEdges rest

def entryExceptions : List (EntryEvent Record Edge) → ℕ
  | [] => 0
  | row :: rest => (if row.badEdge.isNone then 1 else 0) + entryExceptions rest

def creatorMemoryPotential (K : ℤ) (current : Record → ℤ) : ℤ :=
  ∑ v, (K - current v)

theorem creatorMemory_update (K : ℤ) (current : Record → ℤ) (v : Record) (next : ℤ) :
    creatorMemoryPotential K (Function.update current v next) =
      creatorMemoryPotential K current + current v - next := by
  have hpoint : ∀ w, K - Function.update current v next w =
      (K - current w) + if w = v then current v - next else 0 := by
    intro w
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  unfold creatorMemoryPotential
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- Local snapshot consistency: an internal bad entry's loser shift is
the new creator snapshot minus this record's previous creator snapshot.
The recursive update is the actual membership-entry history. -/
def ValidEntryLedger (K : ℤ) (loserShift : Edge → ℤ) (current : Record → ℤ) :
    List (EntryEvent Record Edge) → Prop
  | [] => True
  | row :: rest =>
      (1 ≤ row.creatorLabel ∧ row.creatorLabel ≤ K) ∧
      (∀ e, row.badEdge = some e → loserShift e = row.creatorLabel - current row.record) ∧
      ValidEntryLedger K loserShift (Function.update current row.record row.creatorLabel) rest

theorem entry_loser_bound_remaining (K : ℤ) (loserShift : Edge → ℤ)
    (current : Record → ℤ) (rows : List (EntryEvent Record Edge))
    (hcurrent : ∀ v, 1 ≤ current v ∧ current v ≤ K)
    (hvalid : ValidEntryLedger K loserShift current rows) :
    ((entryBadEdges rows).map loserShift).sum ≤
      creatorMemoryPotential K current + (entryExceptions rows : ℤ) * (K - 1) := by
  induction rows generalizing current with
  | nil =>
      simp only [entryBadEdges, List.map_nil, List.sum_nil, entryExceptions,
        Nat.cast_zero, zero_mul, add_zero]
      unfold creatorMemoryPotential
      exact Finset.sum_nonneg (fun v _ => by have h := (hcurrent v).2; omega)
  | cons row rest ih =>
      rcases hvalid with ⟨hlabel, hmatch, htail⟩
      have hnext : ∀ v, 1 ≤ Function.update current row.record row.creatorLabel v ∧
          Function.update current row.record row.creatorLabel v ≤ K := by
        intro v
        by_cases hv : v = row.record
        · subst v
          simpa using hlabel
        · simpa [Function.update_apply, hv, Ne.symm hv] using hcurrent v
      have hr := ih (Function.update current row.record row.creatorLabel) hnext htail
      rw [creatorMemory_update] at hr
      cases he : row.badEdge with
      | none =>
          simp only [entryBadEdges, he, Option.toList_none, List.nil_append,
            entryExceptions, Option.isNone_none, ↓reduceIte, Nat.cast_add, Nat.cast_one]
          have hc := hcurrent row.record
          nlinarith
      | some e =>
          have hm := hmatch e he
          simp only [entryBadEdges, he, Option.toList_some, List.singleton_append,
            List.map_cons, List.sum_cons, entryExceptions, Option.isNone_some,
            Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          nlinarith

/-- Start with no unpaid creator memory. Every first membership is an
ordinary exceptional entry in the application. Arbitrary interleaving of
different records is handled by the single chronological trace. -/
theorem entry_loser_bound (K : ℤ) (loserShift : Edge → ℤ)
    (rows : List (EntryEvent Record Edge)) (hK : 1 ≤ K)
    (hvalid : ValidEntryLedger K loserShift (fun _ => K) rows) :
    ((entryBadEdges rows).map loserShift).sum ≤
      (entryExceptions rows : ℤ) * (K - 1) := by
  have h := entry_loser_bound_remaining K loserShift (fun _ => K) rows
    (fun _ => ⟨hK, le_refl K⟩) hvalid
  simpa [creatorMemoryPotential] using h

theorem sum_map_full_census {A : Type*} [Fintype A] [DecidableEq A]
    (rows : List A) (w : A → ℤ) (hnodup : rows.Nodup)
    (hcomplete : ∀ a, a ∈ rows) : (rows.map w).sum = ∑ a, w a := by
  have hu : rows.toFinset = Finset.univ := by
    ext a
    simp [hcomplete a]
  rw [← List.sum_toFinset w hnodup, hu]

omit [Fintype Record] [DecidableEq Record] in
theorem entry_exception_census {A : Type*} [Fintype A] [DecidableEq A]
    (order : List A) (row : A → EntryEvent Record Edge)
    (hnodup : order.Nodup) (hcomplete : ∀ a, a ∈ order) :
    (entryExceptions (order.map row) : ℤ) =
      ∑ a, (if (row a).badEdge.isNone then (1 : ℤ) else 0) := by
  have hlist : (entryExceptions (order.map row) : ℤ) =
      (order.map (fun a => if (row a).badEdge.isNone then (1 : ℤ) else 0)).sum := by
    clear hnodup hcomplete
    induction order with
    | nil => simp [entryExceptions]
    | cons a rest ih =>
        cases he : (row a).badEdge <;>
          simp [entryExceptions, he, ih]
  rw [hlist]
  exact sum_map_full_census order _ hnodup hcomplete

/-- An injective charging map to nonnegative event capacities. This
converts local one-unit drops and explicit exception slots to a count. -/
theorem card_le_sum_of_injective_charge {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (charge : A → B) (weight : B → ℤ)
    (hinj : Function.Injective charge) (hweight : ∀ b, 0 ≤ weight b)
    (hunit : ∀ a, 1 ≤ weight (charge a)) :
    (Fintype.card A : ℤ) ≤ ∑ b, weight b := by
  classical
  calc
    (Fintype.card A : ℤ) = ∑ _a : A, (1 : ℤ) := by simp
    _ ≤ ∑ a, weight (charge a) := Finset.sum_le_sum (fun a _ => hunit a)
    _ = ∑ b ∈ Finset.univ.image charge, weight b := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj hab
    _ ≤ ∑ b, weight b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hweight b)

/-- Positive changes have explicit lifetime slots: four per created
block, plus one per paid administrative label update. -/
theorem positive_variation_slots {Cell Block Paid : Type*}
    [Fintype Cell] [Fintype Block] [Fintype Paid]
    (delta : Cell → ℤ) (K : ℤ) (hK : 1 ≤ K)
    (hbound : ∀ c, delta c ≤ K - 1)
    (charge : {c // 0 < delta c} → Sum (Block × Fin 4) Paid)
    (hinj : Function.Injective charge) :
    ∑ c, max 0 (delta c) ≤
      4 * (Fintype.card Block : ℤ) * (K - 1) + (Fintype.card Paid : ℤ) * K := by
  classical
  have hcard := Fintype.card_le_of_injective charge hinj
  have hcard' : ((Finset.univ.filter (fun c => 0 < delta c)).card : ℤ) ≤
      4 * (Fintype.card Block : ℤ) + (Fintype.card Paid : ℤ) := by
    have hcast : (Fintype.card {c // 0 < delta c} : ℤ) ≤
        (Fintype.card (Sum (Block × Fin 4) Paid) : ℤ) := by exact_mod_cast hcard
    simpa [Fintype.card_subtype, Fintype.card_sum, Fintype.card_prod, mul_comm] using hcast
  have hpoint : ∀ c, max 0 (delta c) ≤ if 0 < delta c then K - 1 else 0 := by
    intro c
    by_cases hc : 0 < delta c
    · simp only [if_pos hc, max_eq_right (le_of_lt hc)]
      exact hbound c
    · simp only [if_neg hc]
      exact max_le (le_refl 0) (by omega)
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hpoint c)
  have hid : (∑ c, if 0 < delta c then K - 1 else 0) =
      ((Finset.univ.filter (fun c => 0 < delta c)).card : ℤ) * (K - 1) := by
    rw [← Finset.sum_filter]
    simp
    ring
  rw [hid] at hsum
  have hmul := mul_le_mul_of_nonneg_right hcard' (show 0 ≤ K - 1 by omega)
  have hp : 0 ≤ (Fintype.card Paid : ℤ) := by positivity
  nlinarith

theorem negative_variation_slots {Cell Good : Type*} [Fintype Cell] [Fintype Good]
    [DecidableEq Cell] (delta : Cell → ℤ) (charge : Good → Cell)
    (hinj : Function.Injective charge) (hdrop : ∀ e, delta (charge e) ≤ -1) :
    (Fintype.card Good : ℤ) ≤ ∑ c, max 0 (-delta c) := by
  apply card_le_sum_of_injective_charge charge (fun c => max 0 (-delta c)) hinj
  · intro c
    exact le_max_left _ _
  · intro e
    have h := hdrop e
    have hm := le_max_right (0 : ℤ) (-delta (charge e))
    omega

/-- Each boundary link is either an actual dropping event or consumes
one of the explicitly bounded exception slots of its loser's old block. -/
theorem boundary_variation_slots {Cell Block Boundary : Type*}
    [Fintype Cell] [Fintype Block] [Fintype Boundary]
    [DecidableEq Cell] [DecidableEq Block]
    (delta : Cell → ℤ) (k : ℕ)
    (charge : Boundary → Sum Cell (Block × Fin (2*k+4)))
    (hinj : Function.Injective charge)
    (hdrop : ∀ e c, charge e = Sum.inl c → delta c ≤ -1) :
    (Fintype.card Boundary : ℤ) ≤
      (∑ c, max 0 (-delta c)) + (2*(k:ℤ)+4) * (Fintype.card Block : ℤ) := by
  classical
  let weight : Sum Cell (Block × Fin (2*k+4)) → ℤ :=
    Sum.elim (fun c => max 0 (-delta c)) (fun _ => 1)
  have hn : ∀ x, 0 ≤ weight x := by
    intro x
    cases x with
    | inl c => exact le_max_left _ _
    | inr b => norm_num [weight]
  have hu : ∀ e, 1 ≤ weight (charge e) := by
    intro e
    cases he : charge e with
    | inl c =>
        have hd := hdrop e c he
        have hm := le_max_right (0 : ℤ) (-delta c)
        simp only [weight, Sum.elim_inl]
        omega
    | inr b => simp [weight]
  have h := card_le_sum_of_injective_charge charge weight hinj hn hu
  simpa [weight, Fintype.sum_sum_type, mul_comm] using h

theorem sum_by_fibers {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (owner : A → B) (weight : B → ℤ) :
    ∑ a, weight (owner a) =
      ∑ b, ((Finset.univ.filter (fun a => owner a = b)).card : ℤ) * weight b := by
  classical
  calc
    ∑ a, weight (owner a) = ∑ a, ∑ b, if owner a = b then weight b else 0 := by simp
    _ = ∑ b, ∑ a, if owner a = b then weight b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_filter]
      simp

/-- Bounded local winner capacity controls multiplicity of arbitrary
nonnegative entry deficits attached to those memberships. -/
theorem sum_comp_le_capacity {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (owner : A → B) (weight : B → ℤ) (D : ℕ)
    (hweight : ∀ b, 0 ≤ weight b)
    (hcapacity : ∀ b, (Finset.univ.filter (fun a => owner a = b)).card ≤ D) :
    ∑ a, weight (owner a) ≤ (D : ℤ) * ∑ b, weight b := by
  rw [sum_by_fibers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hc : ((Finset.univ.filter (fun a => owner a = b)).card : ℤ) ≤ (D : ℤ) := by
    exact_mod_cast hcapacity b
  exact mul_le_mul_of_nonneg_right hc (hweight b)

theorem bad_activity_from_entries {Bad Member : Type*}
    [Fintype Bad] [Fintype Member] [DecidableEq Member]
    (winnerEntry : Bad → Member) (memberLabel creatorLabel : Member → ℤ)
    (exceptional : Member → Bool) (K : ℤ) (D : ℕ) (hK : 1 ≤ K)
    (hlabels : ∀ m, 1 ≤ memberLabel m ∧ creatorLabel m ≤ K)
    (hstrict : ∀ m, exceptional m = false → creatorLabel m + 1 ≤ memberLabel m)
    (hcapacity : ∀ m, (Finset.univ.filter (fun e => winnerEntry e = m)).card ≤ D) :
    (Fintype.card Bad : ℤ) ≤
      (∑ e : Bad, (memberLabel (winnerEntry e) - creatorLabel (winnerEntry e))) +
      (D : ℤ) * K * ∑ m, (if exceptional m then (1 : ℤ) else 0) := by
  classical
  have hpoint : ∀ e, (1 : ℤ) ≤
      memberLabel (winnerEntry e) - creatorLabel (winnerEntry e) +
      entryDeficit (memberLabel (winnerEntry e)) (creatorLabel (winnerEntry e)) :=
    fun e => entryRank_add_deficit _ _
  have ha := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hpoint e)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_add_distrib] at ha
  have hmult := sum_comp_le_capacity winnerEntry
    (fun m => entryDeficit (memberLabel m) (creatorLabel m)) D
    (fun m => entryDeficit_nonneg _ _) hcapacity
  have hd : ∑ m, entryDeficit (memberLabel m) (creatorLabel m) ≤
      K * ∑ m, (if exceptional m then (1 : ℤ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    cases he : exceptional m
    · have hz := entryDeficit_eq_zero_of_strict _ _ (hstrict m he)
      simp [hz]
    · have hb := entryDeficit_le_bound K _ _ hK (hlabels m).1 (hlabels m).2
      simpa [he] using hb
  have hdm := mul_le_mul_of_nonneg_left hd (show 0 ≤ (D : ℤ) by positivity)
  nlinarith

/-- The single-creator multiplicity lemma with an explicit selected
set of families. This permits a global finite trace with many creators. -/
theorem selected_join_multiplicity {Block Bad : Type*}
    [Fintype Block] [Fintype Bad] [DecidableEq Block]
    (family : Bad → Block) (selected : Block → Bool) (start finish : Block → ℕ)
    (winnerJoin loserJoin : Bad → ℕ) (time : ℕ) (C M : ℤ)
    (hM : 0 ≤ M)
    (hjoins : ∀ e,
      (start (family e) ≤ winnerJoin e ∧ winnerJoin e ≤ finish (family e)) ∧
      (start (family e) ≤ loserJoin e ∧ loserJoin e ≤ finish (family e)))
    (hlocal : ∀ b,
      ∑ e, (if family e = b ∧
        min (winnerJoin e) (loserJoin e) ≤ time ∧
          time < max (winnerJoin e) (loserJoin e) then (1 : ℤ) else 0) ≤ M)
    (hoverlap : ∑ b,
      (if selected b ∧ start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) ≤ C) :
    ∑ e, (if selected (family e) then
      |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0) ≤ C * M := by
  classical
  let mass : Block → ℤ := fun b =>
    ∑ e, if family e = b then |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0
  have hsum : ∑ b, (if selected b then mass b else 0) =
      ∑ e, (if selected (family e) then
        |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0) := by
    have hdist : ∀ b, (if selected b then mass b else 0) =
        ∑ e, (if selected b then
          if family e = b then |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0
          else 0) := by
      intro b
      by_cases hs : selected b <;> simp [mass, hs]
    simp_rw [hdist]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    have hid : ∀ b, (if selected b then
        if family e = b then |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0
        else 0) =
          if family e = b then
            (if selected (family e) then |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0)
          else 0 := by
      intro b
      by_cases hb : family e = b
      · subst b
        simp
      · simp [hb]
    simp_rw [hid]
    simp
  have hmass : ∀ b, (if selected b then mass b else 0) ≤
      (if selected b ∧ start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * M := by
    intro b
    by_cases hs : selected b
    · by_cases hactive : start b ≤ time ∧ time < finish b
      · have heq : mass b = ∑ e, (if family e = b ∧
            min (winnerJoin e) (loserJoin e) ≤ time ∧
              time < max (winnerJoin e) (loserJoin e) then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [joinCoefficient_abs]
          by_cases hf : family e = b <;> simp [hf]
        simpa [hs, hactive, heq] using hlocal b
      · have hz : mass b = 0 := by
          apply Finset.sum_eq_zero
          intro e he
          by_cases hf : family e = b
          · have hj := hjoins e
            have hzero := joinCoefficient_zero_outside_growth
              (start b) (finish b) (winnerJoin e) (loserJoin e) time
              (by simpa [hf] using hj.1) (by simpa [hf] using hj.2) hactive
            simp [hf, hzero]
          · simp [hf]
        simp [hs, hactive, hz]
    · simp [hs]
  rw [← hsum]
  calc
    _ ≤ ∑ b, (if selected b ∧ start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * M :=
      Finset.sum_le_sum (fun b _ => hmass b)
    _ = (∑ b, if selected b ∧ start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * M := by
      rw [Finset.sum_mul]
    _ ≤ C * M := mul_le_mul_of_nonneg_right hoverlap hM

def labelDelta (T : ℕ) (label : Record → ℕ → ℤ) (cell : Record × Fin T) : ℤ :=
  label cell.1 (cell.2.val + 1) - label cell.1 cell.2.val

omit [DecidableEq Record] in
theorem finite_label_variation_balance (T : ℕ) (label : Record → ℕ → ℤ) (K : ℤ)
    (hstart : ∀ v, label v 0 ≤ K) (hend : ∀ v, 1 ≤ label v T) :
    (∑ cell : Record × Fin T, max 0 (-labelDelta T label cell)) ≤
      (Fintype.card Record : ℤ) * (K - 1) +
      ∑ cell : Record × Fin T, max 0 (labelDelta T label cell) := by
  have hlocal : ∀ v,
      negativeVariation (label v) T ≤ (K - 1) + positiveVariation (label v) T := by
    intro v
    have h := negativeVariation_le_positive (label v) T 1 K
      (by simpa using hstart v) (hend v)
    simpa using h
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hlocal v)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  have hn : ∀ v, (∑ t : Fin T, max 0 (label v t.val - label v (t.val+1))) =
      negativeVariation (label v) T := by
    intro v
    exact Fin.sum_univ_eq_sum_range (fun t => max 0 (label v t - label v (t+1))) T
  have hp : ∀ v, (∑ t : Fin T, max 0 (label v (t.val+1) - label v t.val)) =
      positiveVariation (label v) T := by
    intro v
    exact Fin.sum_univ_eq_sum_range (fun t => max 0 (label v (t+1) - label v t)) T
  simp only [labelDelta, Fintype.sum_prod_type, neg_sub]
  simp_rw [hn, hp]
  exact hs

/-- Signed historical intervals may belong to different records. Local
event coverage is derived per record; this lemma performs only the exact
finite double counting and the absolute-value inequality. -/
theorem channel_signed_coverage {Time : Type*} [Fintype Edge] [Fintype Time]
    (channel : Edge → Record) (coefficient : Edge → Time → ℤ)
    (delta : Record → Time → ℤ) (M : ℤ)
    (hmult : ∀ v t, ∑ e, (if channel e = v then |coefficient e t| else 0) ≤ M) :
    ∑ e, ∑ t, coefficient e t * delta (channel e) t ≤
      M * ∑ v, ∑ t, |delta v t| := by
  classical
  have hexpand : (∑ e, ∑ t, coefficient e t * delta (channel e) t) =
      ∑ v, ∑ t, ∑ e, if channel e = v then coefficient e t * delta v t else 0 := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    simp
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    ∑ e, (if channel e = v then coefficient e t * delta v t else 0) ≤
        ∑ e, (if channel e = v then |coefficient e t| * |delta v t| else 0) := by
      apply Finset.sum_le_sum
      intro e he
      by_cases hc : channel e = v
      · simp only [if_pos hc]
        calc
          _ ≤ |coefficient e t * delta v t| := le_abs_self _
          _ = _ := abs_mul _ _
      · simp [hc]
    _ = (∑ e, if channel e = v then |coefficient e t| else 0) * |delta v t| := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ ≤ M * |delta v t| := mul_le_mul_of_nonneg_right (hmult v t) (abs_nonneg _)

theorem channel_winner_coverage {Time : Type*} [Fintype Edge] [Fintype Time]
    (channel : Edge → Record) (coefficient : Edge → Time → ℤ)
    (delta : Record → Time → ℤ) (D : ℤ)
    (hnonneg : ∀ e t, 0 ≤ coefficient e t)
    (hmult : ∀ v t, ∑ e, (if channel e = v then coefficient e t else 0) ≤ D) :
    ∑ e, ∑ t, coefficient e t * (-delta (channel e) t) ≤
      D * ∑ v, ∑ t, max 0 (-delta v t) := by
  classical
  have hexpand : (∑ e, ∑ t, coefficient e t * (-delta (channel e) t)) =
      ∑ v, ∑ t, ∑ e, if channel e = v then coefficient e t * (-delta v t) else 0 := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    simp
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have hn : 0 ≤ ∑ e, (if channel e = v then coefficient e t else 0) := by
    apply Finset.sum_nonneg
    intro e he
    split_ifs
    · exact hnonneg e t
    · rfl
  have hid : (∑ e, if channel e = v then coefficient e t * (-delta v t) else 0) =
      (∑ e, if channel e = v then coefficient e t else 0) * (-delta v t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  rw [hid]
  calc
    _ ≤ (∑ e, if channel e = v then coefficient e t else 0) * max 0 (-delta v t) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hn
    _ ≤ D * max 0 (-delta v t) :=
      mul_le_mul_of_nonneg_right (hmult v t) (le_max_left _ _)

theorem global_creator_shift_bound {Block : Type*}
    [Fintype Block] [DecidableEq Block] [Fintype Edge]
    (family : Edge → Block) (creator : Block → Record) (start finish : Block → ℕ)
    (winnerJoin loserJoin : Edge → ℕ) (label : Record → ℕ → ℤ)
    (T : ℕ) (C M : ℤ) (hM : 0 ≤ M) (hfinish : ∀ b, finish b ≤ T)
    (hjoins : ∀ e,
      (start (family e) ≤ winnerJoin e ∧ winnerJoin e ≤ finish (family e)) ∧
      (start (family e) ≤ loserJoin e ∧ loserJoin e ≤ finish (family e)))
    (hlocal : ∀ b t,
      ∑ e, (if family e = b ∧
        min (winnerJoin e) (loserJoin e) ≤ t ∧
          t < max (winnerJoin e) (loserJoin e) then (1 : ℤ) else 0) ≤ M)
    (hoverlap : ∀ v t,
      ∑ b, (if creator b = v ∧ start b ≤ t ∧ t < finish b then (1 : ℤ) else 0) ≤ C) :
    ∑ e, (label (creator (family e)) (loserJoin e) -
      label (creator (family e)) (winnerJoin e)) ≤
        C * M * ∑ cell : Record × Fin T, |labelDelta T label cell| := by
  classical
  have hmult : ∀ v (t : Fin T),
      ∑ e, (if creator (family e) = v then
        |joinCoefficient (winnerJoin e) (loserJoin e) t.val| else 0) ≤ C * M := by
    intro v t
    have h := selected_join_multiplicity family (fun b => decide (creator b = v))
      start finish winnerJoin loserJoin t.val C M hM hjoins
      (fun b => hlocal b t.val) (by simpa using hoverlap v t.val)
    simpa using h
  have h := channel_signed_coverage (fun e => creator (family e))
    (fun e (t : Fin T) => joinCoefficient (winnerJoin e) (loserJoin e) t.val)
    (fun v (t : Fin T) => labelDelta T label (v,t)) (C*M) hmult
  have hexpand : ∀ e,
      (∑ t : Fin T, joinCoefficient (winnerJoin e) (loserJoin e) t.val *
        labelDelta T label (creator (family e),t)) =
          label (creator (family e)) (loserJoin e) -
            label (creator (family e)) (winnerJoin e) := by
    intro e
    simp only [labelDelta]
    rw [Fin.sum_univ_eq_sum_range (fun t => joinCoefficient (winnerJoin e) (loserJoin e) t *
      (label (creator (family e)) (t+1) - label (creator (family e)) t)) T]
    exact joinCoefficient_telescope _ T _ _
      ((hjoins e).1.2.trans (hfinish _)) ((hjoins e).2.2.trans (hfinish _))
  simp_rw [hexpand] at h
  simpa [Fintype.sum_prod_type] using h

theorem global_winner_shift_bound {Member : Type*}
    [Fintype Member] [DecidableEq Member] [Fintype Edge]
    (membership : Edge → Member) (memberRecord : Member → Record)
    (join finish : Member → ℕ) (linkTime : Edge → ℕ)
    (label : Record → ℕ → ℤ) (T : ℕ) (D : ℤ)
    (hD : 0 ≤ D) (hfinish : ∀ m, finish m ≤ T)
    (htimes : ∀ e, join (membership e) ≤ linkTime e ∧ linkTime e ≤ finish (membership e))
    (hcapacity : ∀ m, ∑ e, (if membership e = m then (1 : ℤ) else 0) ≤ D)
    (hoverlap : ∀ v t,
      ∑ m, (if memberRecord m = v ∧ join m ≤ t ∧ t < finish m then (1 : ℤ) else 0) ≤ 1) :
    ∑ e, (label (memberRecord (membership e)) (join (membership e)) -
      label (memberRecord (membership e)) (linkTime e)) ≤
        D * ∑ cell : Record × Fin T, max 0 (-labelDelta T label cell) := by
  classical
  have hlocal : ∀ m t,
      ∑ e, (if membership e = m ∧ min (join (membership e)) (linkTime e) ≤ t ∧
        t < max (join (membership e)) (linkTime e) then (1 : ℤ) else 0) ≤ D := by
    intro m t
    calc
      _ ≤ ∑ e, if membership e = m then (1 : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro e he
        split_ifs <;> simp_all
      _ ≤ D := hcapacity m
  have hmult : ∀ v (t : Fin T),
      ∑ e, (if memberRecord (membership e) = v then
        joinCoefficient (join (membership e)) (linkTime e) t.val else 0) ≤ D := by
    intro v t
    have h := selected_join_multiplicity membership (fun m => decide (memberRecord m = v))
      join finish (fun e => join (membership e)) linkTime t.val 1 D hD
      (fun e => ⟨⟨le_refl _, (htimes e).1.trans (htimes e).2⟩, htimes e⟩)
      (fun m => hlocal m t.val) (by simpa using hoverlap v t.val)
    simp only [one_mul, decide_eq_true_eq] at h
    simpa only [abs_of_nonneg (joinCoefficient_nonneg_ordered _ _ _ (htimes _).1)] using h
  have h := channel_winner_coverage (fun e => memberRecord (membership e))
    (fun e (t : Fin T) => joinCoefficient (join (membership e)) (linkTime e) t.val)
    (fun v (t : Fin T) => labelDelta T label (v,t)) D
    (fun e t => joinCoefficient_nonneg_ordered _ _ _ (htimes e).1) hmult
  have hexpand : ∀ e,
      (∑ t : Fin T, joinCoefficient (join (membership e)) (linkTime e) t.val *
        (-labelDelta T label (memberRecord (membership e),t))) =
          label (memberRecord (membership e)) (join (membership e)) -
            label (memberRecord (membership e)) (linkTime e) := by
    intro e
    have htel := joinCoefficient_telescope (label (memberRecord (membership e))) T
      (join (membership e)) (linkTime e)
      ((htimes e).1.trans ((htimes e).2.trans (hfinish _)))
      ((htimes e).2.trans (hfinish _))
    simp only [labelDelta, mul_neg]
    rw [Finset.sum_neg_distrib,
      Fin.sum_univ_eq_sum_range (fun t => joinCoefficient (join (membership e)) (linkTime e) t *
        (label (memberRecord (membership e)) (t+1) - label (memberRecord (membership e)) t)) T,
      htel]
    ring
  simp_rw [hexpand] at h
  simpa [Fintype.sum_prod_type] using h

end GreedyForest.Execution
