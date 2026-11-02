import ChaCha.Entropy.ExpectationOrder

/-!
# Symmetry gives the exact adjacency probability

Every directed pair of distinct local occurrence tokens has the same
expected adjacency indicator. Their indicators sum to `w-1` in every
sample. Hence the probability for each pair is exactly `1/w`, independently
of how many other requests lie outside the interval.
-/

namespace ChaCha.Entropy

open scoped BigOperators
variable {m : Nat}

-- Do not expand finite averages or adjacency tests during higher-order
-- unification: their explicit lemmas provide the needed rewrites.
attribute [local irreducible] uniformMean adjacency

private theorem pair_permutation {α : Type*} {p q u v : α} (pq : p ≠ q) (uv : u ≠ v) :
    ∃ rename : Equiv.Perm α, rename p = u ∧ rename q = v := by
  let first : Bool → α := fun side => if side then p else q
  let second : Bool → α := fun side => if side then u else v
  have injFirst : Function.Injective first := by
    intro a b same
    cases a <;> cases b <;> simp_all [first]
  have injSecond : Function.Injective second := by
    intro a b same
    cases a <;> cases b <;> simp_all [second]
  obtain ⟨rename,maps⟩ := Equiv.Perm.exists_extending_pair first second injFirst injSecond
  exact ⟨rename,by simpa [first,second] using maps true,by simpa [first,second] using maps false⟩

theorem local_pair_permutation (active : Finset (Fin m)) {p q u v : Fin m}
    (hp : p ∈ active) (hq : q ∈ active) (hu : u ∈ active) (hv : v ∈ active)
    (pq : p ≠ q) (uv : u ≠ v) :
    ∃ rename : Equiv.Perm (Fin m),
      (∀ token, rename token ∈ active ↔ token ∈ active) ∧ rename p = u ∧ rename q = v := by
  obtain ⟨inside,first,second⟩ := pair_permutation
    (p := (⟨p,hp⟩ : active)) (q := ⟨q,hq⟩) (u := ⟨u,hu⟩) (v := ⟨v,hv⟩)
    (by intro same; exact pq (congrArg Subtype.val same))
    (by intro same; exact uv (congrArg Subtype.val same))
  let rename : Equiv.Perm (Fin m) := inside.extendDomain (Equiv.refl active)
  have image (token : active) : rename token = (inside token : Fin m) := by
    exact inside.extendDomain_apply_image (Equiv.refl active) token
  refine ⟨rename,?_,?_,?_⟩
  · intro token
    by_cases present : token ∈ active
    · rw [image ⟨token,present⟩]
      exact iff_of_true (inside ⟨token,present⟩).property present
    · have fixed : rename token = token := inside.extendDomain_apply_not_subtype (Equiv.refl active) present
      rw [fixed]
  · rw [image ⟨p,hp⟩,first]
  · rw [image ⟨q,hq⟩,second]

theorem adjacency_mean_same (active : Finset (Fin m)) {p q u v : Fin m}
    (hp : p ∈ active) (hq : q ∈ active) (hu : u ∈ active) (hv : v ∈ active)
    (pq : p ≠ q) (uv : u ≠ v) :
    uniformMean (fun sample => adjacency sample active p q) =
      uniformMean (fun sample => adjacency sample active u v) := by
  obtain ⟨rename,preserves,first,second⟩ := local_pair_permutation active hp hq hu hv pq uv
  calc
    _ = uniformMean (fun sample : Equiv.Perm (Fin m) => adjacency (sample.trans rename) active (rename p) (rename q)) :=
      (uniformMean_congr (fun sample => adjacency_relabel sample rename active preserves p q)).symm
    _ = uniformMean (fun sample => adjacency sample active (rename p) (rename q)) :=
      by simpa only [relabelSamples,Equiv.coe_fn_mk] using
        uniformMean_equiv (relabelSamples rename) (fun sample => adjacency sample active (rename p) (rename q))
    _ = _ := by rw [first,second]

private theorem sum_off_diagonal {α : Type*} [DecidableEq α] (active : Finset α) (value : ℝ) :
    (∑ p ∈ active, ∑ q ∈ active, if p = q then 0 else value) =
      (active.card : ℝ) * ((active.card : ℝ)-1) * value := by
  have row (p : α) (present : p ∈ active) :
      (∑ q ∈ active, if p = q then 0 else value) = (active.card : ℝ)*value-value := by
    calc
      _ = ∑ q ∈ active, (value - if p = q then value else 0) := by
        apply Finset.sum_congr rfl
        intro q member
        split_ifs <;> simp
      _ = _ := by simp [Finset.sum_sub_distrib,present]
  calc
    _ = ∑ p ∈ active, ((active.card : ℝ)*value-value) := Finset.sum_congr rfl row
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The exact probability is valid even with arbitrarily many outside
requests. The two specified tokens themselves ensure `w ≥ 2`. -/
theorem adjacency_mean (active : Finset (Fin m)) {p q : Fin m}
    (hp : p ∈ active) (hq : q ∈ active) (pq : p ≠ q) :
    uniformMean (fun sample => adjacency sample active p q) = 1 / (active.card : ℝ) := by
  let value := uniformMean (fun sample => adjacency sample active p q)
  have many : 1 < active.card := Finset.one_lt_card.mpr ⟨p,hp,q,hq,pq⟩
  have manyReal : (1:ℝ) < active.card := by exact_mod_cast many
  have total := uniformMean_congr (fun sample => adjacency_sum sample active)
  rw [uniformMean_sum] at total
  simp_rw [uniformMean_sum] at total
  rw [uniformMean_const] at total
  have common : (∑ a ∈ active, ∑ b ∈ active, uniformMean (fun sample => adjacency sample active a b)) =
      ∑ a ∈ active, ∑ b ∈ active, if a=b then 0 else value := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases equal : a=b
    · subst b
      simp
    · rw [if_neg equal]
      exact adjacency_mean_same active ha hb hp hq equal pq
  rw [common,sum_off_diagonal] at total
  have castSubtract : ((active.card - 1 : Nat):ℝ) = (active.card:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ active.card),Nat.cast_one]
  rw [castSubtract] at total
  change value = _
  apply (eq_div_iff (ne_of_gt (lt_trans (by norm_num) manyReal))).mpr
  have nonzero : (active.card : ℝ)-1 ≠ 0 := by linarith
  apply (mul_right_cancel₀ nonzero)
  nlinarith [total]

end ChaCha.Entropy
