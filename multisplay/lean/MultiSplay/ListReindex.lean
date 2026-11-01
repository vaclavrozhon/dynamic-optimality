import MultiSplay.InterfaceBlockIds
import Mathlib.Data.List.FinRange

/-!
# Fixed renaming of an append-only record list

The permutation fixes all currently unused IDs. Consequently it also fixes
newly appended IDs, and the same renaming transports an entire execution.
-/

namespace MultiSplay.ListReindex

variable {α : Type*}

structure Related (rename : Equiv.Perm Nat) (a b : List α) : Prop where
  length_eq : a.length = b.length
  lookup : ∀ i, b[rename i]? = a[i]?
  fresh : ∀ i, a.length ≤ i → rename i = i

theorem Related.bound {rename : Equiv.Perm Nat} {a b : List α} (related : Related rename a b)
    {i : Nat} (inside : i < a.length) : rename i < b.length := by
  have found := related.lookup i
  rw [List.getElem?_eq_getElem inside] at found
  exact (List.getElem?_eq_some_iff.mp found).1

noncomputable def Related.finite {rename : Equiv.Perm Nat} {a b : List α} (related : Related rename a b) :
    Equiv.Perm (Fin a.length) :=
  Equiv.ofBijective (fun i => ⟨rename i.val, by simpa only [← related.length_eq] using related.bound i.isLt⟩)
    ((Finite.injective_iff_bijective).mp (by
      intro i j eq
      exact Fin.ext (rename.injective (congrArg Fin.val eq))))

theorem Related.perm {rename : Equiv.Perm Nat} {a b : List α} (related : Related rename a b) : a.Perm b := by
  let g : Fin a.length → α := fun i => b[i.val]'(by rw [← related.length_eq]; exact i.isLt)
  have rightEq : List.ofFn g = b := by
    apply List.ext_getElem
    · simpa using related.length_eq
    · intro i leftBound rightBound
      simp [g]
  have leftEq : List.ofFn (g ∘ related.finite) = a := by
    apply List.ext_getElem
    · simp
    · intro i leftBound rightBound
      have found := related.lookup i
      rw [List.getElem?_eq_getElem rightBound, List.getElem?_eq_getElem (related.bound rightBound)] at found
      simpa [g, Related.finite] using Option.some.inj found
  simpa only [leftEq, rightEq] using related.finite.ofFn_comp_perm g

theorem Related.modify {rename : Equiv.Perm Nat} {a b : List α} (related : Related rename a b)
    (i : Nat) (f : α → α) : Related rename (a.modify i f) (b.modify (rename i) f) := by
  refine ⟨by simpa using related.length_eq, ?_, ?_⟩
  · intro j
    simp only [List.getElem?_modify, related.lookup, rename.injective.eq_iff]
  · intro j bound
    apply related.fresh j
    simpa using bound

theorem Related.append {rename : Equiv.Perm Nat} {a b : List α} (related : Related rename a b)
    (extra : List α) : Related rename (a ++ extra) (b ++ extra) := by
  refine ⟨by simp [related.length_eq], ?_, ?_⟩
  · intro i
    by_cases inside : i < a.length
    · rw [List.getElem?_append_left inside, List.getElem?_append_left (related.bound inside)]
      exact related.lookup i
    · have oldLe : a.length ≤ i := by omega
      rw [related.fresh i oldLe, List.getElem?_append_right oldLe,
        List.getElem?_append_right (by have := related.length_eq; omega : b.length ≤ i), related.length_eq]
  · intro i bound
    apply related.fresh i
    simp only [List.length_append] at bound
    omega

end MultiSplay.ListReindex
