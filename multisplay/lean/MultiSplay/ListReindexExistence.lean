import MultiSplay.ListReindex

/-! # Constructing a fixed ID renaming from a record permutation -/

namespace MultiSplay.ListReindex

variable {α : Type*}

def lift (rename : Equiv.Perm Nat) : Equiv.Perm Nat where
  toFun := fun i => match i with | 0 => 0 | j+1 => rename j + 1
  invFun := fun i => match i with | 0 => 0 | j+1 => rename.symm j + 1
  left_inv := by intro i; cases i <;> simp
  right_inv := by intro i; cases i <;> simp

@[simp] theorem lift_zero (rename : Equiv.Perm Nat) : lift rename 0 = 0 := rfl
@[simp] theorem lift_succ (rename : Equiv.Perm Nat) (i : Nat) : lift rename (i+1) = rename i + 1 := rfl

theorem Related.cons {rename : Equiv.Perm Nat} {a b : List α} (related : Related rename a b) (head : α) :
    Related (lift rename) (head :: a) (head :: b) := by
  refine ⟨by simp [related.length_eq], ?_, ?_⟩
  · intro i
    cases i with
    | zero => rfl
    | succ i => simpa using related.lookup i
  · intro i bound
    cases i with
    | zero => simp at bound
    | succ i =>
        simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
        simp only [lift_succ, related.fresh i bound]

theorem Related.trans {first second : Equiv.Perm Nat} {a b c : List α}
    (one : Related first a b) (two : Related second b c) : Related (first.trans second) a c := by
  refine ⟨one.length_eq.trans two.length_eq, ?_, ?_⟩
  · intro i
    exact (two.lookup (first i)).trans (one.lookup i)
  · intro i bound
    change second (first i) = i
    rw [one.fresh i bound, two.fresh i (by simpa only [one.length_eq] using bound)]

theorem exists_related {a b : List α} (permuted : a.Perm b) : ∃ rename, Related rename a b := by
  induction permuted with
  | nil => exact ⟨Equiv.refl _, rfl, fun _ => rfl, fun _ _ => rfl⟩
  | cons head tail ih =>
      obtain ⟨rename, related⟩ := ih
      exact ⟨lift rename, related.cons head⟩
  | swap x y tail =>
      refine ⟨Equiv.swap 0 1, by simp, ?_, ?_⟩
      · intro i
        rcases i with _ | (_ | i)
        · simp
        · simp
        · simp [Equiv.swap_apply_of_ne_of_ne]
      · intro i bound
        have large : 2 ≤ i := by simp only [List.length_cons] at bound; omega
        exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  | trans first second ihFirst ihSecond =>
      obtain ⟨one, firstRelated⟩ := ihFirst
      obtain ⟨two, secondRelated⟩ := ihSecond
      exact ⟨one.trans two, firstRelated.trans secondRelated⟩

theorem inverse_bound (rename : Equiv.Perm Nat) (size : Nat)
    (fresh : ∀ i, size ≤ i → rename i = i) (i : Nat) (inside : i < size) : rename.symm i < size := by
  by_contra outside
  have eq := fresh (rename.symm i) (by omega)
  rw [rename.apply_symm_apply] at eq
  omega

noncomputable def reorder (rename : Equiv.Perm Nat) (a : List α)
    (fresh : ∀ i, a.length ≤ i → rename i = i) : List α :=
  List.ofFn (fun i : Fin a.length => a[rename.symm i.val]'(inverse_bound rename a.length fresh i.val i.isLt))

theorem reorder_related (rename : Equiv.Perm Nat) (a : List α)
    (fresh : ∀ i, a.length ≤ i → rename i = i) : Related rename a (reorder rename a fresh) := by
  refine ⟨by simp [reorder], ?_, fresh⟩
  intro i
  by_cases inside : i < a.length
  · have mapped : rename i < a.length := by
      by_contra outside
      have fixed := fresh (rename i) (by omega)
      have same : rename i = i := rename.injective fixed
      omega
    simp [reorder, List.getElem?_eq_getElem, inside, mapped]
  · have bound : a.length ≤ i := by omega
    simp [reorder, fresh i bound, List.getElem?_eq_none bound, bound]

end MultiSplay.ListReindex
