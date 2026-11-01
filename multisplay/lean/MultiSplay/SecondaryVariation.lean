import TangoSquared.TurnAccounting
import TangoSquared.FlipAccounting

/-!
# The cost of reversing the ancestor block in one secondary row

`Mixed` means that a binary write block contains both directions. Reversing a
block preserves all its internal variation; only its two boundary edges may
change. The estimates retain arbitrary preceding and following writes, so they
can be summed over successive changes of query order without resetting bits.
-/

namespace MultiSplay.Secondary

open TangoSquared (edgeChange changesFrom changesFrom_cons changesFrom_nil)

theorem changesFrom_append (initial : Bool) (first last : List Bool) :
    changesFrom initial (first++last) = changesFrom initial first + changesFrom (first.getLastD initial) last := by
  induction first generalizing initial with
  | nil => simp [changesFrom]
  | cons head tail ih => simp only [List.cons_append, changesFrom_cons, ih, List.getLastD_cons, Nat.add_assoc]

def Mixed (word : List Bool) : Prop := false ∈ word ∧ true ∈ word

instance (word : List Bool) : Decidable (Mixed word) := inferInstanceAs (Decidable (_ ∧ _))

theorem reversal_walk (first last : Bool) (word : List Bool) :
    changesFrom first (word++[last]) = changesFrom last (word.reverse++[first]) := by
  induction word generalizing first with
  | nil => simp [changesFrom, TangoSquared.edgeChange_comm]
  | cons head tail ih =>
      simp only [List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append, changesFrom_cons]
      rw [TangoSquared.changesFrom_append_cons last tail.reverse head [first]]
      simp only [changesFrom_cons, changesFrom_nil, Nat.add_zero]
      rw [ih]
      rw [TangoSquared.edgeChange_comm first head]
      omega

theorem endpoint_change (first left right : Bool) (word : List Bool) :
    changesFrom first (word++[left]) ≤ changesFrom first (word++[right])+1 := by
  rw [changesFrom_append, changesFrom_append]
  have edge : edgeChange (word.getLastD first) left ≤ 1 := by
    unfold edgeChange
    split <;> omega
  simp only [changesFrom_cons, changesFrom_nil, Nat.add_zero]
  omega

theorem reversal_boundary (first last : Bool) (word : List Bool) :
    changesFrom first (word.reverse++[last]) ≤ changesFrom first (word++[last])+2 := by
  rw [← reversal_walk last first word]
  have initial := TangoSquared.FlipAccounting.changesFrom_initial_le last first (word++[first])
  have final := endpoint_change first first last word
  omega

theorem reversal_initial (first : Bool) (word : List Bool) :
    changesFrom first word.reverse ≤ changesFrom first word+1 := by
  have initialPart := TangoSquared.changesFrom_sublist (List.sublist_append_left word.reverse [first]) first
  rw [← reversal_walk first first word] at initialPart
  rw [changesFrom_append] at initialPart
  have edge : edgeChange (word.getLastD first) first ≤ 1 := by unfold edgeChange; split <;> omega
  simp only [changesFrom_cons, changesFrom_nil, Nat.add_zero] at initialPart
  omega

theorem contextual_reversal (initial : Bool) (front word back : List Bool) :
    changesFrom initial (front++word.reverse++back) ≤ changesFrom initial (front++word++back)+2 := by
  rw [List.append_assoc, List.append_assoc,
    changesFrom_append initial front (word.reverse++back), changesFrom_append initial front (word++back)]
  cases back with
  | nil =>
      simp only [List.append_nil]
      have bound := reversal_initial (front.getLastD initial) word
      omega
  | cons last rest =>
      rw [TangoSquared.changesFrom_append_cons (front.getLastD initial) word.reverse last rest,
        TangoSquared.changesFrom_append_cons (front.getLastD initial) word last rest]
      have bound := reversal_boundary (front.getLastD initial) last word
      omega

theorem reverse_eq_of_not_mixed {word : List Bool} (homogeneous : ¬ Mixed word) : word.reverse = word := by
  by_cases left : false ∈ word
  · have right : true ∉ word := fun h => homogeneous ⟨left,h⟩
    have constant : word = List.replicate word.length false :=
      List.eq_replicate_of_mem (fun bit member => by cases bit; rfl; exact False.elim (right member))
    rw [constant, List.reverse_replicate]
  · have constant : word = List.replicate word.length true :=
      List.eq_replicate_of_mem (fun bit member => by cases bit; exact False.elim (left member); rfl)
    rw [constant, List.reverse_replicate]

theorem contextual_reversal_mixed (initial : Bool) (front word back : List Bool) :
    changesFrom initial (front++word.reverse++back) ≤
      changesFrom initial (front++word++back) + 2*(if Mixed word then 1 else 0) := by
  by_cases mixed : Mixed word
  · simpa only [if_pos mixed] using contextual_reversal initial front word back
  · simp only [if_neg mixed, reverse_eq_of_not_mixed mixed, Nat.mul_zero, Nat.add_zero, Nat.le_refl]

end MultiSplay.Secondary
