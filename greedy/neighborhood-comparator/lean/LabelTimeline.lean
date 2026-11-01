import FiniteExecution

/-!
Chronological composition of literal one-record updates. All global
snapshot bounds and elementary-cell provenance facts are derived from
local before/after certificates. There is no aggregate variation premise.
-/
namespace GreedyForest.Timeline

inductive Origin (Block : Type*) where
  | phase (block : Block)
  | paid
  | free
  deriving DecidableEq

structure Update (Record Block : Type*) where
  record : Record
  value : ℤ
  origin : Origin Block
  good : Bool

variable {Record Block : Type*} [DecidableEq Record]

def applyUpdate (labels : Record → ℤ) (u : Update Record Block) : Record → ℤ :=
  Function.update labels u.record u.value

def run (labels : Record → ℤ) (updates : List (Update Record Block)) : Record → ℤ :=
  updates.foldl applyUpdate labels

def stateAt (labels : Record → ℤ) (updates : List (Update Record Block)) (time : ℕ) : Record → ℤ :=
  run labels (updates.take time)

def LocalValid (K : ℤ) (labels : Record → ℤ) (u : Update Record Block) : Prop :=
  (1 ≤ u.value ∧ u.value ≤ K) ∧
    (u.origin = .free → u.value ≤ labels u.record) ∧
    (u.good = true → u.value+1 ≤ labels u.record)

def Valid (K : ℤ) (labels : Record → ℤ) : List (Update Record Block) → Prop
  | [] => True
  | u::rest => LocalValid K labels u ∧ Valid K (applyUpdate labels u) rest

theorem run_append (labels : Record → ℤ) (first second : List (Update Record Block)) :
    run labels (first++second) = run (run labels first) second := by
  exact List.foldl_append

/-- Local snapshot times in a later segment embed by the exact length
of its preceding update list. Administrative cells and idle cells may
be included without changing this identity. -/
theorem stateAt_append_right (labels : Record → ℤ)
    (first second : List (Update Record Block)) (time : ℕ) :
    stateAt labels (first++second) (first.length+time) =
      stateAt (run labels first) second time := by
  simp only [stateAt,List.take_length_add_append,run_append]

theorem stateAt_append_left (labels : Record → ℤ)
    (first second : List (Update Record Block)) (time : ℕ) (ht : time ≤ first.length) :
    stateAt labels (first++second) time = stateAt labels first time := by
  simp only [stateAt,List.take_append_of_le_length ht]

theorem valid_append {K : ℤ} {labels : Record → ℤ}
    {first second : List (Update Record Block)}
    (hfirst : Valid K labels first) (hsecond : Valid K (run labels first) second) :
    Valid K labels (first++second) := by
  induction first generalizing labels with
  | nil => exact hsecond
  | cons u rest ih =>
      exact ⟨hfirst.1,ih hfirst.2 hsecond⟩

theorem applyUpdate_bounds {K : ℤ} {labels : Record → ℤ} (u : Update Record Block)
    (hlabels : ∀ v, 1 ≤ labels v ∧ labels v ≤ K) (hu : 1 ≤ u.value ∧ u.value ≤ K) :
    ∀ v, 1 ≤ applyUpdate labels u v ∧ applyUpdate labels u v ≤ K := by
  intro v
  by_cases heq : v=u.record
  · subst v; simpa [applyUpdate] using hu
  · simpa [applyUpdate,heq] using hlabels v

theorem stateAt_bounds {K : ℤ} {labels : Record → ℤ} {updates : List (Update Record Block)}
    (hlabels : ∀ v, 1 ≤ labels v ∧ labels v ≤ K) (hvalid : Valid K labels updates)
    (time : ℕ) : ∀ v, 1 ≤ stateAt labels updates time v ∧ stateAt labels updates time v ≤ K := by
  induction updates generalizing labels time with
  | nil => simpa [stateAt,run] using hlabels
  | cons u rest ih =>
      cases time with
      | zero => simpa [stateAt,run] using hlabels
      | succ time =>
          exact ih (applyUpdate_bounds u hlabels hvalid.1.1) hvalid.2 time

theorem local_valid_at {K : ℤ} {labels : Record → ℤ} {updates : List (Update Record Block)}
    (hvalid : Valid K labels updates) (time : Fin updates.length) :
    LocalValid K (stateAt labels updates time) (updates.get time) := by
  induction updates generalizing labels with
  | nil => exact Fin.elim0 time
  | cons u rest ih =>
      rcases time with ⟨time,htime⟩
      cases time with
      | zero => exact hvalid.1
      | succ time =>
          have ht : time < rest.length := by simpa using htime
          exact ih hvalid.2 ⟨time,ht⟩

theorem stateAt_succ (labels : Record → ℤ) (updates : List (Update Record Block))
    (time : Fin updates.length) :
    stateAt labels updates (time.val+1) =
      applyUpdate (stateAt labels updates time) (updates.get time) := by
  simp only [stateAt,run,List.take_succ_eq_append_getElem time.isLt,
    List.foldl_append,List.foldl_cons,List.foldl_nil,List.get_eq_getElem]

def delta (labels : Record → ℤ) (updates : List (Update Record Block))
    (cell : Record × Fin updates.length) : ℤ :=
  stateAt labels updates (cell.2.val+1) cell.1 - stateAt labels updates cell.2 cell.1

theorem changed_record {labels : Record → ℤ} {updates : List (Update Record Block)}
    (cell : Record × Fin updates.length) (hchange : delta labels updates cell ≠ 0) :
    cell.1 = (updates.get cell.2).record := by
  by_contra hne
  apply hchange
  simp only [delta,stateAt_succ,applyUpdate,Function.update_of_ne hne,sub_self]

theorem positive_not_free {K : ℤ} {labels : Record → ℤ} {updates : List (Update Record Block)}
    (hvalid : Valid K labels updates) (cell : Record × Fin updates.length)
    (hpositive : 0 < delta labels updates cell) :
    (updates.get cell.2).origin ≠ .free := by
  intro hfree
  have hlocal := (local_valid_at hvalid cell.2).2.1 hfree
  have heq := changed_record cell (ne_of_gt hpositive)
  simp only [delta,stateAt_succ,applyUpdate,heq,Function.update_self] at hpositive
  omega

def Positive (labels : Record → ℤ) (updates : List (Update Record Block)) :=
  {cell : Record × Fin updates.length // 0 < delta labels updates cell}

def Paid (updates : List (Update Record Block)) :=
  {time : Fin updates.length // (updates.get time).origin = .paid}

noncomputable instance paidFintype (updates : List (Update Record Block)) : Fintype (Paid updates) := by
  classical
  unfold Paid
  infer_instance

noncomputable def positiveOrigin {K : ℤ} {labels : Record → ℤ}
    {updates : List (Update Record Block)} (hvalid : Valid K labels updates)
    (event : Positive labels updates) : Sum Block (Paid updates) :=
  match horigin : (updates.get event.val.2).origin with
  | .phase block => Sum.inl block
  | .paid => Sum.inr ⟨event.val.2,horigin⟩
  | .free => False.elim (positive_not_free hvalid event.val event.property horigin)

theorem positiveOrigin_paid_time {K : ℤ} {labels : Record → ℤ}
    {updates : List (Update Record Block)} (hvalid : Valid K labels updates)
    (event : Positive labels updates) (paid : Paid updates)
    (heq : positiveOrigin hvalid event = Sum.inr paid) : event.val.2 = paid.val := by
  unfold positiveOrigin at heq
  split at heq
  · contradiction
  · have h := Sum.inr.inj heq
    exact congrArg Subtype.val h
  · rename_i hfree
    exact False.elim (positive_not_free hvalid event.val event.property hfree)

/-- Paid administrative slots are actual update occurrences. No two
positive elementary cells can claim one such slot. -/
theorem positivePaidUnique {K : ℤ} {labels : Record → ℤ}
    {updates : List (Update Record Block)} (hvalid : Valid K labels updates)
    (a b : Positive labels updates) (paid : Paid updates)
    (ha : positiveOrigin hvalid a = Sum.inr paid)
    (hb : positiveOrigin hvalid b = Sum.inr paid) : a=b := by
  have ht : a.val.2 = b.val.2 := (positiveOrigin_paid_time hvalid a paid ha).trans
    (positiveOrigin_paid_time hvalid b paid hb).symm
  have hra := changed_record a.val (ne_of_gt a.property)
  have hrb := changed_record b.val (ne_of_gt b.property)
  apply Subtype.ext
  apply Prod.ext
  · rw [ht] at hra
    exact hra.trans hrb.symm
  · exact ht

def Good (updates : List (Update Record Block)) :=
  {time : Fin updates.length // (updates.get time).good = true}

instance goodFintype (updates : List (Update Record Block)) : Fintype (Good updates) := by
  unfold Good
  infer_instance

def goodCell (updates : List (Update Record Block)) (event : Good updates) :
    Record × Fin updates.length := ((updates.get event.val).record,event.val)

omit [DecidableEq Record] in
theorem goodCell_injective (updates : List (Update Record Block)) :
    Function.Injective (goodCell updates) := by
  intro a b heq
  apply Subtype.ext
  exact congrArg Prod.snd heq

theorem goodCell_drop {K : ℤ} {labels : Record → ℤ}
    {updates : List (Update Record Block)} (hvalid : Valid K labels updates)
    (event : Good updates) : delta labels updates (goodCell updates event) ≤ -1 := by
  have hdrop := (local_valid_at hvalid event.val).2.2 event.property
  simp only [delta,goodCell,stateAt_succ,applyUpdate,Function.update_self]
  omega

end GreedyForest.Timeline

#print axioms GreedyForest.Timeline.stateAt_bounds
#print axioms GreedyForest.Timeline.positivePaidUnique
#print axioms GreedyForest.Timeline.goodCell_drop
