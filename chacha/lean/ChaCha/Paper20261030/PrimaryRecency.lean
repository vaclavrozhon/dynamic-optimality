import ChaCha.Paper20261030.PrimaryFlipBound

/-!
# The first actual exit is the LCA with the current path endpoint

`referenceLCA` is the depth of the common ancestor in the fixed primary
shape. Preference bits play no part in its definition. A complete access
sets the endpoint to the requested key. Thus the next first exit is the
LCA with the last request, including the completion depth for repetitions.
-/

namespace ChaCha.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

def referenceLCA : PrefRouter α → α → α → Nat
  | .leaf _, _, _ => 0
  | .fork _ l r, x, y =>
      if x ∈ l.leaves ∧ y ∈ l.leaves then 1 + referenceLCA l x y
      else if x ∈ r.leaves ∧ y ∈ r.leaves then 1 + referenceLCA r x y
      else 0

theorem perfect_height {H : Nat} {t : PrefRouter α} (h : Perfect H t) :
    t.height = H := by
  induction H generalizing t with
  | zero => cases t <;> simp_all [Perfect,height]
  | succ H ih =>
    cases t with
    | leaf a => contradiction
    | fork b l r => simp [height,ih h.1,ih h.2]

theorem perfect_access {H : Nat} {t : PrefRouter α} (h : Perfect H t) (x : α) :
    Perfect H (t.access x) := by
  induction t generalizing H with
  | leaf a => exact h
  | fork b l r ihl ihr =>
    cases H with
    | zero => contradiction
    | succ H =>
      simp only [access]
      split_ifs <;> exact ⟨by first | exact ihl h.1 | exact h.1,
        by first | exact ihr h.2 | exact h.2⟩

theorem referenceLCA_access (t : PrefRouter α) (x y z : α) :
    (t.access z).referenceLCA x y = t.referenceLCA x y := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    simp only [access]
    split_ifs <;> simp only [referenceLCA,access_leaves,ihl,ihr]

theorem headD_succ (ds : List Nat) (H : Nat) :
    (ds.map Nat.succ).headD (H + 1) = ds.headD H + 1 := by
  cases ds <;> rfl

theorem first_exit_lca {H : Nat} {t : PrefRouter α} (hp : Perfect H t)
    (hn : t.leaves.Nodup) {x : α} (hx : x ∈ t.leaves) :
    (t.exitDepths x).headD H = t.referenceLCA t.terminal x := by
  induction t generalizing H with
  | leaf a =>
    cases H <;> simp_all [Perfect,exitDepths,referenceLCA]
  | fork b l r ihl ihr =>
    cases H with
    | zero => contradiction
    | succ H =>
      obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
      have htl := terminal_mem l
      have htr := terminal_mem r
      have htlr : l.terminal ∉ r.leaves := fun h => hdis _ htl _ h rfl
      have htrl : r.terminal ∉ l.leaves := fun h => hdis _ h _ htr rfl
      by_cases hl : x ∈ l.leaves
      · have hr : x ∉ r.leaves := fun h => hdis _ hl _ h rfl
        have hi := ihl hp.1 hnl hl
        cases b <;> simp [exitDepths,referenceLCA,PrefRouter.terminal,hl,hr,
          htl,htr,htlr,htrl,headD_succ,hi,Nat.add_comm] <;>
          simpa only [List.headD_eq_head?_getD] using hi
      · have hr : x ∈ r.leaves := (List.mem_append.mp hx).resolve_left hl
        have hi := ihr hp.2 hnr hr
        cases b <;> simp [exitDepths,referenceLCA,PrefRouter.terminal,hl,hr,
          htl,htr,htlr,htrl,headD_succ,hi,Nat.add_comm] <;>
          simpa only [List.headD_eq_head?_getD] using hi

/-- After a completed request, the first exit for the next request is
determined by the previous key, independently of the old preferences. -/
theorem next_first_exit_lca {H : Nat} {t : PrefRouter α} (hp : Perfect H t)
    (hn : t.leaves.Nodup) {x y : α} (hx : x ∈ t.leaves) (hy : y ∈ t.leaves) :
    ((t.access x).exitDepths y).headD H = t.referenceLCA x y := by
  have hp' := perfect_access hp x
  have hn' : (t.access x).leaves.Nodup := by simpa only [access_leaves] using hn
  have hy' : y ∈ (t.access x).leaves := by simpa only [access_leaves] using hy
  rw [first_exit_lca hp' hn' hy',terminal_access x t hx,referenceLCA_access]

end ChaCha.PreferredProjection.PrefRouter
