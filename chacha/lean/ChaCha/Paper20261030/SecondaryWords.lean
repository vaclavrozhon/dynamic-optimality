import ChaCha.Paper20261030.SecondaryResetBound

/-!
# Concrete secondary write words

At a secondary split at depth `c`, visiting depth `d` writes the bit
`c < d`. Increasing depth visits therefore write a block of UP (`false`)
followed by a block of DOWN (`true`). Repeated writes have no flip cost.
This module connects that actual word to the previously proved block
accounting, preserving both the exact cost and the final memory bit.
-/

namespace ChaCha.Paper20261030.Secondary

open FlipAccounting

def writeWord (c : Nat) (ds : List Nat) : List Bool :=
  ds.map (fun d => decide (c < d))

theorem writeWord_form (c : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·)) :
    writeWord c ds = List.replicate (lowDepths c ds).length false ++
      List.replicate (highDepths c ds).length true := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    by_cases hd : d ≤ c
    · have hcd : ¬ c < d := by omega
      simp only [writeWord,List.map_cons,decide_eq_false hcd]
      rw [show ds.map (fun d => decide (c < d)) = _ from ih htail]
      simp [lowDepths,highDepths,hd,hcd,List.replicate_succ]
    · have hcd : c < d := by omega
      have hlow : lowDepths c ds = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        have := hhead e he
        simp only [decide_eq_true_eq]
        omega
      have hhigh : highDepths c ds = ds := by
        apply List.filter_eq_self.mpr
        intro e he
        have := hhead e he
        simp only [decide_eq_true_eq]
        omega
      simp only [writeWord,List.map_cons,decide_eq_true hcd]
      rw [show ds.map (fun d => decide (c < d)) = _ from ih htail,hlow,hhigh]
      simp [lowDepths,highDepths,hd,hcd,show ds.filter (fun d => decide (d ≤ c)) = [] from hlow,
        show ds.filter (fun d => decide (c < d)) = ds from hhigh,List.replicate_succ]

theorem changes_replicate_prefix (a b : Bool) (n : Nat) (ys : List Bool) :
    changesFrom a (List.replicate (n + 1) b ++ ys) =
      edgeChange a b + changesFrom b ys := by
  induction n generalizing a with
  | zero => simp [List.replicate_succ]
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,changesFrom_cons,ih]
    simp

theorem last_replicate_prefix (a b : Bool) (n : Nat) (ys : List Bool) :
    (List.replicate (n + 1) b ++ ys).getLastD a = ys.getLastD b := by
  induction n generalizing a with
  | zero => simpa only [List.replicate_succ,List.replicate_zero,List.nil_append,
      List.cons_append] using (List.getLastD_cons (a := a) (l := ys) (b := b))
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,List.getLastD_cons,ih]

def compactWord (m n : Nat) : List Bool :=
  (if m = 0 then [] else [false]) ++ (if n = 0 then [] else [true])

theorem compactWord_changes (a : Bool) (m n : Nat) :
    changesFrom a (List.replicate m false ++ List.replicate n true) =
      changesFrom a (compactWord m n) := by
  have hrep (a b : Bool) (n : Nat) :
      changesFrom a (List.replicate (n + 1) b) = edgeChange a b := by
    simpa only [List.append_nil,changesFrom_nil,Nat.add_zero] using
      changes_replicate_prefix a b n []
  cases m <;> cases n <;> simp [compactWord,changes_replicate_prefix,hrep]

theorem compactWord_last (a : Bool) (m n : Nat) :
    (List.replicate m false ++ List.replicate n true).getLastD a =
      (compactWord m n).getLastD a := by
  have hrep (a b : Bool) (n : Nat) :
      (List.replicate (n + 1) b).getLastD a = b := by
    simpa only [List.append_nil,List.getLastD_nil] using
      last_replicate_prefix a b n []
  cases m <;> cases n <;> simp only [compactWord,Nat.succ_ne_zero,if_false,if_true,
    List.replicate_zero,List.nil_append,List.append_nil,last_replicate_prefix,hrep,
    List.getLastD_cons,List.getLastD_nil,List.singleton_append]

def visitBlock (c : Nat) (ds : List Nat) : Option Block :=
  if lowDepths c ds = [] then
    if highDepths c ds = [] then none else some .right
  else if highDepths c ds = [] then some .left else some .reset

def blockWord (b : Option Block) : List Bool := b.toList.flatMap Block.word

theorem visitBlock_word (c : Nat) (ds : List Nat) :
    blockWord (visitBlock c ds) =
      compactWord (lowDepths c ds).length (highDepths c ds).length := by
  unfold visitBlock
  split_ifs <;> simp_all [blockWord,Block.word,compactWord]

/-- Exact flip count, including a change from the old stored preference. -/
theorem writeWord_changes (c : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·))
    (initial : Bool) :
    changesFrom initial (writeWord c ds) =
      changesFrom initial (blockWord (visitBlock c ds)) := by
  rw [writeWord_form c ds hs,visitBlock_word,compactWord_changes]

/-- Compression preserves the persistent preference for the next access. -/
theorem writeWord_last (c : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·))
    (initial : Bool) :
    (writeWord c ds).getLastD initial =
      (blockWord (visitBlock c ds)).getLastD initial := by
  rw [writeWord_form c ds hs,visitBlock_word,compactWord_last]

theorem visitBlock_resets (c : Nat) (ds : List Nat) :
    ((visitBlock c ds).toList.map Block.resets).sum =
      if lowDepths c ds = [] ∨ highDepths c ds = [] then 0 else 1 := by
  unfold visitBlock
  split_ifs <;> simp_all [Block.resets]

theorem writeWord_changes_le_two (c : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·))
    (initial : Bool) : changesFrom initial (writeWord c ds) ≤ 2 := by
  rw [writeWord_changes c ds hs]
  cases h : visitBlock c ds with
  | none => simp [blockWord]
  | some b => cases b <;> cases initial <;> decide +kernel

/-- Two flips can only be DOWN-to-UP followed by UP-to-DOWN. -/
theorem writeWord_two_iff (c : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·))
    (initial : Bool) :
    changesFrom initial (writeWord c ds) = 2 ↔
      initial = true ∧ visitBlock c ds = some .reset := by
  rw [writeWord_changes c ds hs]
  cases h : visitBlock c ds with
  | none => simp [blockWord]
  | some b => cases b <;> cases initial <;> decide +kernel

theorem changes_append (initial : Bool) (xs ys : List Bool) :
    changesFrom initial (xs ++ ys) =
      changesFrom initial xs + changesFrom (xs.getLastD initial) ys := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append,changesFrom_cons,List.getLastD_cons,ih]
    omega

def historyBlocks (c : Nat) (visits : List (List Nat)) : List Block :=
  visits.filterMap (visitBlock c)

theorem historyBlocks_cons (c : Nat) (ds : List Nat) (visits : List (List Nat)) :
    historyBlocks c (ds :: visits) =
      (visitBlock c ds).toList ++ historyBlocks c visits := by
  cases h : visitBlock c ds <;> simp [historyBlocks,h]

/-- Exact whole-history cost after suppressing repeated writes within each
request. Empty visits leave the stored preference untouched. -/
theorem writeHistory_changes (c : Nat) (visits : List (List Nat))
    (hs : ∀ ds ∈ visits, ds.Pairwise (· < ·)) (initial : Bool) :
    changesFrom initial (visits.flatMap (writeWord c)) =
      changesFrom initial ((historyBlocks c visits).flatMap Block.word) := by
  induction visits generalizing initial with
  | nil => rfl
  | cons ds visits ih =>
    have hd := hs ds (by simp)
    have ht : ∀ xs ∈ visits, xs.Pairwise (· < ·) := fun xs hx => hs xs (by simp [hx])
    rw [List.flatMap_cons,historyBlocks_cons,List.flatMap_append]
    rw [changes_append,changes_append,writeWord_changes c ds hd,
      writeWord_last c ds hd,ih ht]
    rfl

/-- The Boolean accounting part of secondary charging. The identification
of regular heads with fragment LCA updates is a separate proof obligation. -/
theorem writeHistory_head_bound (c : Nat) (visits : List (List Nat))
    (hs : ∀ ds ∈ visits, ds.Pairwise (· < ·)) (initial : Bool)
    (regularHeads : List Bool) (first : Option Bool)
    (hh : (historyBlocks c visits).map Block.head = first.toList ++ regularHeads) :
    changesFrom initial (visits.flatMap (writeWord c)) ≤
      2 * rlCount regularHeads + 2 * ((historyBlocks c visits).map Block.resets).sum + 3 := by
  rw [writeHistory_changes c visits hs]
  exact head_reset_bound initial _ regularHeads first hh

end ChaCha.Paper20261030.Secondary
