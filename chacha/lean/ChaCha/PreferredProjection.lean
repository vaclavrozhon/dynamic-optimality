import ChaCha.RouterProjection

/-!
# A retained preferred terminal survives leaf projection

This is the preference-decorated version of the existing alphabetic
`RouterProjection.Router` pruning kernel. A false branch bit prefers left;
a true bit prefers right. Unary suppression preserves surviving bits.

If an old preferred terminal is retained, projection preserves it. Thus
source subtrees with distinct retained preferred terminals still have
distinct projected terminals. Applying this to old preferred paths uses
their standard identification by preferred terminal; that global component
identification, guard transport, and cost accounting are not formalized
here. No theorem about dynamic optimality is asserted.
-/

namespace ChaCha.PreferredProjection

open RouterProjection

inductive PrefRouter (α : Type*) where
  | leaf : α → PrefRouter α
  | fork : Bool → PrefRouter α → PrefRouter α → PrefRouter α
  deriving DecidableEq

namespace PrefRouter

variable {α : Type*}

/-- Follow the preferred children to a leaf. -/
def terminal : PrefRouter α → α
  | .leaf a => a
  | .fork right l r => if right then terminal r else terminal l

def erase : PrefRouter α → Router α
  | .leaf a => .leaf a
  | .fork _ l r => .fork (erase l) (erase r)

def eraseOption : Option (PrefRouter α) → Router α
  | none => .empty
  | some t => erase t

/-- Contract a unary branch, retaining bits at genuine binary branches. -/
def combine (right : Bool) : Option (PrefRouter α) → Option (PrefRouter α) →
    Option (PrefRouter α)
  | none, r => r
  | l, none => l
  | some l, some r => some (.fork right l r)

def prune (p : α → Bool) : PrefRouter α → Option (PrefRouter α)
  | .leaf a => if p a then some (.leaf a) else none
  | .fork right l r => combine right (prune p l) (prune p r)

@[simp] theorem eraseOption_combine (right : Bool)
    (l r : Option (PrefRouter α)) :
    eraseOption (combine right l r) =
      Router.join (eraseOption l) (eraseOption r) := by
  cases l with
  | none => rfl
  | some l =>
      cases r with
      | none => simp [combine, eraseOption]
      | some r => cases l <;> cases r <;> rfl

/-- The decorated projection has exactly the existing physical pruning shape. -/
theorem erase_prune (p : α → Bool) (t : PrefRouter α) :
    eraseOption (prune p t) = Router.prune p (erase t) := by
  induction t with
  | leaf a => cases hp : p a <;> simp [prune, eraseOption, erase, Router.prune, hp]
  | fork right l r ihl ihr =>
      simp only [prune, eraseOption_combine, erase, Router.prune, ihl, ihr]

/-- Keeping the old preferred terminal preserves that terminal. -/
theorem retained_terminal (p : α → Bool) (t : PrefRouter α)
    (hkeep : p (terminal t) = true) :
    ∃ u, prune p t = some u ∧ terminal u = terminal t := by
  induction t with
  | leaf a =>
      exact ⟨.leaf a, by simpa [prune, terminal] using hkeep, rfl⟩
  | fork right l r ihl ihr =>
      cases right with
      | false =>
          obtain ⟨l', hl, hterm⟩ := ihl (by simpa [terminal] using hkeep)
          cases hr : prune p r with
          | none =>
              exact ⟨l', by simp [prune, hl, hr, combine],
                by simpa [terminal] using hterm⟩
          | some r' =>
              exact ⟨.fork false l' r', by simp [prune, hl, hr, combine],
                by simpa [terminal] using hterm⟩
      | true =>
          obtain ⟨r', hr, hterm⟩ := ihr (by simpa [terminal] using hkeep)
          cases hl : prune p l with
          | none =>
              exact ⟨r', by simp [prune, hl, hr, combine],
                by simpa [terminal] using hterm⟩
          | some l' =>
              exact ⟨.fork true l' r', by simp [prune, hl, hr, combine],
                by simpa [terminal] using hterm⟩

theorem terminal_of_prune_eq_some (p : α → Bool) (t u : PrefRouter α)
    (hkeep : p (terminal t) = true) (hout : prune p t = some u) :
    terminal u = terminal t := by
  obtain ⟨v, hv, hterm⟩ := retained_terminal p t hkeep
  have huv : u = v := Option.some.inj (hout.symm.trans hv)
  simpa [huv] using hterm

/-- Distinct retained source terminals cannot coalesce under pruning. -/
theorem distinct_retained_terminals (p : α → Bool)
    (s t u v : PrefRouter α)
    (hs : p (terminal s) = true) (ht : p (terminal t) = true)
    (hsu : prune p s = some u) (htv : prune p t = some v)
    (hne : terminal s ≠ terminal t) :
    terminal u ≠ terminal v := by
  rw [terminal_of_prune_eq_some p s u hs hsu,
    terminal_of_prune_eq_some p t v ht htv]
  exact hne

end PrefRouter

end ChaCha.PreferredProjection
