import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic
import Lean.Elab.Tactic.Omega

/-!
# Persistent forest accounting

The list order of components is bookkeeping: selecting a component is handled
by the concrete execution model, not by traversing this list. A local rewrite
retains every component outside its displayed input. Its two natural-number
indices record actual cost and amortized allowance, respectively.

The result charges the initial forest once. In particular, splitting a component
does not charge the sizes of the two surviving representations as new input.
-/

namespace MultiSplay.Forest

variable {α : Type*}

def potential (φ : α → Nat) (forest : List α) : Nat :=
  (forest.map φ).sum

@[simp] theorem potential_nil (φ : α → Nat) : potential φ [] = 0 := rfl

@[simp] theorem potential_cons (φ : α → Nat) (a : α) (forest : List α) :
    potential φ (a :: forest) = φ a + potential φ forest := by
  simp [potential]

@[simp] theorem potential_append (φ : α → Nat) (a b : List α) :
    potential φ (a ++ b) = potential φ a + potential φ b := by
  simp [potential]

theorem potential_perm (φ : α → Nat) {a b : List α} (h : a.Perm b) :
    potential φ a = potential φ b :=
  (h.map φ).sum_eq

/-- A concrete local operation may replace several selected components.
The surrounding components retain their actual states. -/
inductive Step (rule : List α → List α → Nat → Nat → Prop) :
    List α → List α → Nat → Nat → Prop
  | replace {a b : List α} {cost allowance : Nat}
      (operation : rule a b cost allowance) (front back : List α) :
      Step rule (front ++ a ++ back) (front ++ b ++ back) cost allowance
  | reorder {a b : List α} (order : a.Perm b) : Step rule a b 0 0

/-- Chronological composition; no potential is restarted at a local operation. -/
inductive Trace (rule : List α → List α → Nat → Nat → Prop) :
    List α → List α → Nat → Nat → Prop
  | nil (a : List α) : Trace rule a a 0 0
  | cons {a b c : List α} {cost₁ cost₂ allowance₁ allowance₂ : Nat}
      (head : Step rule a b cost₁ allowance₁)
      (tail : Trace rule b c cost₂ allowance₂) :
      Trace rule a c (cost₁ + cost₂) (allowance₁ + allowance₂)

def LocallyAmortized (φ : α → Nat)
    (rule : List α → List α → Nat → Nat → Prop) : Prop :=
  ∀ ⦃a b cost allowance⦄, rule a b cost allowance →
    cost + potential φ b ≤ potential φ a + allowance

theorem Step.amortized {φ : α → Nat}
    {rule : List α → List α → Nat → Nat → Prop}
    (bound : LocallyAmortized φ rule) {a b : List α} {cost allowance : Nat}
    (step : Step rule a b cost allowance) :
    cost + potential φ b ≤ potential φ a + allowance := by
  cases step with
  | replace operation front back =>
      have h := bound operation
      simp only [potential_append]
      omega
  | reorder order =>
      have h := potential_perm φ order
      omega

theorem Trace.amortized {φ : α → Nat}
    {rule : List α → List α → Nat → Nat → Prop}
    (bound : LocallyAmortized φ rule) {a b : List α} {cost allowance : Nat}
    (trace : Trace rule a b cost allowance) :
    cost + potential φ b ≤ potential φ a + allowance := by
  induction trace with
  | nil => omega
  | cons head tail ih =>
      have h := head.amortized bound
      omega

theorem Trace.cost_le {φ : α → Nat}
    {rule : List α → List α → Nat → Nat → Prop}
    (bound : LocallyAmortized φ rule) {a b : List α} {cost allowance : Nat}
    (trace : Trace rule a b cost allowance) :
    cost ≤ potential φ a + allowance := by
  have h := trace.amortized bound
  omega

theorem potential_le_size (φ size : α → Nat) (constant : Nat)
    (bound : ∀ a, φ a ≤ constant * size a) (forest : List α) :
    potential φ forest ≤ constant * potential size forest := by
  induction forest with
  | nil => simp
  | cons a rest ih =>
      simp only [potential_cons, Nat.mul_add]
      exact Nat.add_le_add (bound a) ih

/-- The only size term is that of the initial forest, irrespective of the
number or sizes of components subsequently created by splits and joins. -/
theorem Trace.cost_le_initial_size {φ size : α → Nat} {constant : Nat}
    {rule : List α → List α → Nat → Nat → Prop}
    (bound : LocallyAmortized φ rule)
    (initialBound : ∀ a, φ a ≤ constant * size a)
    {a b : List α} {cost allowance : Nat} (trace : Trace rule a b cost allowance) :
    cost ≤ constant * potential size a + allowance := by
  have h := trace.cost_le bound
  have h' := potential_le_size φ size constant initialBound a
  omega

end MultiSplay.Forest
