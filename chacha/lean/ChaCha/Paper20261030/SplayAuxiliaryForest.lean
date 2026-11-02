import ChaCha.Paper20261030.SplayAuxiliaryPotential
import MultiSplay.ForestSplayRun
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# One persistent potential for the complete auxiliary operation word

The forest consists of actual ordinary trees. Each event is the existing
standard splay search, splay-and-split, or raw join at an exposed separator.
Components may be reordered, split, and joined without restarting the
potential. The only invariant is distinct keys within each component and
the physical component-size cap; no cost estimate is an input.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)
open MultiSplay.CommonForest

variable {α : Type*}

def forestPotential (forest : List (RawTree α)) : Nat := (forest.map potential).sum

def forestSize (forest : List (RawTree α)) : Nat := (forest.map size).sum

def Valid (capacity : Nat) (forest : List (RawTree α)) : Prop :=
  ∀ tree ∈ forest, (inorder tree).Nodup ∧ size tree ≤ capacity

@[simp] theorem forestPotential_append (a b : List (RawTree α)) :
    forestPotential (a++b) = forestPotential a+forestPotential b := by
  simp [forestPotential]

theorem forestPotential_perm {a b : List (RawTree α)} (order : a.Perm b) :
    forestPotential a = forestPotential b := (order.map potential).sum_eq

theorem Valid.perm {capacity : Nat} {a b : List (RawTree α)}
    (valid : Valid capacity a) (order : a.Perm b) : Valid capacity b :=
  fun tree member => valid tree (order.mem_iff.mpr member)

theorem Valid.part {capacity : Nat} {whole part : List (RawTree α)}
    (valid : Valid capacity whole) (included : ∀ tree ∈ part, tree ∈ whole) : Valid capacity part :=
  fun tree member => valid tree (included tree member)

theorem forestPotential_le {capacity : Nat} {forest : List (RawTree α)} (valid : Valid capacity forest) :
    forestPotential forest ≤ forestSize forest * Nat.log 2 capacity := by
  induction forest with
  | nil => simp [forestPotential,forestSize]
  | cons tree tail ih =>
      have first := potential_le tree capacity (valid tree (by simp)).2
      have remaining := ih (valid.part (by intro t member; simp [member]))
      simp only [forestPotential,forestSize,List.map_cons,List.sum_cons] at *
      nlinarith

theorem primitive_amortized {capacity : Nat} {event : Event α} {before after : List (RawTree α)}
    {work : Nat} (operation : SplayPrimitive event before after work)
    (validBefore : Valid capacity before) (validAfter : Valid capacity after) :
    work+2*forestPotential after ≤ 2*forestPotential before+6*Nat.log 2 capacity+2 := by
  classical
  cases operation with
  | @search key before after rotations execution =>
      have valid := validBefore before (by simp)
      have bounded := splay_amortized_capacity execution valid.1 valid.2
      simpa only [forestPotential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Nat.add_zero] using (show rotations+1+2*potential after ≤
          2*potential before+6*Nat.log 2 capacity+2 by omega)
  | @split pivot before left right rotations execution =>
      have valid := validBefore before (by simp)
      have bounded := splay_amortized_capacity execution valid.1 valid.2
      simp only [potential] at bounded
      simp only [forestPotential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      omega
  | join left right pivot =>
      have valid := validAfter (.node left pivot right) (by simp)
      have bounded : rank (.node left pivot right) ≤ Nat.log 2 capacity :=
        Nat.log_mono_right valid.2
      simp only [forestPotential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,potential]
      omega

theorem action_amortized {capacity : Nat} {event : Event α} {before after : List (RawTree α)}
    {work : Nat} (operation : SplayAction event before after work)
    (validBefore : Valid capacity before) (validAfter : Valid capacity after) :
    work+2*forestPotential after ≤ 2*forestPotential before+6*Nat.log 2 capacity+2 := by
  obtain ⟨selected,returned,context,primitive,first,last⟩ := operation
  have before := validBefore.perm first
  have after := validAfter.perm last
  have bounded := primitive_amortized primitive
    (before.part (by intro tree member; exact List.mem_append_left _ member))
    (after.part (by intro tree member; exact List.mem_append_left _ member))
  rw [forestPotential_perm first,forestPotential_perm last,forestPotential_append,forestPotential_append]
  omega

theorem run_valid_before {capacity : Nat} {before after : List (RawTree α)}
    {word : List (Event α)} {work : Nat} (run : SplayRun (Valid capacity) before word after work) :
    Valid capacity before := by cases run <;> assumption

theorem run_valid_after {capacity : Nat} {before after : List (RawTree α)}
    {word : List (Event α)} {work : Nat} (run : SplayRun (Valid capacity) before word after work) :
    Valid capacity after := by
  induction run with
  | done valid order => exact valid.perm order
  | next valid action remaining ih => exact ih

/-- No component potential is reset when ownership or fragment membership changes. -/
theorem run_amortized {capacity : Nat} {before after : List (RawTree α)}
    {word : List (Event α)} {work : Nat} (run : SplayRun (Valid capacity) before word after work) :
    work+2*forestPotential after ≤
      2*forestPotential before+(6*Nat.log 2 capacity+2)*word.length := by
  induction run with
  | done valid order => simp [forestPotential_perm order]
  | @next before middle after event word head tail valid action remaining ih =>
      have first := action_amortized action valid (run_valid_before remaining)
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

/-- The persistent mixed-forest bound, charged once for the initial records. -/
theorem run_cost {capacity : Nat} {before after : List (RawTree α)}
    {word : List (Event α)} {work : Nat} (run : SplayRun (Valid capacity) before word after work) :
    work ≤ 2*forestSize before*Nat.log 2 capacity +
      (6*Nat.log 2 capacity+2)*word.length := by
  have bound := run_amortized run
  have initial := forestPotential_le (run_valid_before run)
  nlinarith

theorem run_cost_uniform {capacity : Nat} {before after : List (RawTree α)}
    {word : List (Event α)} {work : Nat} (run : SplayRun (Valid capacity) before word after work) :
    work ≤ 8*(forestSize before+word.length)*(Nat.clog 2 (capacity+1)+1) := by
  have bound := run_cost run
  have logarithm : Nat.log 2 capacity ≤ Nat.clog 2 (capacity+1) :=
    (Nat.log_le_clog 2 capacity).trans (Nat.clog_mono_right 2 (by omega))
  nlinarith

end ChaCha.Paper20261030.SplayAuxiliary
