import DynamicOptimality.Funnel.Alternation
import Mathlib.Tactic.CasesM

/-! # The five states of a common search-path prefix

A common prefix of searches for `y < x` contains only keys below `y`
(label `true`) or above `x` (label `false`). Splitting at either endpoint
retains precisely one of these labels. The three inequalities below are
Levy--Tarjan's local crossing charge, expressed only in terms of this prefix.
The finite transition checks are kernel reduction; the prefix itself has
arbitrary length and is handled by induction.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

private inductive PrefixState where
  | empty | onlyFalse | onlyTrue | bothFalse | bothTrue
  deriving DecidableEq

private def next : PrefixState → Bool → PrefixState
  | .empty, false => .onlyFalse
  | .empty, true => .onlyTrue
  | .onlyFalse, false => .onlyFalse
  | .onlyFalse, true => .bothTrue
  | .onlyTrue, false => .bothFalse
  | .onlyTrue, true => .onlyTrue
  | .bothFalse, false => .bothFalse
  | .bothFalse, true => .bothTrue
  | .bothTrue, false => .bothFalse
  | .bothTrue, true => .bothTrue

private def originalPrevious (boundary : Option Bool) : PrefixState → Option (Option Bool)
  | .empty => boundary.map some
  | .onlyFalse | .bothFalse => some (some false)
  | .onlyTrue | .bothTrue => some (some true)

private def plainPrevious : PrefixState → Option (Option Bool)
  | .empty => none
  | .onlyFalse | .bothFalse => some (some false)
  | .onlyTrue | .bothTrue => some (some true)

private def lowPrevious : PrefixState → Option (Option Bool)
  | .empty | .onlyFalse => none
  | .onlyTrue | .bothFalse | .bothTrue => some (some true)

private def highPrevious : PrefixState → Option (Option Bool)
  | .empty | .onlyTrue => some (some true)
  | .onlyFalse | .bothFalse | .bothTrue => some (some false)

private def credit (boundary : Option Bool) : PrefixState → Nat
  | .empty => changeStep boundary true
  | .onlyFalse => changeStep boundary true + 1 - changeStep boundary false
  | .onlyTrue => 0
  | .bothFalse => 4
  | .bothTrue => changeStep boundary true + 4 - changeStep boundary false

private theorem transition_credit : ∀ (boundary : Option Bool) (state : PrefixState) (b : Bool),
    changeStep (originalPrevious boundary state) (some b) +
      4 * (if b then changeStep (lowPrevious state) (some true) else 0) +
      credit boundary (next state b) ≤
    4 * changeStep (plainPrevious state) (some b) +
      (if b then 0 else changeStep (highPrevious state) (some false)) + credit boundary state  := by
  intros
  cases_type* PrefixState Option Bool <;> decide

private theorem fork_base : ∀ (boundary : Option Bool) (state : PrefixState),
    changeStep (originalPrevious boundary state) (some true) +
      4 * changeStep (lowPrevious state) (some false) ≤
    changeStep (highPrevious state) (some true) +
      4 * changeStep (plainPrevious state) (some false) + credit boundary state  := by
  intros
  cases_type* PrefixState Option Bool <;> decide

private theorem lower_base : ∀ (boundary : Option Bool) (state : PrefixState) (s : Option Bool),
    changeStep (originalPrevious boundary state) (some true) + changeStep (some (some true)) s +
      4 * changeStep (lowPrevious state) none ≤
    changeStep (highPrevious state) s +
      4 * changeStep (plainPrevious state) none + credit boundary state  := by
  intros
  cases_type* PrefixState Option Bool <;> decide

private theorem upper_base : ∀ (boundary : Option Bool) (state : PrefixState) (s : Option Bool),
    changeStep (originalPrevious boundary state) none +
      4 * changeStep (lowPrevious state) s ≤
    changeStep (highPrevious state) none +
      4 * (changeStep (plainPrevious state) (some false) + changeStep (some (some false)) s) +
      credit boundary state  := by
  intros
  cases_type* PrefixState Option Bool <;> decide

private def labels (p : List Bool) : List (Option Bool) := p.map some
private def low (p : List Bool) : List (Option Bool) := (p.filter id).map some
private def high (p : List Bool) : List (Option Bool) := (p.filter (! ·)).map some

private theorem fork_aux (boundary : Option Bool) (p : List Bool) (state : PrefixState) :
    changesFrom (originalPrevious boundary state) (labels p ++ [some true]) +
      4 * changesFrom (lowPrevious state) (low p ++ [some false]) ≤
    changesFrom (highPrevious state) (high p ++ [some true]) +
      4 * changesFrom (plainPrevious state) (labels p ++ [some false]) + credit boundary state := by
  induction p generalizing state with
  | nil => simpa [labels,low,high,changesFrom] using fork_base boundary state
  | cons b p ih =>
    have bound := ih (next state b)
    have step := transition_credit boundary state b
    cases state <;> cases b <;>
      simp only [labels,low,high,List.map_cons,List.filter_cons,List.cons_append,
        Bool.not_false,Bool.not_true,id_eq,Bool.true_eq,Bool.false_eq_true,↓reduceIte,changesFrom,next,originalPrevious,
        plainPrevious,lowPrevious,highPrevious] at bound step ⊢ <;> omega

private theorem lower_aux (boundary : Option Bool) (p : List Bool) (s : Option Bool)
    (state : PrefixState) :
    changesFrom (originalPrevious boundary state) (labels p ++ [some true,s]) +
      4 * changesFrom (lowPrevious state) (low p ++ [none]) ≤
    changesFrom (highPrevious state) (high p ++ [s]) +
      4 * changesFrom (plainPrevious state) (labels p ++ [none]) + credit boundary state := by
  induction p generalizing state with
  | nil => simpa [labels,low,high,changesFrom] using lower_base boundary state s
  | cons b p ih =>
    have bound := ih (next state b)
    have step := transition_credit boundary state b
    cases state <;> cases b <;>
      simp only [labels,low,high,List.map_cons,List.filter_cons,List.cons_append,
        Bool.not_false,Bool.not_true,id_eq,Bool.true_eq,Bool.false_eq_true,↓reduceIte,changesFrom,next,originalPrevious,
        plainPrevious,lowPrevious,highPrevious] at bound step ⊢ <;> omega

private theorem upper_aux (boundary : Option Bool) (p : List Bool) (s : Option Bool)
    (state : PrefixState) :
    changesFrom (originalPrevious boundary state) (labels p ++ [none]) +
      4 * changesFrom (lowPrevious state) (low p ++ [s]) ≤
    changesFrom (highPrevious state) (high p ++ [none]) +
      4 * changesFrom (plainPrevious state) (labels p ++ [some false,s]) + credit boundary state := by
  induction p generalizing state with
  | nil => simpa [labels,low,high,changesFrom] using upper_base boundary state s
  | cons b p ih =>
    have bound := ih (next state b)
    have step := transition_credit boundary state b
    cases state <;> cases b <;>
      simp only [labels,low,high,List.map_cons,List.filter_cons,List.cons_append,
        Bool.not_false,Bool.not_true,id_eq,Bool.true_eq,Bool.false_eq_true,↓reduceIte,changesFrom,next,originalPrevious,
        plainPrevious,lowPrevious,highPrevious] at bound step ⊢ <;> omega

/-- The searches diverge strictly between their two target keys. -/
theorem prefix_fork (boundary : Option Bool) (p : List Bool) :
    changesFrom (boundary.map some) (p.map some ++ [some true]) +
      4 * changes ((p.filter id).map some ++ [some false]) ≤
    changesFrom (boundary.map some) (some true :: (p.filter (! ·)).map some ++ [some true]) +
      4 * changes (p.map some ++ [some false]) := by
  have bound := fork_aux boundary p .empty
  cases boundary with
  | none => simpa [originalPrevious,lowPrevious,highPrevious,plainPrevious,credit,
      labels,low,high,changes,changesFrom,changeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
  | some b => cases b <;> simpa [originalPrevious,lowPrevious,highPrevious,plainPrevious,credit,
      labels,low,high,changes,changesFrom,changeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound

/-- The smaller target is an ancestor of the larger target. -/
theorem prefix_lower (boundary : Option Bool) (p : List Bool) (s : Option Bool) :
    changesFrom (boundary.map some) (p.map some ++ [some true,s]) +
      4 * changes ((p.filter id).map some ++ [none]) ≤
    changesFrom (boundary.map some) (some true :: (p.filter (! ·)).map some ++ [s]) +
      4 * changes (p.map some ++ [none]) := by
  have bound := lower_aux boundary p s .empty
  cases boundary with
  | none => simpa [originalPrevious,lowPrevious,highPrevious,plainPrevious,credit,
      labels,low,high,changes,changesFrom,changeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
  | some b => cases b <;> simpa [originalPrevious,lowPrevious,highPrevious,plainPrevious,credit,
      labels,low,high,changes,changesFrom,changeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound

/-- The larger target is an ancestor of the smaller target. -/
theorem prefix_upper (boundary : Option Bool) (p : List Bool) (s : Option Bool) :
    changesFrom (boundary.map some) (p.map some ++ [none]) +
      4 * changes ((p.filter id).map some ++ [s]) ≤
    changesFrom (boundary.map some) (some true :: (p.filter (! ·)).map some ++ [none]) +
      4 * changes (p.map some ++ [some false,s]) := by
  have bound := upper_aux boundary p s .empty
  cases boundary with
  | none => simpa [originalPrevious,lowPrevious,highPrevious,plainPrevious,credit,
      labels,low,high,changes,changesFrom,changeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
  | some b => cases b <;> simpa [originalPrevious,lowPrevious,highPrevious,plainPrevious,credit,
      labels,low,high,changes,changesFrom,changeStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound

end DynamicOptimality.Funnel.ApproxMonotonicity
