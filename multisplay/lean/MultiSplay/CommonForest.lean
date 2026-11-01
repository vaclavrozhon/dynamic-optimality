import MultiSplay.AuxiliarySplay
import Mathlib.Data.List.Perm.Basic

/-!
# The common split/join word

An event specifies the ordered key domains, not the auxiliary tree shapes.
Both executions of a comparison must realize this same event word. A split
removes its pivot; a join inserts its pivot above the two existing children.
The component-list order is immaterial and may be permuted without changing
an event. Selection of a component is charged in the operation itself.

`access` and `prepare` are execution relations, not cost inequalities. The splay
instance below allows only standard splays and identity preparation. An offline
instance may use paid pointer rearrangements as preparation between events.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder size)

variable {α : Type*}

inductive Event (α : Type*) where
  | search (keys : List α) (key : α)
  | split (left : List α) (pivot : α) (right : List α)
  | join (left : List α) (pivot : α) (right : List α)

def Event.structural : Event α → Nat
  | .search _ _ => 0
  | .split _ _ _ => 1
  | .join _ _ _ => 1

def structuralCount (word : List (Event α)) : Nat :=
  (word.map Event.structural).sum

abbrev Access (α : Type*) := α → RawTree α → RawTree α → Nat → Prop
abbrev Preparation (α : Type*) := RawTree α → RawTree α → Nat → Prop

inductive Step (access : Access α) (prepare : Preparation α) :
    List (RawTree α) → List (Event α) → List (RawTree α) → Nat → Prop
  | search {key : α} {a b : RawTree α} {work : Nat}
      (execution : access key a b work) :
      Step access prepare [a] [.search (inorder a) key] [b] (work + 1)
  | split {pivot : α} {a l r : RawTree α} {work : Nat}
      (execution : access pivot a (.node l pivot r) work) :
      Step access prepare [a] [.split (inorder l) pivot (inorder r)] [l, r] (work + 1)
  | join (l r : RawTree α) (pivot : α) :
      Step access prepare [l, r] [.join (inorder l) pivot (inorder r)] [.node l pivot r] 1
  | prepare {a b : RawTree α} {work : Nat} (execution : prepare a b work) :
      Step access prepare [a] [] [b] work
  | context {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
      (step : Step access prepare a word b work) (front back : List (RawTree α)) :
      Step access prepare (front ++ a ++ back) word (front ++ b ++ back) work
  | reorder {a b : List (RawTree α)} (order : a.Perm b) : Step access prepare a [] b 0

inductive Trace (access : Access α) (prepare : Preparation α) :
    List (RawTree α) → List (Event α) → List (RawTree α) → Nat → Prop
  | nil (a : List (RawTree α)) : Trace access prepare a [] a 0
  | cons {a b c : List (RawTree α)} {first rest : List (Event α)} {head tail : Nat}
      (step : Step access prepare a first b head) (remaining : Trace access prepare b rest c tail) :
      Trace access prepare a (first ++ rest) c (head + tail)

theorem Trace.single {access : Access α} {prepare : Preparation α}
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (step : Step access prepare a word b work) : Trace access prepare a word b work := by
  simpa using Trace.cons step (Trace.nil b)

theorem Trace.append {access : Access α} {prepare : Preparation α}
    {a b c : List (RawTree α)} {first rest : List (Event α)} {head tail : Nat}
    (run₁ : Trace access prepare a first b head) (run₂ : Trace access prepare b rest c tail) :
    Trace access prepare a (first ++ rest) c (head + tail) := by
  induction run₁ with
  | nil => simpa using run₂
  | cons step remaining ih =>
      simpa [List.append_assoc, Nat.add_assoc] using Trace.cons step (ih run₂)

theorem Trace.context {access : Access α} {prepare : Preparation α}
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (run : Trace access prepare a word b work) (front back : List (RawTree α)) :
    Trace access prepare (front ++ a ++ back) word (front ++ b ++ back) work := by
  induction run with
  | nil => exact .nil _
  | cons step remaining ih => exact .cons (step.context front back) ih

def idle : Preparation α := fun a b work => a = b ∧ work = 0

abbrev SplayTrace := @Trace α Auxiliary.Splay idle

/-- Exactly three splits and three raw joins, written using their ordered
domains. The old left tail remains a separate component after the switch. -/
def leftToRightWord (a old incoming b : List α) (lower pivot upper : α) : List (Event α) :=
  [.split (a ++ [lower] ++ old) pivot ([upper] ++ b),
   .split a lower old,
   .split [] upper b,
   .join a lower [],
   .join incoming upper b,
   .join (a ++ [lower]) pivot (incoming ++ [upper] ++ b)]

theorem leftToRightWord_structural (a old incoming b : List α) (lower pivot upper : α) :
    structuralCount (leftToRightWord a old incoming b lower pivot upper) = 6 := by
  simp [structuralCount, leftToRightWord, Event.structural]

/-- The standard stopped guard splays are full splays of the two daughter
components after the pivot split. This statement retains their actual endpoint
shapes, not merely their key sets or their total costs. -/
theorem leftToRight_exact {whole left right a old incoming b : RawTree α}
    {lower pivot upper : α} {pivotWork leftWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
    (leftSplay : Auxiliary.Splay lower left (.node a lower old) leftWork)
    (rightSplay : Auxiliary.Splay upper right (.node .empty upper b) rightWork) :
    SplayTrace [whole, incoming]
      (leftToRightWord (inorder a) (inorder old) (inorder incoming) (inorder b) lower pivot upper)
      [.node (.node a lower .empty) pivot (.node incoming upper b), old]
      (pivotWork + leftWork + rightWork + 6) := by
  have first : SplayTrace [whole, incoming]
      [.split (inorder left) pivot (inorder right)] [left, right, incoming] (pivotWork + 1) := by
    simpa using (Trace.single (Step.split pivotSplay)).context [] [incoming]
  have second : SplayTrace [left, right, incoming]
      [.split (inorder a) lower (inorder old)] [a, old, right, incoming] (leftWork + 1) := by
    simpa using (Trace.single (Step.split leftSplay)).context [] [right, incoming]
  have third : SplayTrace [a, old, right, incoming]
      [.split [] upper (inorder b)] [a, old, .empty, b, incoming] (rightWork + 1) := by
    simpa [inorder] using (Trace.single (Step.split rightSplay)).context [a, old] [incoming]
  have order : ([a, old, .empty, b, incoming] : List (RawTree α)).Perm
      [a, .empty, incoming, b, old] := by
    have firstOrder : ([old, .empty, b, incoming] : List (RawTree α)).Perm
        [.empty, b, incoming, old] := by
      simpa using (List.perm_middle : ([.empty, b, incoming] ++ [old]).Perm
        (old :: [.empty, b, incoming])).symm
    have secondOrder : ([.empty, b, incoming, old] : List (RawTree α)).Perm
        [.empty, incoming, b, old] :=
      List.Perm.cons .empty (List.Perm.swap incoming b [old])
    exact List.Perm.cons a (firstOrder.trans secondOrder)
  have fourth : SplayTrace [a, .empty, incoming, b, old]
      [.join (inorder a) lower []] [.node a lower .empty, incoming, b, old] 1 := by
    simpa [inorder] using (Trace.single (Step.join a .empty lower)).context [] [incoming, b, old]
  have fifth : SplayTrace [.node a lower .empty, incoming, b, old]
      [.join (inorder incoming) upper (inorder b)]
      [.node a lower .empty, .node incoming upper b, old] 1 := by
    simpa using (Trace.single (Step.join incoming b upper)).context [.node a lower .empty] [old]
  have sixth : SplayTrace [.node a lower .empty, .node incoming upper b, old]
      [.join (inorder (.node a lower .empty)) pivot (inorder (.node incoming upper b))]
      [.node (.node a lower .empty) pivot (.node incoming upper b), old] 1 := by
    simpa using (Trace.single (Step.join (.node a lower .empty) (.node incoming upper b) pivot)).context [] [old]
  have total := first.append (second.append (third.append
    ((Trace.single (Step.reorder order)).append (fourth.append (fifth.append sixth)))))
  have leftKeys := leftSplay.inorder_eq
  have rightKeys := rightSplay.inorder_eq
  simpa [leftToRightWord, leftKeys, rightKeys, inorder, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using total

end MultiSplay.CommonForest
