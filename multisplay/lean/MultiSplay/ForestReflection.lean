import MultiSplay.CommonForest
import MultiSplay.AuxiliaryReflection

/-! Reflection preserves the exact common operation word and its cost.
It includes the component permutations required at split and join boundaries. -/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open Auxiliary (mirror inorder_mirror)
open ChaCha.MTR.Tree (inorder)

variable {α : Type*}

def Event.mirror : Event α → Event α
  | .search keys key => .search keys.reverse key
  | .split left pivot right => .split right.reverse pivot left.reverse
  | .join left pivot right => .join right.reverse pivot left.reverse

@[simp] theorem Event.mirror_mirror (event : Event α) : event.mirror.mirror = event := by
  cases event <;> simp [Event.mirror]

@[simp] theorem Event.structural_mirror (event : Event α) : event.mirror.structural = event.structural := by
  cases event <;> rfl

theorem structuralCount_mirror (word : List (Event α)) :
    structuralCount (word.map Event.mirror) = structuralCount word := by
  simp [structuralCount, List.map_map, Function.comp_def]

theorem Step.mirror_trace {access : Access α} {prepare : Preparation α}
    (accessMirror : ∀ ⦃key a b work⦄, access key a b work → access key (mirror a) (mirror b) work)
    (prepareMirror : ∀ ⦃a b work⦄, prepare a b work → prepare (mirror a) (mirror b) work)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (step : Step access prepare a word b work) :
    Trace access prepare (a.map mirror) (word.map Event.mirror) (b.map mirror) work := by
  induction step with
  | search execution =>
      simpa [Event.mirror, inorder_mirror] using Trace.single (Step.search (accessMirror execution))
  | @split pivot a l r work execution =>
      have first : Trace access prepare [mirror a]
          [.split (inorder (mirror r)) pivot (inorder (mirror l))] [mirror r, mirror l] (work + 1) :=
        Trace.single (Step.split (accessMirror execution))
      have order : [mirror r, mirror l].Perm [mirror l, mirror r] := List.Perm.swap _ _ []
      simpa [Event.mirror, inorder_mirror] using first.append (Trace.single (Step.reorder order))
  | join l r pivot =>
      have order : [mirror l, mirror r].Perm [mirror r, mirror l] := List.Perm.swap _ _ []
      have first : Trace access prepare [mirror l, mirror r] [] [mirror r, mirror l] 0 :=
        Trace.single (Step.reorder order)
      simpa [Event.mirror, mirror, inorder_mirror] using
        first.append (Trace.single (Step.join (mirror r) (mirror l) pivot))
  | prepare execution =>
      simpa using Trace.single (Step.prepare (prepareMirror execution))
  | context step front back ih =>
      simpa only [List.map_append] using ih.context (front.map mirror) (back.map mirror)
  | reorder order =>
      exact Trace.single (Step.reorder (order.map mirror))

theorem Trace.mirror {access : Access α} {prepare : Preparation α}
    (accessMirror : ∀ ⦃key a b work⦄, access key a b work → access key (mirror a) (mirror b) work)
    (prepareMirror : ∀ ⦃a b work⦄, prepare a b work → prepare (mirror a) (mirror b) work)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (run : Trace access prepare a word b work) :
    Trace access prepare (a.map mirror) (word.map Event.mirror) (b.map mirror) work := by
  induction run with
  | nil => exact .nil _
  | cons step remaining ih =>
      simpa only [List.map_append] using (step.mirror_trace accessMirror prepareMirror).append ih

theorem SplayTrace.mirror {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (run : SplayTrace a word b work) :
    SplayTrace (a.map mirror) (word.map Event.mirror) (b.map mirror) work := by
  apply Trace.mirror (access := Auxiliary.Splay) (prepare := idle)
    (fun {_ _ _ _} execution => Auxiliary.Splay.mirror execution) ?_ run
  intro a b work h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

def rightToLeftWord (a incoming old b : List α) (lower pivot upper : α) : List (Event α) :=
  [.split (a ++ [lower]) pivot (old ++ [upper] ++ b),
   .split old upper b, .split a lower [], .join [] upper b,
   .join a lower incoming, .join (a ++ [lower] ++ incoming) pivot ([upper] ++ b)]

theorem rightToLeft_exact {whole left right a incoming old b : RawTree α}
    {lower pivot upper : α} {pivotWork leftWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
    (upperSplay : Auxiliary.Splay upper right (.node old upper b) rightWork)
    (lowerSplay : Auxiliary.Splay lower left (.node a lower .empty) leftWork) :
    SplayTrace [whole, incoming]
      (rightToLeftWord (inorder a) (inorder incoming) (inorder old) (inorder b) lower pivot upper)
      [.node (.node a lower incoming) pivot (.node .empty upper b), old]
      (pivotWork + rightWork + leftWork + 6) := by
  have reflected := leftToRight_exact (incoming := mirror incoming)
    pivotSplay.mirror upperSplay.mirror lowerSplay.mirror
  have twice := SplayTrace.mirror reflected
  simpa [leftToRightWord, rightToLeftWord, Event.mirror, mirror, inorder_mirror,
    List.reverse_append, List.append_assoc, inorder] using twice

end MultiSplay.CommonForest
