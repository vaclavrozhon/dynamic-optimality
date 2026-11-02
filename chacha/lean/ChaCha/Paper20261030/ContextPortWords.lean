import ChaCha.Paper20261030.ComponentPortWords
import ChaCha.Paper20261030.PreferredContext

/-!
# Exact port-list substitution in a preferred-path context

The fixed outside context contributes one port for each outside separator.
Replacing the middle component replaces exactly its complete port list;
the context's two lists of hanging subtrees are unchanged. Together with
the corresponding record-word theorem this characterizes component
equivalence independently of balancing shape.
-/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α κ : Type*} {β : κ → Type*} {right : Record (β := β) → Bool}

namespace ContextFrame

def beforePorts (frame : ContextFrame (α := α) right) : List (Source α (Record (β := β))) :=
  match frame with
  | .left .. => []
  | .right _ _ component .. => [closed component]

def afterPorts (frame : ContextFrame (α := α) right) : List (Source α (Record (β := β))) :=
  match frame with
  | .left _ _ component .. => [closed component]
  | .right .. => []

theorem portWord (frame : ContextFrame (α := α) right) (c : AuxiliaryComponent α κ (Tagged β)) :
    (frame.applyCore c).portWord = frame.beforePorts ++ c.portWord ++ frame.afterPorts := by
  cases frame <;> simp only [applyCore,append_portWord,prepend_portWord,beforePorts,afterPorts,
    List.nil_append,List.append_nil,List.singleton_append]

theorem beforePorts_length (frame : ContextFrame (α := α) right) :
    frame.beforePorts.length = frame.before.length := by cases frame <;> rfl

theorem afterPorts_length (frame : ContextFrame (α := α) right) :
    frame.afterPorts.length = frame.after.length := by cases frame <;> rfl

end ContextFrame

namespace PreferredContext

def beforePorts : List (ContextFrame (α := α) right) → List (Source α (Record (β := β)))
  | [] => []
  | frame :: rest => beforePorts rest ++ frame.beforePorts

def afterPorts : List (ContextFrame (α := α) right) → List (Source α (Record (β := β)))
  | [] => []
  | frame :: rest => frame.afterPorts ++ afterPorts rest

theorem portWord (c : AuxiliaryComponent α κ (Tagged β)) (frames : List (ContextFrame right)) :
    (wrap c frames).portWord = beforePorts frames ++ c.portWord ++ afterPorts frames := by
  induction frames generalizing c with
  | nil => simp [wrap,beforePorts,afterPorts]
  | cons frame rest ih => simp only [wrap,ih,ContextFrame.portWord,beforePorts,afterPorts,List.append_assoc]

theorem beforePorts_length (frames : List (ContextFrame (α := α) right)) :
    (beforePorts frames).length = (before frames).length := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simp only [beforePorts,before,List.length_append,ContextFrame.beforePorts_length,ih]

theorem afterPorts_length (frames : List (ContextFrame (α := α) right)) :
    (afterPorts frames).length = (after frames).length := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simp only [afterPorts,after,List.length_append,ContextFrame.afterPorts_length,ih]

theorem equivalent_of_context_words [Ord κ] (c sub : AuxiliaryComponent α κ (Tagged β))
    (frames : List (ContextFrame right))
    (hw : c.core.toListModel = before frames ++ sub.core.toListModel ++ after frames)
    (hp : c.portWord = beforePorts frames ++ sub.portWord ++ afterPorts frames) :
    Equivalent c (wrap sub frames) := by
  apply equivalent_of_words
  · rw [word]
    exact hw
  · rw [portWord]
    exact hp

end PreferredContext

end ChaCha.Paper20261030.PathDecomposition
