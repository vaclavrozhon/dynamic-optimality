import ChaCha.Paper20261030.PathDecomposition

/-!
# The unchanged context of a preferred-path descendant

A context frame records one preferred ancestor and the represented
nonpreferred sibling. Rewrapping a replacement component is a semantic
construction: the physical cost is supplied separately by interval
replacement. Its word consists of a fixed prefix, the replacement word,
and a fixed suffix. The replacement's gap ports occupy exactly the
intervening port window, with no dependence on balancing shape.
-/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α κ : Type*} {β : κ → Type*}

inductive ContextFrame (right : Record (β := β) → Bool)
  | left (record : Record (β := β)) (sibling : Source α (Record (β := β)))
      (component : AuxiliaryComponent α κ (Tagged β))
      (clean : entry record = false) (direction : right record = false)
      (represented : Represents right sibling component)
  | right (record : Record (β := β)) (sibling : Source α (Record (β := β)))
      (component : AuxiliaryComponent α κ (Tagged β))
      (clean : entry record = false) (direction : right record = true)
      (represented : Represents right sibling component)

namespace ContextFrame

variable {right : Record (β := β) → Bool}

def applyCore (frame : ContextFrame (α := α) right) (c : AuxiliaryComponent α κ (Tagged β)) :=
  match frame with
  | .left record _ sibling _ _ _ => append c record.2.1 record.2.2 (closed sibling)
  | .right record _ sibling _ _ _ => prepend record.2.1 record.2.2 (closed sibling) c

def applyReference (frame : ContextFrame (α := α) right) (source : Source α (Record (β := β))) :=
  match frame with
  | .left record sibling _ _ _ _ => Source.fork record source sibling
  | .right record sibling _ _ _ _ => Source.fork record sibling source

def before (frame : ContextFrame (α := α) right) : List (Sigma (Tagged β)) :=
  match frame with
  | .left .. => []
  | .right record .. => [record.2]

def after (frame : ContextFrame (α := α) right) : List (Sigma (Tagged β)) :=
  match frame with
  | .left record .. => [record.2]
  | .right .. => []

theorem size (frame : ContextFrame (α := α) right) (c : AuxiliaryComponent α κ (Tagged β)) :
    (frame.applyCore c).core.size = c.core.size + 1 := by
  cases frame <;> simp only [applyCore,append_size,prepend_size]

theorem word [Ord κ] (frame : ContextFrame (α := α) right) (c : AuxiliaryComponent α κ (Tagged β)) :
    (frame.applyCore c).core.toListModel = frame.before ++ c.core.toListModel ++ frame.after := by
  cases frame <;> simp only [applyCore,append_word,prepend_word,before,after,List.nil_append,
    List.append_nil,List.singleton_append]

theorem before_length (frame : ContextFrame (α := α) right) : frame.before.length ≤ 1 := by
  cases frame <;> simp [before]

theorem port_window (frame : ContextFrame (α := α) right) (c : AuxiliaryComponent α κ (Tagged β))
    (i : Nat) (hi : i ≤ c.core.size) :
    (frame.applyCore c).ports (frame.before.length + i) = c.ports i := by
  cases frame with
  | left => simp only [applyCore,before,List.length_nil,Nat.zero_add,append,if_pos hi]
  | right => simp [applyCore,before,prepend,Nat.add_comm]

theorem represents (frame : ContextFrame (α := α) right)
    {source : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right source c) : Represents right (frame.applyReference source) (frame.applyCore c) := by
  cases frame with
  | left record sibling component clean direction represented =>
    exact .left direction clean h represented (.refl _)
  | right record sibling component clean direction represented =>
    exact .right direction clean represented h (.refl _)

theorem equivalent [Ord κ] (frame : ContextFrame (α := α) right)
    {a b : AuxiliaryComponent α κ (Tagged β)} (h : Equivalent a b) :
    Equivalent (frame.applyCore a) (frame.applyCore b) := by
  cases frame with
  | left => exact h.append _ _ _
  | right => exact h.prepend _ _ _

end ContextFrame

namespace PreferredContext

variable {right : Record (β := β) → Bool}

def wrap (c : AuxiliaryComponent α κ (Tagged β)) : List (ContextFrame (α := α) right) → AuxiliaryComponent α κ (Tagged β)
  | [] => c
  | frame :: rest => wrap (frame.applyCore c) rest

def plug (source : Source α (Record (β := β))) : List (ContextFrame (α := α) right) → Source α (Record (β := β))
  | [] => source
  | frame :: rest => plug (frame.applyReference source) rest

def before : List (ContextFrame (α := α) right) → List (Sigma (Tagged β))
  | [] => []
  | frame :: rest => before rest ++ frame.before

def after : List (ContextFrame (α := α) right) → List (Sigma (Tagged β))
  | [] => []
  | frame :: rest => frame.after ++ after rest

theorem wrap_append (c : AuxiliaryComponent α κ (Tagged β)) (a b : List (ContextFrame right)) :
    wrap c (a ++ b) = wrap (wrap c a) b := by
  induction a generalizing c with
  | nil => rfl
  | cons frame rest ih => exact ih (frame.applyCore c)

theorem plug_append (source : Source α (Record (β := β))) (a b : List (ContextFrame right)) :
    plug source (a ++ b) = plug (plug source a) b := by
  induction a generalizing source with
  | nil => rfl
  | cons frame rest ih => exact ih (frame.applyReference source)

theorem before_append (a b : List (ContextFrame (α := α) right)) :
    before (a ++ b) = before b ++ before a := by
  induction a with
  | nil => simp [before]
  | cons frame rest ih => simp only [List.cons_append,before,ih,List.append_assoc]

theorem after_append (a b : List (ContextFrame (α := α) right)) :
    after (a ++ b) = after a ++ after b := by
  induction a with
  | nil => simp [after]
  | cons frame rest ih => simp only [List.cons_append,after,ih,List.append_assoc]

theorem size (c : AuxiliaryComponent α κ (Tagged β)) (frames : List (ContextFrame right)) :
    (wrap c frames).core.size = c.core.size + frames.length := by
  induction frames generalizing c with
  | nil => simp [wrap]
  | cons frame rest ih => simp only [wrap,ih,ContextFrame.size,List.length_cons]; omega

theorem word [Ord κ] (c : AuxiliaryComponent α κ (Tagged β)) (frames : List (ContextFrame right)) :
    (wrap c frames).core.toListModel = before frames ++ c.core.toListModel ++ after frames := by
  induction frames generalizing c with
  | nil => simp [wrap,before,after]
  | cons frame rest ih => simp only [wrap,ih,ContextFrame.word,before,after,List.append_assoc]

theorem before_length (frames : List (ContextFrame (α := α) right)) :
    (before frames).length ≤ frames.length := by
  induction frames with
  | nil => simp [before]
  | cons frame rest ih =>
    have hf := frame.before_length
    simp only [before,List.length_append,List.length_cons]
    omega

theorem port_window (c : AuxiliaryComponent α κ (Tagged β)) (frames : List (ContextFrame right))
    (i : Nat) (hi : i ≤ c.core.size) :
    (wrap c frames).ports ((before frames).length + i) = c.ports i := by
  induction frames generalizing c i with
  | nil => simp [wrap,before]
  | cons frame rest ih =>
    have hb : frame.before.length + i ≤ (frame.applyCore c).core.size := by
      rw [frame.size]
      have := frame.before_length
      omega
    have hw := ih (frame.applyCore c) (frame.before.length + i) hb
    simp only [wrap,before,List.length_append,Nat.add_assoc]
    exact hw.trans (frame.port_window c i hi)

theorem represents (frames : List (ContextFrame (α := α) right))
    {source : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right source c) : Represents right (plug source frames) (wrap c frames) := by
  induction frames generalizing source c with
  | nil => exact h
  | cons frame rest ih => exact ih (frame.represents h)

theorem equivalent [Ord κ] (frames : List (ContextFrame (α := α) right))
    {a b : AuxiliaryComponent α κ (Tagged β)} (h : Equivalent a b) :
    Equivalent (wrap a frames) (wrap b frames) := by
  induction frames generalizing a b with
  | nil => exact h
  | cons frame rest ih => exact ih (frame.equivalent h)

end PreferredContext

end ChaCha.Paper20261030.PathDecomposition
