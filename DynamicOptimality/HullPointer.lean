import DynamicOptimality.Basic

/-! Concrete simulation of the existing rooted-hull model in the shared
adjacent-pointer model. Both models are reused from the Cha-Cha library. -/

namespace DynamicOptimality

open ChaCha ChaCha.MTR ChaCha.MTR.Pointer
open ChaCha.Paper20261030.Auxiliary

variable {α : Type*}

theorem restricted_pointer {a b : RawTree α} (step : MTR.Tree.RestrictedStep a b) :
    Rearranges a b 3 := by
  intro ancestors
  cases step with
  | rootRight a b c x y =>
    exact ⟨1,.step (.rotateRight a b c x y ancestors) (.nil _),by decide⟩
  | rootLeft a b c x y =>
    exact ⟨1,.step (.rotateLeft a b c x y ancestors) (.nil _),by decide⟩
  | rightRight a b c d x y z =>
    exact ⟨3,.step (.right a (.node b y c) d x z ancestors)
      (.step (.rotateRight b c d y z (.right a x :: ancestors))
        (.step (.upRight a (.node b y (.node c z d)) x ancestors) (.nil _))),le_rfl⟩
  | rightLeft a b c d x y z =>
    exact ⟨3,.step (.right a b (.node c z d) x y ancestors)
      (.step (.rotateLeft b c d y z (.right a x :: ancestors))
        (.step (.upRight a (.node (.node b y c) z d) x ancestors) (.nil _))),le_rfl⟩
  | leftRight a b c d x y z =>
    exact ⟨3,.step (.left (.node a x b) c d y z ancestors)
      (.step (.rotateRight a b c x y (.left z d :: ancestors))
        (.step (.upLeft (.node a x (.node b y c)) d z ancestors) (.nil _))),le_rfl⟩
  | leftLeft a b c d x y z =>
    exact ⟨3,.step (.left a (.node b y c) d x z ancestors)
      (.step (.rotateLeft a b c x y (.left z d :: ancestors))
        (.step (.upLeft (.node (.node a x b) y c) d z ancestors) (.nil _))),le_rfl⟩

theorem marked_pointer_trace {a b : RawTree α} {word : List α} {rotations : Nat}
    (trace : MarkedTrace a word b rotations) :
    ∃ cost, Pointer.Trace (.atRoot a) word (.atRoot b) cost ∧
      cost ≤ 3 * rotations + word.length := by
  induction trace with
  | nil => exact ⟨0,.nil _,le_rfl⟩
  | rotate step rest ih =>
    obtain ⟨rc,rt,hr⟩ := restricted_pointer step []
    obtain ⟨tc,tt,ht⟩ := ih
    exact ⟨rc + tc,by simpa only [List.nil_append,Pointer.Cursor.atRoot] using trace_append rt tt,by omega⟩
  | serve atRoot rest ih =>
    obtain ⟨cost,trace,hc⟩ := ih
    exact ⟨cost + 1,.serve atRoot trace,by simp only [List.length_cons]; omega⟩

theorem hullAccess_pointer [LinearOrder α] {x : α} {a b : RawTree α}
    (access : HullAccess x a b) (ordered : MTR.Tree.Ordered a) :
    ∃ cost, Pointer.Access x a b cost ∧ cost ≤ 37 * access.cost := by
  obtain ⟨rotations,hr,trace⟩ := access.marked_trace ordered
  obtain ⟨cost,trace,hc⟩ := marked_pointer_trace trace
  have hp := access.cost_pos
  refine ⟨cost,⟨.atRoot b,rfl,trace⟩,?_⟩
  simp only [List.length_singleton] at hc
  omega

theorem accessExecution_pointer [LinearOrder α] {a b : RawTree α} {word : List α} {hullCost : Nat}
    (execution : AccessExecution a word b hullCost) (ordered : MTR.Tree.Ordered a) :
    ∃ cost, Pointer.Execution a word b cost ∧ cost ≤ 37 * hullCost := by
  induction execution with
  | nil => exact ⟨0,.nil _,le_rfl⟩
  | cons access rest ih =>
    obtain ⟨hc,ht,hh⟩ := hullAccess_pointer access ordered
    obtain ⟨tc,tt,th⟩ := ih (access.ordered_after ordered)
    exact ⟨hc + tc,.cons ht tt,by omega⟩

end DynamicOptimality
