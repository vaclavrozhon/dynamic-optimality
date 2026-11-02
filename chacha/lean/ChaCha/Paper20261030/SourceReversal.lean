import ChaCha.Paper20261030.SourceNavigation

/-! Reversing an actual record-decorated pointer trace retains its cost.
Reads are performed again at the reached vertices; their resulting word
need not be the reversal of the original observation word. -/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

theorem Step.symm {c d : Cursor α ρ} (h : Step c d) : Step d c := by
  cases h with
  | left => exact .upLeft _ _ _ _
  | right => exact .upRight _ _ _ _
  | upLeft => exact .left _ _ _ _
  | upRight => exact .right _ _ _ _
  | rotateRight => exact .rotateLeft _ _ _ _ _ _
  | rotateLeft => exact .rotateRight _ _ _ _ _ _
  | write focus fresh rest =>
    have he : (focus.setRoot fresh).setRoot focus.rootRecord = focus := by cases focus <;> rfl
    simpa only [he] using Step.write (focus.setRoot fresh) focus.rootRecord rest

theorem Trace.reverse {c d : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (h : Trace c reads d cost) : ∃ observations, Trace d observations c cost := by
  induction h with
  | nil c => exact ⟨[],.nil c⟩
  | step move rest ih =>
    obtain ⟨observations,reverse⟩ := ih
    exact ⟨_,reverse.append (.step move.symm (.nil _))⟩
  | read rest ih =>
    obtain ⟨observations,reverse⟩ := ih
    exact ⟨_,reverse.append (.read (.nil _))⟩

theorem Rearranges.symm {a b : Source α ρ} {budget : Nat}
    (h : Rearranges a b budget) : Rearranges b a budget := by
  intro rest
  obtain ⟨reads,cost,trace,hcost⟩ := h rest
  obtain ⟨observations,reverse⟩ := trace.reverse
  exact ⟨observations,cost,reverse,hcost⟩

end ChaCha.Paper20261030.SourcePointer

namespace ChaCha.Paper20261030.ProjectionLocal

variable {α ρ : Type*}

theorem Rearranges.symm {a b : Projected α ρ} {budget : Nat}
    (h : Rearranges a b budget) : Rearranges b a budget := by
  cases a <;> cases b
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact SourcePointer.Rearranges.symm h

end ChaCha.Paper20261030.ProjectionLocal
