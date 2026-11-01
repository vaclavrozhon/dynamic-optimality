import TangoSquared.Paper20261030.SourceProgramRecordMap

set_option autoImplicit false

/-!
# Recovering tagged prepared boundaries from actual compiler outputs

The source compiler returns an identified tree and its erasure. These
lemmas recover the same boundary vertices and retained subtrees from that
output. No fresh ids or independently chosen tagged fragments are needed
when invoking the boundary observer and canonical head-input theorems.
-/

namespace TangoSquared.Paper20261030.IdentifiedBoundaryViews

open ColoredStorage

variable {α ρ ι : Type*}

theorem fork (source : Source α (ι × ρ)) (record : ρ) (left right : Source α ρ)
    (erases : source.mapRecords Prod.snd = .fork record left right) :
    ∃ ident, ∃ l r : Source α (ι × ρ), source = .fork (ident,record) l r ∧
      l.mapRecords Prod.snd = left ∧ r.mapRecords Prod.snd = right := by
  cases source with
  | leaf => cases erases
  | fork root l r =>
    cases root with
    | mk ident value =>
      simp only [Source.mapRecords,Source.fork.injEq] at erases
      obtain ⟨rfl,leftEq,rightEq⟩ := erases
      exact ⟨ident,l,r,rfl,leftEq,rightEq⟩

theorem leaf (source : Source α (ι × ρ)) (key : α) (record : ρ)
    (erases : source.mapRecords Prod.snd = .leaf key record) :
    ∃ ident, source = .leaf key (ident,record) := by
  cases source with
  | fork => cases erases
  | leaf actualKey root =>
    cases root with
    | mk ident value =>
      simp only [Source.mapRecords,Source.leaf.injEq] at erases
      obtain ⟨rfl,rfl⟩ := erases
      exact ⟨ident,rfl⟩

theorem sentinel (source : Source α (ι × ρ)) (high terminal : ρ) (key : α) (tail : Source α ρ)
    (erases : source.mapRecords Prod.snd = .fork high (.leaf key terminal) tail) :
    ∃ highId terminalId, ∃ taggedTail : Source α (ι × ρ),
      source = .fork (highId,high) (.leaf key (terminalId,terminal)) taggedTail ∧
      taggedTail.mapRecords Prod.snd = tail := by
  obtain ⟨highId,taggedTerminal,taggedTail,sourceEq,terminalEq,tailEq⟩ := fork source high (.leaf key terminal) tail erases
  obtain ⟨terminalId,rfl⟩ := leaf taggedTerminal key terminal terminalEq
  exact ⟨highId,terminalId,taggedTail,sourceEq,tailEq⟩

theorem active (source : Source α (ι × ρ)) (low high terminal : ρ) (key : α) (head tail : Source α ρ)
    (erases : source.mapRecords Prod.snd = .fork low head (.fork high (.leaf key terminal) tail)) :
    ∃ lowId highId terminalId, ∃ taggedHead taggedTail : Source α (ι × ρ),
      source = .fork (lowId,low) taggedHead (.fork (highId,high) (.leaf key (terminalId,terminal)) taggedTail) ∧
      taggedHead.mapRecords Prod.snd = head ∧ taggedTail.mapRecords Prod.snd = tail := by
  obtain ⟨lowId,taggedHead,taggedRest,sourceEq,headEq,restEq⟩ := fork source low head (.fork high (.leaf key terminal) tail) erases
  obtain ⟨highId,terminalId,taggedTail,rfl,tailEq⟩ := sentinel taggedRest high terminal key tail restEq
  exact ⟨lowId,highId,terminalId,taggedHead,taggedTail,sourceEq,headEq,tailEq⟩

end TangoSquared.Paper20261030.IdentifiedBoundaryViews
