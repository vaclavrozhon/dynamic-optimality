import ChaCha.Paper20261030.StructuralRotationReads
import ChaCha.Paper20261030.PackedPortAgreement
import ChaCha.Paper20261030.IdentifiedHeadExchange

/-!
# Computing the five logical boundary records of a head switch

Each stored child descriptor contains an identifier and a color mask.
The exposed active source has two pivots and one terminal; the incoming
source has one pivot and one terminal. Moving the incoming boundary into
the active source changes these five records. The prefix and the two
tails keep their parents, and their leaf colors agree before and after.

`repair` consumes only these five records and the two new terminal colors.
It does not inspect a tree or receive a subtree oracle. `repair_exact`
proves the resulting fields are the exact structural annotations of the
new source views. Physical acquisition, packing, and installation of
these records remain separate operations.
-/

namespace ChaCha.Paper20261030.Structural

open ColoredStorage RouterProjection

variable {α ρ ι C : Type*} [LinearOrder C]

theorem descriptor_color_congr (identifier : ρ → ι) (source : Source α ρ)
    (before after : α → C) (same : ∀ key ∈ source.shape.leaves, before key = after key) :
    descriptor identifier before source = descriptor identifier after source := by
  simp only [descriptor,source.support_congr before after same]

theorem fields_color_congr (identifier : ρ → ι) (source : Source α ρ) (parent : Option ι)
    (before after : α → C) (same : ∀ key ∈ source.shape.leaves, before key = after key) :
    fields identifier before parent source = fields identifier after parent source := by
  cases source with
  | leaf key record =>
    have equal := same key (by simp only [Source.shape,Router.leaves,List.mem_singleton])
    simp only [fields,Source.support,equal]
  | fork record left right =>
    have leftSame := fun key member => same key (List.mem_append_left right.shape.leaves member)
    have rightSame := fun key member => same key (List.mem_append_right left.shape.leaves member)
    simp only [fields,Source.support,left.support_congr before after leftSame,
      right.support_congr before after rightSame,descriptor_color_congr identifier left before after leftSame,
      descriptor_color_congr identifier right before after rightSame]

theorem annotate_color_congr (identifier : ρ → ι) (source : Source α ρ) (parent : Option ι)
    (before after : α → C) (same : ∀ key ∈ source.shape.leaves, before key = after key) :
    annotate identifier before parent source = annotate identifier after parent source := by
  induction source generalizing parent with
  | leaf key record =>
    simp only [annotate,fields_color_congr identifier (.leaf key record) parent before after same]
  | fork record left right ihl ihr =>
    have leftSame := fun key member => same key (List.mem_append_left right.shape.leaves member)
    have rightSame := fun key member => same key (List.mem_append_right left.shape.leaves member)
    simp only [annotate,fields_color_congr identifier (.fork record left right) parent before after same,
      ihl _ leftSame,ihr _ rightSame]

namespace HeadBoundary

abbrev Record (ρ ι C : Type*) := ρ × Fields ι C

structure Records (ρ ι C : Type*) where
  low : Record ρ ι C
  oldHigh : Record ρ ι C
  incomingHigh : Record ρ ι C
  oldTerminal : Record ρ ι C
  incomingTerminal : Record ρ ι C

def observed (identifier : ρ → ι) (activeColor incomingColor : α → C)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (prefixTree oldTail incomingTail : Source α ρ) : Records ρ ι C :=
  let oldBoundary := Source.fork oldHigh (.leaf depth oldTerminal) oldTail
  let incomingBoundary := Source.fork incomingHigh (.leaf depth incomingTerminal) incomingTail
  ⟨(low,fields identifier activeColor none (.fork low prefixTree oldBoundary)),
    (oldHigh,fields identifier activeColor (some (identifier low)) oldBoundary),
    (incomingHigh,fields identifier incomingColor none incomingBoundary),
    (oldTerminal,fields identifier activeColor (some (identifier oldHigh)) (.leaf depth oldTerminal)),
    (incomingTerminal,fields identifier incomingColor (some (identifier incomingHigh)) (.leaf depth incomingTerminal))⟩

def storedDescriptor (identifier : ρ → ι) (record : Record ρ ι C) : Child ι C :=
  ⟨identifier record.1,record.2.colors⟩

def terminal (parent : ι) (color : C) (record : Record ρ ι C) : Record ρ ι C :=
  (record.1,⟨some parent,{color},none⟩)

def branch (parent : Option ι) (record : Record ρ ι C) (left right : Child ι C) : Record ρ ι C :=
  (record.1,⟨parent,left.colors ∪ right.colors,some (left,right)⟩)

def repair (identifier : ρ → ι) (oldTerminalColor incomingTerminalColor : C)
    (records : Records ρ ι C) : Option (Records ρ ι C) :=
  match records.low.2.children,records.oldHigh.2.children,records.incomingHigh.2.children with
  | some (prefixChild,_),some (_,oldTailChild),some (_,incomingTailChild) =>
    let oldTerminal := terminal (identifier records.oldHigh.1) oldTerminalColor records.oldTerminal
    let incomingTerminal := terminal (identifier records.incomingHigh.1) incomingTerminalColor records.incomingTerminal
    let oldHigh := branch none records.oldHigh (storedDescriptor identifier oldTerminal) oldTailChild
    let incomingHigh := branch (some (identifier records.low.1)) records.incomingHigh
      (storedDescriptor identifier incomingTerminal) incomingTailChild
    let low := branch none records.low prefixChild (storedDescriptor identifier incomingHigh)
    some ⟨low,oldHigh,incomingHigh,oldTerminal,incomingTerminal⟩
  | _,_,_ => none

/-- Output fields use the new active and dormant color functions. The
three agreement hypotheses concern only the untouched block interiors. -/
theorem repair_exact (identifier : ρ → ι) (oldColor incomingColor newColor dormantColor : α → C)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (prefixTree oldTail incomingTail : Source α ρ)
    (prefixColors : ∀ key ∈ prefixTree.shape.leaves, oldColor key = newColor key)
    (oldColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key)
    (incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key) :
    repair identifier (dormantColor depth) (newColor depth)
      (observed identifier oldColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
        depth prefixTree oldTail incomingTail) =
      some {
        low := (low,fields identifier newColor none
          (.fork low prefixTree (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))
        oldHigh := (oldHigh,fields identifier dormantColor none
          (.fork oldHigh (.leaf depth oldTerminal) oldTail))
        incomingHigh := (incomingHigh,fields identifier newColor (some (identifier low))
          (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))
        oldTerminal := (oldTerminal,fields identifier dormantColor (some (identifier oldHigh)) (.leaf depth oldTerminal))
        incomingTerminal := (incomingTerminal,fields identifier newColor (some (identifier incomingHigh)) (.leaf depth incomingTerminal)) } := by
  simp only [repair,observed,fields,terminal,branch,storedDescriptor,
    descriptor,Source.rootRecord,Source.support,
    prefixTree.support_congr oldColor newColor prefixColors,
    oldTail.support_congr oldColor dormantColor oldColors,
    incomingTail.support_congr incomingColor newColor incomingColors]

/-- No internal record of any transferred block needs rewriting. Even
the parent identifier of each block root stays the same. -/
theorem blocks_unchanged (identifier : ρ → ι) (oldColor incomingColor newColor dormantColor : α → C)
    (low oldHigh incomingHigh : ρ) (prefixTree oldTail incomingTail : Source α ρ)
    (prefixColors : ∀ key ∈ prefixTree.shape.leaves, oldColor key = newColor key)
    (oldColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key)
    (incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key) :
    annotate identifier oldColor (some (identifier low)) prefixTree =
      annotate identifier newColor (some (identifier low)) prefixTree ∧
    annotate identifier oldColor (some (identifier oldHigh)) oldTail =
      annotate identifier dormantColor (some (identifier oldHigh)) oldTail ∧
    annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail =
      annotate identifier newColor (some (identifier incomingHigh)) incomingTail :=
  ⟨annotate_color_congr identifier prefixTree _ _ _ prefixColors,
    annotate_color_congr identifier oldTail _ _ _ oldColors,
    annotate_color_congr identifier incomingTail _ _ _ incomingColors⟩

end HeadBoundary
end ChaCha.Paper20261030.Structural
