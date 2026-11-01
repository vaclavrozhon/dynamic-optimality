import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log

namespace Splay.Interface

/--
The abstract interface has one element for every value or null external node:
`null 0, value 0, ..., value (n - 1), null n`.
-/
abbrev Element (n : ℕ) :=
  Fin (2 * n + 1)

/-- Stable identifiers for blocks. A state's block list is indexed by these. -/
abbrev BlockId :=
  ℕ

/--
Structural parameters on which the hidden constants in the abstract interface
may depend.

The matching fraction is `matchingNumerator / matchingDenominator`; keeping it
rational makes the pass-size condition an exact natural-number inequality.
-/
structure Shape where
  growingLimit : ℕ
  exemptPasses : ℕ
  matchingNumerator : ℕ
  matchingDenominator : ℕ
  matchingNumerator_pos : 0 < matchingNumerator
  matchingFraction_le_half :
    2 * matchingNumerator ≤ matchingDenominator

/--
Finite parameters of one instance of the abstract interface.

The value bound is deliberately kept outside `Shape`: the constants in the
activity theorem must be uniform in both the number of elements and this bound.
-/
structure Parameters extends Shape where
  valueBound : ℕ
  valueBound_ge_two : 2 ≤ valueBound

/-- A block can grow until conversion, after which it can only shrink. -/
inductive Mode
  | growing
  | shrinking
  deriving DecidableEq, Repr

/-- One ordered block in the interface state. -/
structure Block (n : ℕ) where
  creator : Element n
  passCount : ℕ
  mode : Mode
  elements : List (Element n)
  deriving DecidableEq, Repr

/--
A raw finite state. Validity separately enforces value bounds, disjoint block
membership, and the per-creator limit on growing blocks.
-/
structure State (n : ℕ) where
  blocks : List (Block n)
  value : Element n → ℕ

namespace State

variable {n : ℕ}

/-- Lookup by a stable block identifier. -/
def block? (state : State n) (id : BlockId) : Option (Block n) :=
  state.blocks[id]?

/-- All elements currently belonging to blocks, retaining block order. -/
def allElements (state : State n) : List (Element n) :=
  state.blocks.flatMap fun block => block.elements

/-- Number of growing blocks with a specified creator. -/
def growingCount (state : State n) (creator : Element n) : ℕ :=
  (state.blocks.filter fun block =>
    decide (block.mode = .growing ∧ block.creator = creator)).length

/-- The complete invariant required of every state in a valid trace. -/
def Valid (state : State n) (params : Parameters) : Prop :=
  state.allElements.Nodup ∧
    (∀ element, 1 ≤ state.value element ∧
      state.value element ≤ params.valueBound) ∧
    ∀ creator, state.growingCount creator ≤ params.growingLimit

/-- An initial state has no blocks; its bounded values are arbitrary. -/
def Initial (state : State n) (params : Parameters) : Prop :=
  state.Valid params ∧ state.blocks = []

end State

/-- A unit change of an element value. -/
inductive ValueDelta
  | decrease
  | increase
  deriving DecidableEq, Repr

/--
One tuple in a pass matching: `winner` stays in the shrinking source block,
while `loser` moves to the indicated growing block of `winner`.
-/
structure Pairing (n : ℕ) where
  winner : Element n
  loser : Element n
  destination : BlockId
  deriving DecidableEq, Repr

/-- The externally visible operations of the abstract interface. -/
inductive Operation (n : ℕ)
  | convert (block : BlockId)
  | create (creator : Element n)
  | insert (block : BlockId) (element : Element n)
  | delete (block : BlockId) (element : Element n)
  | pass (block : BlockId) (matching : List (Pairing n))
  | split (block : BlockId) (prefixLength : ℕ)
  | valueChange (element : Element n) (delta : ValueDelta)
  deriving DecidableEq, Repr

/-- Two elements occur consecutively in either order in an ordered block. -/
def Adjacent {α : Type*} (elements : List α) (first second : α) : Prop :=
  ∃ front back,
    elements = front ++ first :: second :: back ∨
      elements = front ++ second :: first :: back

/-- Preconditions for one pairing tuple in a particular source block. -/
def PairingValid {n : ℕ} (state : State n) (sourceId : BlockId)
    (source : Block n) (pairing : Pairing n) : Prop :=
  Adjacent source.elements pairing.winner pairing.loser ∧
    state.value pairing.winner + 1 ≤ state.value pairing.loser ∧
    pairing.destination ≠ sourceId ∧
    ∃ destination,
      state.block? pairing.destination = some destination ∧
        destination.mode = .growing ∧
        destination.creator = pairing.winner

/--
Validity of a complete pass matching.

`source.passCount < exemptPasses` exempts exactly the first
`exemptPasses` calls, whose pre-pass counts are `0, ..., exemptPasses - 1`.
Once the count equals `exemptPasses`, the matching-fraction inequality is
mandatory. This is the corrected strict condition used by the decay argument.
-/
def MatchingValid {n : ℕ} (params : Parameters) (state : State n)
    (sourceId : BlockId) (source : Block n)
    (matching : List (Pairing n)) : Prop :=
  source.mode = .shrinking ∧
    (matching.flatMap fun pairing =>
      [pairing.winner, pairing.loser]).Nodup ∧
    (matching.map fun pairing => pairing.destination).Nodup ∧
    (∀ pairing ∈ matching,
      PairingValid state sourceId source pairing) ∧
    (source.passCount < params.exemptPasses ∨
      params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator * matching.length)

/-- Remove each pass loser once from the source sequence. -/
def removeLosers {n : ℕ} (elements : List (Element n))
    (matching : List (Pairing n)) : List (Element n) :=
  matching.foldl (fun remaining pairing =>
    remaining.erase pairing.loser) elements

/-- Prepend each loser to its indicated destination block. -/
def insertAtDestinations {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n)) : List (Block n) :=
  matching.foldl
    (fun current pairing =>
      current.modify pairing.destination fun destination =>
        { destination with
          elements := pairing.loser :: destination.elements })
    blocks

/-- Exact simultaneous effect of a valid pass on the block collection. -/
def passBlocks {n : ℕ} (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (matching : List (Pairing n)) : List (Block n) :=
  let sourceAfter :=
    { source with
      passCount := source.passCount + 1
      elements := removeLosers source.elements matching }
  let sourceUpdated := blocks.modify sourceId fun _ => sourceAfter
  insertAtDestinations sourceUpdated matching

/--
Exact effect of a split. The old block remains as an empty shrinking block,
and the two new shrinking blocks are appended, giving them fresh stable IDs.
-/
def splitBlocks {n : ℕ} (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (prefixLength : ℕ) : List (Block n) :=
  let oldEmptied :=
    blocks.modify sourceId fun current => { current with elements := [] }
  let prefixBlock :=
    { source with elements := source.elements.take prefixLength }
  let suffixBlock :=
    { source with elements := source.elements.drop prefixLength }
  oldEmptied ++ [prefixBlock, suffixBlock]

/--
The exact state effect and operation-specific preconditions. Global state
validity is imposed by `Step` below.
-/
inductive Effect {n : ℕ} (params : Parameters) :
    State n → Operation n → State n → Prop
  | convert {before after : State n} {blockId : BlockId} {block : Block n}
      (found : before.block? blockId = some block)
      (growing : block.mode = .growing)
      (blocks_eq :
        after.blocks =
          before.blocks.modify blockId fun current =>
            { current with mode := .shrinking })
      (values_eq : after.value = before.value) :
      Effect params before (.convert blockId) after
  | create {before after : State n} {creator : Element n}
      (room :
        before.growingCount creator < params.growingLimit)
      (blocks_eq :
        after.blocks =
          before.blocks ++
            [{ creator := creator
               passCount := 0
               mode := .growing
               elements := [] }])
      (values_eq : after.value = before.value) :
      Effect params before (.create creator) after
  | insert {before after : State n} {blockId : BlockId}
      {block : Block n} {element : Element n}
      (found : before.block? blockId = some block)
      (growing : block.mode = .growing)
      (unassigned : element ∉ before.allElements)
      (value_order :
        before.value block.creator + 1 ≤ before.value element)
      (blocks_eq :
        after.blocks =
          before.blocks.modify blockId fun current =>
            { current with elements := element :: current.elements })
      (values_eq : after.value = before.value) :
      Effect params before (.insert blockId element) after
  | delete {before after : State n} {blockId : BlockId}
      {block : Block n} {element : Element n}
      (found : before.block? blockId = some block)
      (shrinking : block.mode = .shrinking)
      (present : element ∈ block.elements)
      (blocks_eq :
        after.blocks =
          before.blocks.modify blockId fun current =>
            { current with elements := current.elements.erase element })
      (values_eq : after.value = before.value) :
      Effect params before (.delete blockId element) after
  | pass {before after : State n} {blockId : BlockId}
      {source : Block n} {matching : List (Pairing n)}
      (found : before.block? blockId = some source)
      (valid_matching :
        MatchingValid params before blockId source matching)
      (blocks_eq :
        after.blocks =
          passBlocks before.blocks blockId source matching)
      (values_eq : after.value = before.value) :
      Effect params before (.pass blockId matching) after
  | split {before after : State n} {blockId : BlockId}
      {source : Block n} {prefixLength : ℕ}
      (found : before.block? blockId = some source)
      (shrinking : source.mode = .shrinking)
      (prefix_le : prefixLength ≤ source.elements.length)
      (blocks_eq :
        after.blocks =
          splitBlocks before.blocks blockId source prefixLength)
      (values_eq : after.value = before.value) :
      Effect params before (.split blockId prefixLength) after
  | decrease {before after : State n} {element : Element n}
      (can_decrease : 1 < before.value element)
      (blocks_eq : after.blocks = before.blocks)
      (values_eq :
        after.value =
          Function.update before.value element
            (before.value element - 1)) :
      Effect params before (.valueChange element .decrease) after
  | increase {before after : State n} {element : Element n}
      (can_increase : before.value element < params.valueBound)
      (blocks_eq : after.blocks = before.blocks)
      (values_eq :
        after.value =
          Function.update before.value element
            (before.value element + 1)) :
      Effect params before (.valueChange element .increase) after

/-- A legal step is an exact operation effect between two valid states. -/
def Step {n : ℕ} (params : Parameters) (before : State n)
    (operation : Operation n) (after : State n) : Prop :=
  before.Valid params ∧
    Effect params before operation after ∧
    after.Valid params

/-- A finite sequence of legal interface steps. -/
inductive Trace {n : ℕ} (params : Parameters) :
    State n → List (Operation n) → State n → Prop
  | nil {state : State n} (valid : state.Valid params) :
      Trace params state [] state
  | cons {before middle after : State n} {operation : Operation n}
      {operations : List (Operation n)}
      (head : Step params before operation middle)
      (tail : Trace params middle operations after) :
      Trace params before (operation :: operations) after

namespace Operation

/-- Contribution of one operation to total activity. -/
def activity {n : ℕ} : Operation n → ℕ
  | .pass _ matching => matching.length
  | _ => 0

/-- Indicator for an `Insert` operation. -/
def insertCount {n : ℕ} : Operation n → ℕ
  | .insert _ _ => 1
  | _ => 0

/-- Indicator for a `ValueChange` operation in either direction. -/
def valueChangeCount {n : ℕ} : Operation n → ℕ
  | .valueChange _ _ => 1
  | _ => 0

end Operation

/-- Sum of matching sizes over all pass operations. -/
def totalActivity {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.activity).sum

/-- Number of inserts in an operation sequence. -/
def totalInserts {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.insertCount).sum

/-- Number of unit value changes in an operation sequence. -/
def totalValueChanges {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.valueChangeCount).sum

/--
Exact uniform formulation of the manuscript's abstract activity claim.

The two constants may depend on the structural `Shape`, but are chosen before
`params` and `n`; in particular, they are uniform in both the number of
elements and `valueBound`. They represent the hidden constants in the
`Insert · O(valueBound)` and `ValueChange · O(log valueBound)` terms.  The
theorem `activityBound` is proved from the chronological incidence argument.
-/
def ActivityBound (shape : Shape) : Prop :=
  ∃ insertConstant valueChangeConstant : ℕ,
    0 < insertConstant ∧
      0 < valueChangeConstant ∧
      ∀ (params : Parameters), params.toShape = shape →
        ∀ {n : ℕ} {initial final : State n}
          {operations : List (Operation n)},
          initial.Initial params →
          Trace params initial operations final →
          totalActivity operations ≤
            insertConstant * params.valueBound * totalInserts operations +
              valueChangeConstant * Nat.clog 2 params.valueBound *
                totalValueChanges operations

end Splay.Interface
