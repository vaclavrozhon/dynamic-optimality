import Splay.Interface.Model
import Mathlib.Tactic

namespace Splay.Interface

namespace Operation

/-- Exact increase in the persistent block list caused by one operation. -/
def blockGrowth {n : ℕ} : Operation n → ℕ
  | .create _ => 1
  | .split _ _ => 2
  | _ => 0

end Operation

/-- Total persistent block-list growth of an abstract operation sequence. -/
def totalBlockGrowth {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.blockGrowth).sum

@[simp]
theorem insertAtDestinations_length {n : ℕ}
    (blocks : List (Block n)) (matching : List (Pairing n)) :
    (insertAtDestinations blocks matching).length = blocks.length := by
  unfold insertAtDestinations
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons pairing matching ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp

@[simp]
theorem passBlocks_length {n : ℕ}
    (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (matching : List (Pairing n)) :
    (passBlocks blocks sourceId source matching).length =
      blocks.length := by
  unfold passBlocks
  rw [insertAtDestinations_length]
  simp

@[simp]
theorem splitBlocks_length {n : ℕ}
    (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (prefixLength : ℕ) :
    (splitBlocks blocks sourceId source prefixLength).length =
      blocks.length + 2 := by
  simp [splitBlocks]

namespace Effect

/--
The interface never removes block identities.  Create appends one and split
retains its emptied source while appending two; every other operation
preserves the exact list length.
-/
theorem blocks_length_eq {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after) :
    after.blocks.length =
      before.blocks.length + operation.blockGrowth := by
  cases effect <;>
    simp_all [Operation.blockGrowth]

end Effect

namespace Trace

/-- Exact telescoping block-count law for a complete interface trace. -/
theorem blocks_length_eq {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (trace : Trace params initial operations final) :
    final.blocks.length =
      initial.blocks.length + totalBlockGrowth operations := by
  induction trace with
  | nil _ =>
      simp [totalBlockGrowth]
  | cons head tail ih =>
      have hHead := head.2.1.blocks_length_eq
      simp only [totalBlockGrowth] at ih
      simp only [totalBlockGrowth, List.map_cons, List.sum_cons]
      omega

end Trace

end Splay.Interface
