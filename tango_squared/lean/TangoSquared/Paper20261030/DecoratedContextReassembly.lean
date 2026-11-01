import TangoSquared.Paper20261030.ContextReassembly

/-!
# Reassembly with explicit connector record lists

The context leaves name whole unchanged physical blocks. A record list
at each context vertex is stored as a prefix at the reached projection
root, exactly as in the colored storage primitives. Clear these prefixes,
reassemble the empty-record context, then install the target prefixes.
All reads, writes, cursor movements, and rotations are charged. The lists
and their target values are inputs; this does not infer a record-acquisition
or structural-metadata maintenance algorithm.
-/

namespace TangoSquared.Paper20261030.OrderedContext

open RouterProjection ColoredStorage ProjectionLocal

variable {ι α ρ : Type*}

def decorated (blocks : ι → Projected α ρ) : Source ι (List ρ) → Projected α ρ
  | .leaf key records => decorate records (blocks key)
  | .fork records l r => decorate records (join (decorated blocks l) (decorated blocks r))

def vertices : Source ι (List ρ) → Nat
  | .leaf .. => 1
  | .fork _ l r => vertices l + vertices r + 1

theorem context_full (t : Source ι (List ρ)) : Router.Full t.shape := by
  induction t with
  | leaf => trivial
  | fork records l r ihl ihr => exact ⟨SourcePointer.source_nonempty l,SourcePointer.source_nonempty r,ihl,ihr⟩

theorem context_vertices (t : Source ι (List ρ)) : vertices t + 1 = 2 * t.shape.leaves.length := by
  induction t with
  | leaf => rfl
  | fork records l r ihl ihr =>
    simp only [vertices,Source.shape,Router.leaves,List.length_append]
    omega

theorem clear_records (blocks : ι → Projected α ρ) (t : Source ι (List ρ)) :
    Rearranges (decorated blocks t) (realize blocks t.shape) (6 * vertices t) := by
  induction t with
  | leaf key records => exact (decorate_backward records (blocks key)).mono (by simp only [vertices]; omega)
  | fork records l r ihl ihr =>
    have clearRoot := decorate_backward records (join (decorated blocks l) (decorated blocks r))
    have clearLeft := ihl.join_left (r := decorated blocks r)
    have clearRight := ihr.join_right (l := realize blocks l.shape)
    apply ((clearRoot.trans clearLeft).trans clearRight).mono
    simp only [vertices]
    omega

theorem reassemble_decorated (blocks : ι → Projected α ρ) (before after : Source ι (List ρ))
    (orderedBlocks : before.shape.leaves = after.shape.leaves) (k : Nat)
    (beforeSize : before.shape.leaves.length = k) :
    Rearranges (decorated blocks before) (decorated blocks after) (36 * k) := by
  have first := clear_records blocks before
  have middle := reassemble_leaf_bound blocks before.shape after.shape (context_full before)
    (context_full after) orderedBlocks k beforeSize
  have last := (clear_records blocks after).symm
  apply ((first.trans middle).trans last).mono
  have nb := context_vertices before
  have na := context_vertices after
  rw [beforeSize] at nb
  rw [← orderedBlocks,beforeSize] at na
  omega

end TangoSquared.Paper20261030.OrderedContext
