import MultiSplay.PackedProgram

/-! # Physical forest programs without an assumed common accounting universe -/

namespace MultiSplay.Unlocated

open Splay.Interface (Parameters)
open Splay.Rank (Snapshot)
open Splay.Tree.BST
open Splay.Assumptions.NormalForm

structure Trees where
  size : Nat
  comparison : Splay.Tree.BST 0 size
  splay : Splay.Tree.BST 0 size

def mass (forest : List Trees) : Nat := (forest.map (fun trees => 2*trees.size+1)).sum

inductive Move (params : Parameters) (slack depth : Nat) : List Trees → List Trees → Type
  | request {n : Nat} (comparison before after : Splay.Tree.BST 0 n) (key : Fin n) (tail : List Trees)
      (root : comparison.HasRoot key.val) (execution : SplayExecution key.val before after)
      (cap : Splay.Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound)
      (normal : HasRelevantNeighborRankBound (Snapshot.ofTree comparison) slack) :
      Move params slack depth (⟨n, comparison, before⟩ :: tail) (⟨n, comparison, after⟩ :: tail)
  | rotation {n actualDepth : Nat} (before after splay : Splay.Tree.BST 0 n) (tail : List Trees)
      (rotation : RotationAt actualDepth before after) (normal : actualDepth ≤ depth) :
      Move params slack depth (⟨n, before, splay⟩ :: tail) (⟨n, after, splay⟩ :: tail)
  | split {l r : Nat} (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
      (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (tail : List Trees) :
      Move params slack depth (⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr⟩ :: tail)
        (⟨l, left, sl⟩ :: ⟨r, right, sr⟩ :: tail)
  | join {l r : Nat} (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
      (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (tail : List Trees)
      (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
      Move params slack depth (⟨l, left, sl⟩ :: ⟨r, right, sr⟩ :: tail)
        (⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr⟩ :: tail)
  | reorder {before after : List Trees} (order : before.Perm after) : Move params slack depth before after

namespace Move

variable {params : Parameters} {slack depth : Nat} {before after : List Trees}

def splayCost : Move params slack depth before after → Nat
  | .request _ before _ key _ _ _ _ _ => before.depth key.val+1
  | .rotation .. | .split .. | .join .. | .reorder .. => 0

def requests : Move params slack depth before after → Nat
  | .request .. => 1
  | .rotation .. | .split .. | .join .. | .reorder .. => 0

def rotations : Move params slack depth before after → Nat
  | .rotation .. => 1
  | .request .. | .split .. | .join .. | .reorder .. => 0

def boundaries : Move params slack depth before after → Nat
  | .split .. | .join .. => 1
  | .request .. | .rotation .. | .reorder .. => 0

def joins : Move params slack depth before after → Nat
  | .join .. => 1
  | .request .. | .rotation .. | .split .. | .reorder .. => 0

end Move

inductive Program (params : Parameters) (slack depth : Nat) : List Trees → List Trees → Type
  | done (forest : List Trees) : Program params slack depth forest forest
  | next {first middle last : List Trees} (move : Move params slack depth first middle)
      (tail : Program params slack depth middle last) : Program params slack depth first last

namespace Program

variable {params : Parameters} {slack depth : Nat}

def sum (charge : ∀ {before after : List Trees}, Move params slack depth before after → Nat) :
    {before after : List Trees} → Program params slack depth before after → Nat
  | _, _, .done _ => 0
  | _, _, .next move tail => charge move + tail.sum charge

abbrev splayCost {before after : List Trees} (program : Program params slack depth before after) := program.sum Move.splayCost
abbrev requests {before after : List Trees} (program : Program params slack depth before after) := program.sum Move.requests
abbrev rotations {before after : List Trees} (program : Program params slack depth before after) := program.sum Move.rotations
abbrev boundaries {before after : List Trees} (program : Program params slack depth before after) := program.sum Move.boundaries
abbrev joins {before after : List Trees} (program : Program params slack depth before after) := program.sum Move.joins

end Program
end MultiSplay.Unlocated
