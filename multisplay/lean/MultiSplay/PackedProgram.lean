import MultiSplay.PackedSplaySplit
import MultiSplay.PackedSplayJoin

/-!
# A portable physical program for the splay-side comparison

The program mentions comparison trees, splay trees, and disjoint embeddings.
Requests carry actual complete splay executions; preparations carry actual
comparison rotations. Common splits and joins are explicit. No lazy states,
interface executions, pairing estimates, or amortized bounds are inputs.
-/

namespace MultiSplay.PackedSplay

open Splay.Interface (Element Parameters)
open Splay.Tree.BST
open Splay.Rank (Snapshot)
open Splay.Assumptions.NormalForm

variable {m : Nat}

inductive Move (params : Parameters) (slack depth : Nat) : List (Trees m) → List (Trees m) → Type
  | request {n : Nat} (comparison before after : Splay.Tree.BST 0 n) (key : Fin n)
      (element : Element n → Element m) (injective : Function.Injective element) (tail : List (Trees m))
      (root : comparison.HasRoot key.val) (execution : SplayExecution key.val before after)
      (cap : Splay.Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound)
      (normal : HasRelevantNeighborRankBound (Snapshot.ofTree comparison) slack) :
      Move params slack depth (⟨n, comparison, before, element, injective⟩ :: tail)
        (⟨n, comparison, after, element, injective⟩ :: tail)
  | rotation {n actualDepth : Nat} (before after splay : Splay.Tree.BST 0 n)
      (element : Element n → Element m) (injective : Function.Injective element) (tail : List (Trees m))
      (rotation : RotationAt actualDepth before after) (normal : actualDepth ≤ depth) :
      Move params slack depth (⟨n, before, splay, element, injective⟩ :: tail)
        (⟨n, after, splay, element, injective⟩ :: tail)
  | split {l r : Nat} (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
      (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
      (element : Element (0+l+1+r) → Element m) (injective : Function.Injective element) (tail : List (Trees m)) :
      Move params slack depth (⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr, element, injective⟩ :: tail)
        (⟨l, left, sl, element ∘ JoinIntervals.leftEmbedding l r,
          injective.comp (RankEmbedding.external_injective _ _)⟩ ::
         ⟨r, right, sr, element ∘ JoinIntervals.rightEmbedding l r,
          injective.comp (RankEmbedding.external_injective _ _)⟩ :: tail)
  | join {l r : Nat} (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
      (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
      (element : Element (0+l+1+r) → Element m) (injective : Function.Injective element) (tail : List (Trees m))
      (disjoint : ∀ component ∈ tail, ∀ x y, element x ≠ component.element y)
      (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
      Move params slack depth
        (⟨l, left, sl, element ∘ JoinIntervals.leftEmbedding l r,
          injective.comp (RankEmbedding.external_injective _ _)⟩ ::
         ⟨r, right, sr, element ∘ JoinIntervals.rightEmbedding l r,
          injective.comp (RankEmbedding.external_injective _ _)⟩ :: tail)
        (⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr, element, injective⟩ :: tail)
  | reorder {before after : List (Trees m)} (order : before.Perm after) : Move params slack depth before after

namespace Move

variable {params : Parameters} {slack depth : Nat} {before after : List (Trees m)}

def splayCost : Move params slack depth before after → Nat
  | .request _ before _ key _ _ _ _ _ _ _ => before.depth key.val + 1
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

end Move

inductive Program (params : Parameters) (slack depth : Nat) : List (Trees m) → List (Trees m) → Type
  | done (forest : List (Trees m)) : Program params slack depth forest forest
  | next {first middle last : List (Trees m)} (move : Move params slack depth first middle)
      (tail : Program params slack depth middle last) : Program params slack depth first last

namespace Program

variable {params : Parameters} {slack depth : Nat}

def sum (charge : ∀ {before after : List (Trees m)}, Move params slack depth before after → Nat) :
    {before after : List (Trees m)} → Program params slack depth before after → Nat
  | _, _, .done _ => 0
  | _, _, .next move tail => charge move + tail.sum charge

abbrev splayCost {before after : List (Trees m)} (program : Program params slack depth before after) := program.sum Move.splayCost
abbrev requests {before after : List (Trees m)} (program : Program params slack depth before after) := program.sum Move.requests
abbrev rotations {before after : List (Trees m)} (program : Program params slack depth before after) := program.sum Move.rotations
abbrev boundaries {before after : List (Trees m)} (program : Program params slack depth before after) := program.sum Move.boundaries

end Program
end MultiSplay.PackedSplay
