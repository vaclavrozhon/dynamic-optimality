import MultiSplay.PortableSplayFactor
import MultiSplay.BoundedMacros
import Splay.Accounting.OfflineStructuralRibBridge

/-! # The bounded normalizer supplies the local hypotheses of the splay program -/

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Interface (Element Parameters)
open Splay.Tree.BST
open Splay.Rank (Snapshot)

variable {n m : Nat}

def boundedRequest (height slack depth : Nat) (comparison before after : Splay.Tree.BST 0 n)
    (key : Fin n) (element : Element n → Element m) (injective : Function.Injective element)
    (tail : List (Trees m)) (root : comparison.HasRoot key.val)
    (execution : SplayExecution key.val before after) (bounded : comparison.height ≤ height)
    (ribs : OfflineNormalForm.HasBoundedMinorRibs comparison slack) :
    Move (articleParameters height) slack depth (⟨n, comparison, before, element, injective⟩ :: tail)
      (⟨n, comparison, after, element, injective⟩ :: tail) :=
  .request comparison before after key element injective tail root execution
    (Splay.Analysis.contractedGap_mono (by change 2*comparison.height+1 ≤ 2*height+1; omega))
    ((OfflineNormalForm.hasBoundedMinorRibs_iff_relevantNeighborDepth comparison).mp ribs).toRankBound

/-- Expand the actual bounded preparation path into individual comparison
rotations. The splay trees are literally unchanged during preparation. -/
theorem prepare {height slack count : Nat} {before after : Splay.Tree.BST 0 n}
    (path : BoundedMacros.Path height slack before after count)
    (splay : Splay.Tree.BST 0 n) (element : Element n → Element m)
    (injective : Function.Injective element) (tail : List (Trees m)) (params : Parameters) :
    ∃ program : Program params slack 1 (⟨n, before, splay, element, injective⟩ :: tail)
      (⟨n, after, splay, element, injective⟩ :: tail),
      program.rotations = count ∧ program.requests = 0 ∧ program.boundaries = 0 ∧ program.splayCost = 0 := by
  induction path with
  | nil source bounded ribs => exact ⟨.done _, rfl, rfl, rfl, rfl⟩
  | cons rotation shallow bounded ribs rest ih =>
      obtain ⟨later, rotations, requests, boundaries, cost⟩ := ih
      refine ⟨.next (.rotation _ _ splay element injective tail rotation shallow) later, ?_, ?_, ?_, ?_⟩
      · change 1 + later.rotations = _
        omega
      · simpa [Program.requests, Program.sum, Move.requests] using requests
      · simpa [Program.boundaries, Program.sum, Move.boundaries] using boundaries
      · simpa [Program.splayCost, Program.sum, Move.splayCost] using cost

end MultiSplay.PackedSplay
