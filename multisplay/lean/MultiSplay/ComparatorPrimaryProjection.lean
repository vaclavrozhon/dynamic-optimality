import MultiSplay.ClassicalSwitchReference
import MultiSplay.ComparatorGapProgram
import TangoSquared.Paper20261030.PhysicalComponentOperations

/-! # A primary comparator component has exactly its original keys

An indexed reference BST has one external gap at each boundary of its
key interval. Regard its two children as routing children and retain the
current preference bit. Collapse each nonpreferred exit subtree to its
rightmost external gap. The boundaries between these collapsed gaps are
precisely the original keys on the preferred path.

We unfold an arbitrary maintained depth source using the existing packed
primary construction, then remove the final external gap with `GapBST.gaps`.
There is no added maximum-key root and no extra sentinel key. The existing
source rearrangement theorem supplies an actual comparator preparation on
this exact original-key alphabet.
-/

namespace MultiSplay.ComparatorPrimary

open DynamicOptimality (BST)
open TangoSquared
open Paper20261030
open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical
open EndpointEncoding

/-- Original key `k` separates external gap intervals ending and beginning
at `k`. Empty indexed trees therefore contribute their one boundary. -/
def routing : {lower upper : Nat} → State → BST lower upper → PrefRouter Nat
  | _, _, _, .empty boundary => .leaf boundary
  | _, _, state, .node left right =>
      .fork (state []) (routing (below state false) left) (routing (below state true) right)

def lastGap : PrefRouter Nat → Nat
  | .leaf key => key
  | .fork _ _ right => lastGap right

def gapWord (primary : PrefRouter Nat) : List Nat :=
  ((exits primary).filter (·.leftOfEndpoint)).map (fun exit => lastGap exit.subtree) ++
    [primary.terminal] ++
      (((exits primary).filter (fun exit => !exit.leftOfEndpoint)).reverse).map
        (fun exit => lastGap exit.subtree)

theorem lastGap_routing {lower upper : Nat} (state : State) (reference : BST lower upper) :
    lastGap (routing state reference) = upper := by
  induction reference generalizing state with
  | empty => rfl
  | node left right ihl ihr => exact ihr _

theorem gapWord_false (left right : PrefRouter Nat) :
    gapWord (.fork false left right) = gapWord left ++ [lastGap right] := by
  simp [gapWord,exits,PrefRouter.terminal,List.filter_cons,List.map_append,List.append_assoc]

theorem gapWord_true (left right : PrefRouter Nat) :
    gapWord (.fork true left right) = lastGap left :: gapWord right := by
  simp [gapWord,exits,PrefRouter.terminal,List.filter_cons]

/-- The last external boundary is discarded later; every preceding gap
boundary is one original key of the canonical preferred component. -/
theorem gapWord_routing {lower upper : Nat} (state : State) (reference : BST lower upper) :
    gapWord (routing state reference) =
      (ClassicalSwitch.preferred state reference.toRaw).inorder ++ [upper] := by
  induction reference generalizing state with
  | empty boundary => rfl
  | @node lower key upper left right ihl ihr =>
      cases bit : state [] with
      | false =>
          simp only [routing,bit,gapWord_false,ihl,lastGap_routing,ClassicalSwitch.preferred,
            DynamicOptimality.BST.toRaw,Bool.false_eq_true,if_false,MTR.Tree.inorder,List.append_nil,
            List.append_assoc]
      | true =>
          simp only [routing,bit,gapWord_true,ihr,lastGap_routing,ClassicalSwitch.preferred,
            DynamicOptimality.BST.toRaw,if_true,MTR.Tree.inorder,List.nil_append,List.cons_append]

def collapsed (ρ : Type*) (exit : Exit Nat) : Source Nat (List (Option (PackedPrimary.Datum ρ))) :=
  .leaf (lastGap exit.subtree) []

theorem physical_gapWord {ρ : Type*} {primary : PrefRouter Nat}
    (input : PackedPrimary.Input primary ρ) :
    (input.physical (collapsed ρ)).shape.leaves = gapWord primary := by
  rw [PackedPrimary.Input.physical,PrimaryPhysical.component_leaves,graftWing_leaves,graftWing_leaves,
    input.completePlan_words.1,input.completePlan_words.2]
  simp only [collapsed,Source.shape,RouterProjection.Router.leaves,← List.map_eq_flatMap]
  rfl

def tree {lower upper : Nat} {ρ : Type*} (state : State) (reference : BST lower upper)
    (input : PackedPrimary.Input (routing state reference) ρ) : DynamicOptimality.RawTree Nat :=
  GapBST.gaps (input.physical (collapsed ρ))

theorem tree_inorder {lower upper : Nat} {ρ : Type*} (state : State) (reference : BST lower upper)
    (input : PackedPrimary.Input (routing state reference) ρ) :
    (tree state reference input).inorder = (ClassicalSwitch.preferred state reference.toRaw).inorder := by
  have words := (GapBST.gaps_word (input.physical (collapsed ρ))).trans
    ((physical_gapWord input).trans (gapWord_routing state reference))
  have prefixes := congrArg List.dropLast words
  simpa only [tree,List.dropLast_append_cons,List.dropLast_singleton,List.append_nil] using prefixes

/-- A source rearrangement unfolds inside the same actual preferred
component. Its output domain is derived by `tree_inorder` on both sides. -/
theorem source_program {lower upper : Nat} {ρ : Type*} (state : State) (reference : BST lower upper)
    (before after : PackedPrimary.Input (routing state reference) ρ)
    (sameStart : before.start = after.start) {budget : Nat}
    (execution : SourcePointer.Rearranges before.source after.source budget) :
    ∃ work ≤ 816 * budget + 156,
      CommonForest.Program [tree state reference before] [] [tree state reference after] work := by
  have physical := PackedPrimary.source_physical_rearranges before after sameStart (collapsed ρ) execution
  obtain ⟨work,bound,run⟩ := ComparatorGap.rearranges_program physical
  exact ⟨work,by omega,run⟩

end MultiSplay.ComparatorPrimary
