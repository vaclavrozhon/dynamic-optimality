import MultiSplay.PackedSplay
import MultiSplay.RichSplitPackingExact

/-! # Common splits of an arbitrary component in the actual packed history -/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Interface (Element Parameters)
open SharedSplay
open InterfacePacking (pack)

variable {l r m : Nat} {params : Parameters}

theorem split (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
    (element : Element (0+l+1+r) → Element m) (injective : Function.Injective element)
    (source : Splay.Lazy.State (0+l+1+r)) (tail : List (Local m)) (whole : Splay.Interface.State m)
    (packing : Packing params
      (⟨⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr, element, injective⟩, source⟩ :: tail) whole)
    (slack depth : Nat) :
    ∃ a : Splay.Lazy.State l, ∃ b : Splay.Lazy.State r, ∃ final : Splay.Interface.State m,
      Nonempty (Packing params
        (⟨⟨l, left, sl, element ∘ JoinIntervals.leftEmbedding l r,
          injective.comp (RankEmbedding.external_injective _ _)⟩, a⟩ ::
         ⟨⟨r, right, sr, element ∘ JoinIntervals.rightEmbedding l r,
          injective.comp (RankEmbedding.external_injective _ _)⟩, b⟩ :: tail) final) ∧
      ∃ segment : Segment params whole final,
        SegmentEvolution slack depth segment
          (⟨_, ⟨JoinRanks.tree left right, JoinRanks.tree sl sr, source⟩⟩ :: geometry tail)
          (⟨l, ⟨left, sl, a⟩⟩ :: ⟨r, ⟨right, sr, b⟩⟩ :: geometry tail) ∧
        segment.splayCost = 0 ∧ segment.requests = 0 ∧ segment.rotations = 0 ∧ segment.maintenanceCost ≤ 8 := by
  have cert := packing.certified _ (List.mem_cons_self)
  obtain ⟨boundary, execution, same, length⟩ := RichSplit.exists_packed_split left right sl sr source cert.represented
  let a := RichSplit.leftState left right sl sr source cert.represented
  let b := RichSplit.rightState left right sl sr source cert.represented
  let children := [RichSplit.leftComponent left right sl sr source cert.represented,
    RichSplit.rightComponent left right sl sr source cert.represented]
  let retired := RichSplit.archive source (JoinRanks.pivot l r)
  have retiredClosed : InterfacePacking.Closed retired := ⟨RichSplit.archive_closed _ _, fun _ => rfl⟩
  let framed := packing.headFrame
  obtain ⟨word, final, actual, ⟨next, elementEq, frameEq⟩, count, _, _, _, _⟩ := framed.trace execution
  have actualEq := next.equivalent
  rw [elementEq, frameEq] at actualEq
  have disjoint : ∀ component ∈ components tail, ∀ x y, element x ≠ component.element y :=
    (List.pairwise_cons.mp packing.separate).1
  have flat := InterfacePacking.flatten element injective retired packing.archive children (components tail) disjoint
  have nested := same.prefix element (pack packing.archive (components tail))
  refine ⟨a, b, final, ?_, .maintenance actual,
    .maintenance actual (.split left right sl sr source a b [] (geometry tail)), rfl, rfl, rfl, ?_⟩
  · refine ⟨⟨InterfacePrefix.state element packing.archive retired, packing.closed.prefix retiredClosed element injective,
      ?_, ?_, ?_⟩⟩
    · apply InterfacePacking.separate_replacement element injective children (components tail)
      · simpa [children, List.pairwise_cons, RichSplit.leftComponent, RichSplit.rightComponent,
          InterfacePacking.Component.Disjoint] using JoinIntervals.disjoint l r
      · exact (List.pairwise_cons.mp packing.separate).2
      · exact disjoint
    · intro component member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨RichSplit.left_represents left right sl sr source cert.represented,
          RichRestriction.growing_zero source _ _ cert.growingZero,
          RichSplit.left_unbroken left right sl sr source cert.represented cert.unbroken⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨RichSplit.right_represents left right sl sr source cert.represented,
            RichRestriction.growing_zero source _ _ cert.growingZero,
            RichSplit.right_unbroken left right sl sr source cert.represented cert.unbroken⟩
        · exact packing.certified component (List.mem_cons_of_mem _ member)
    · exact ⟨flat.1.symm.trans (nested.1.trans actualEq.1), flat.2.symm.trans (nested.2.trans actualEq.2)⟩
  · change word.length ≤ 8
    omega

end MultiSplay.PackedSplay
