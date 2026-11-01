import MultiSplay.PackedSplay

/-! # Constructing a common join from two actual packed components -/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Interface (Element Parameters)
open SharedSplay
open InterfacePacking (pack)

variable {l r m : Nat} {params : Parameters}

theorem join (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
    (element : Element (0+l+1+r) → Element m) (injective : Function.Injective element)
    (a : Splay.Lazy.State l) (b : Splay.Lazy.State r) (tail : List (Local m)) (whole : Splay.Interface.State m)
    (packing : Packing params
      (⟨⟨l, left, sl, element ∘ JoinIntervals.leftEmbedding l r,
        injective.comp (RankEmbedding.external_injective _ _)⟩, a⟩ ::
       ⟨⟨r, right, sr, element ∘ JoinIntervals.rightEmbedding l r,
        injective.comp (RankEmbedding.external_injective _ _)⟩, b⟩ :: tail) whole)
    (disjoint : ∀ component ∈ tail, ∀ x y, element x ≠ component.1.element y)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) (slack depth : Nat) :
    ∃ source : Splay.Lazy.State (0+l+1+r), ∃ final : Splay.Interface.State m,
      Nonempty (Packing params
        (⟨⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr, element, injective⟩, source⟩ :: tail) final) ∧
      ∃ segment : Segment params whole final,
        SegmentEvolution slack depth segment
          (⟨l, ⟨left, sl, a⟩⟩ :: ⟨r, ⟨right, sr, b⟩⟩ :: geometry tail)
          (⟨_, ⟨JoinRanks.tree left right, JoinRanks.tree sl sr, source⟩⟩ :: geometry tail) ∧
        segment.splayCost = 0 ∧ segment.requests = 0 ∧ segment.rotations = 0 ∧ segment.maintenanceCost ≤ 8 := by
  have aCert := packing.certified _ (List.mem_cons_self)
  have bCert := packing.certified _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have tailSeparate := (List.pairwise_cons.mp (List.pairwise_cons.mp packing.separate).2).2
  have tailValid : ∀ component ∈ components tail, component.source.Valid params := by
    intro component member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (packing.certified original (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present))).represented.valid.1
  have regionSeparate : ∀ component ∈ components tail, ∀ x y, element x ≠ component.element y := by
    intro component member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact disjoint original present
  let framed := InterfacePacking.regionFrame element injective
    (InterfaceCommonJoin.initial a.toInterface b.toInterface)
    [InterfacePacking.leftJoinComponent a.toInterface r, InterfacePacking.rightJoinComponent l b.toInterface]
    (InterfacePacking.join_initial_packed a.toInterface b.toInterface)
    packing.archive packing.closed (components tail) tailSeparate tailValid regionSeparate whole packing.equivalent
  have execution := RichJoin.interface_trace left right sl sr a b aCert.represented bCert.represented growingLimit valueCap
  obtain ⟨word, final, actual, ⟨next, elementEq, frameEq⟩, count, _, _, _, _⟩ := framed.trace execution
  let source := RichJoin.state left right sl sr a b
  refine ⟨source, final, ?_, .maintenance actual,
    .maintenance actual (.join left right sl sr source a b [] (geometry tail)), rfl, rfl, rfl, ?_⟩
  · refine ⟨⟨packing.archive, packing.closed, List.pairwise_cons.mpr ⟨regionSeparate, tailSeparate⟩, ?_, ?_⟩⟩
    · intro component member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨RichJoin.represents left right sl sr a b aCert.represented bCert.represented growingLimit valueCap,
          RichJoin.growing_zero left right sl sr a b aCert.growingZero bCert.growingZero,
          RichJoin.unbroken left right sl sr a b aCert.represented bCert.represented aCert.unbroken bCert.unbroken⟩
      · exact packing.certified component (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
    · have same := next.equivalent
      rw [elementEq, frameEq] at same
      exact same
  · change word.length ≤ 8
    rw [count]
    rfl

end MultiSplay.PackedSplay
