import ChaCha.Paper20261030.SplayAuxiliaryPreparedTerminal
import ChaCha.Paper20261030.SplayAuxiliaryJoin
import ChaCha.Paper20261030.SplayAuxiliaryExchangePotential
import ChaCha.Paper20261030.SplayAuxiliaryExposure

/-!
# Prepared primary splitting by ordinary bottom-up splay

Splay the actual predecessor of the prepared terminal. The right subtree
is the dormant suffix, with exactly the old suffix ports. Attaching the
incoming suffix leaves all other ports unchanged. The bound includes
both resulting auxiliaries and charges no potential reset.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection
open MultiSplay.Auxiliary

private theorem ordered_parts {left right : RawTree Nat} {key : Nat}
    (ordered : (ChaCha.MTR.Tree.node left key right).Ordered) :
    (∀ x ∈ left.inorder, x < key) ∧ (∀ x ∈ right.inorder, key < x) := by
  have outer := List.pairwise_append.mp ordered
  have inner := List.pairwise_append.mp outer.1
  exact ⟨fun x member => inner.2.2 x member key (by simp),
    fun x member => outer.2.2 key (by simp) x member⟩

private theorem predecessor_filters (left right : RawTree Nat) (d : Nat) (positive : 0 < d)
    (ordered : (ChaCha.MTR.Tree.node left (d-1) right).Ordered) :
    (ChaCha.MTR.Tree.node left (d-1) right).inorder.filter (fun key => decide (d ≤ key)) =
      right.inorder ∧
    ((ChaCha.MTR.Tree.node left (d-1) right).inorder.filter (fun key => decide (key < d))).length =
      left.size+1 := by
  obtain ⟨less,greater⟩ := ordered_parts ordered
  have leftHigh : left.inorder.filter (fun key => decide (d ≤ key)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro key member
    have := less key member
    simpa using (show ¬d ≤ key by omega)
  have rightHigh : right.inorder.filter (fun key => decide (d ≤ key)) = right.inorder := by
    apply List.filter_eq_self.mpr
    intro key member
    have := greater key member
    simpa using (show d ≤ key by omega)
  have leftLow : left.inorder.filter (fun key => decide (key < d)) = left.inorder := by
    apply List.filter_eq_self.mpr
    intro key member
    have := less key member
    simpa using (show key < d by omega)
  have rightLow : right.inorder.filter (fun key => decide (key < d)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro key member
    have := greater key member
    simpa using (show ¬key < d by omega)
  constructor <;>
    simp [ChaCha.MTR.Tree.inorder,List.filter_append,leftHigh,rightHigh,leftLow,rightLow,
      show ¬d ≤ d-1 by omega,show d-1 < d by omega,ChaCha.MTR.Tree.length_inorder]

/-- Any actual predecessor splay locates the terminal at the same exact gap. -/
theorem prepared_splay_rank {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    {active : RawComponent Nat Nat}
    (represented : Represents cutKey followsRight (source reference p) active)
    {left right : RawTree Nat} {work : Nat}
    (execution : Splay (d-1) active.core (.node left (d-1) right) work) :
    PathDecomposition.terminalIndex followsRight (source reference p) = left.size+1 := by
  have ordered := represented_core_ordered represented (referenceCuts_source_ordered reference p)
  have same : Equivalent ⟨.node left (d-1) right,active.ports⟩ active :=
    ⟨execution.inorder_eq.symm,fun _ _ => rfl⟩
  have index := (predecessor_filters left right d (by omega) (execution.ordered_after ordered)).2
  rw [prepared_terminal_rank reference p d prepared (represented.equivalent same),index]

/-- A prepared non-leftmost terminal admits an actual splay split. The
returned components retain the original physical port subtrees verbatim. -/
theorem prepared_root_split {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    (active : RawComponent Nat Nat)
    (represented : Represents cutKey followsRight (source reference p) active) :
    ∃ left right : RawTree Nat, ∃ work : Nat,
      Splay (d-1) active.core (.node left (d-1) right) work ∧
      Represents cutKey followsRight (source reference p) ⟨.node left (d-1) right,active.ports⟩ ∧
      Represents cutKey followsRight (suffixSource reference p d valid)
        (RawComponent.suffix left right active.ports) ∧
      PathDecomposition.terminalIndex followsRight (source reference p) = left.size+1 ∧
      right.inorder = active.core.inorder.filter (fun key => decide (d ≤ key)) ∧
      SourcePointer.Rearranges active.closed
        (.fork (d-1) (RawComponent.prefixPart left active.ports).closed
          (RawComponent.suffix left right active.ports).closed) (3*work+1) := by
  have ordered := represented_core_ordered represented (referenceCuts_source_ordered reference p)
  have unique := ordered.imp (fun less => Nat.ne_of_lt less)
  obtain ⟨after,work,execution,physical⟩ := exists_pointer_splay
    (prepared_lower_member reference p d prepared lower represented)
  cases after with
  | empty => have impossible := execution.root_after; cases impossible
  | node left pivot right =>
      have key : pivot = d-1 := Option.some.inj execution.root_after
      subst pivot
      have same : Equivalent ⟨.node left (d-1) right,active.ports⟩ active :=
        ⟨execution.inorder_eq.symm,fun _ _ => rfl⟩
      have representedAfter := represented.equivalent same
      obtain ⟨suffixWord,indexWord⟩ := predecessor_filters left right d (by omega)
        (execution.ordered_after ordered)
      have rank : PathDecomposition.terminalIndex followsRight (source reference p) = left.size+1 := by
        rw [prepared_terminal_rank reference p d prepared representedAfter,indexWord]
      have word : right.inorder = active.core.inorder.filter (fun key => decide (d ≤ key)) := by
        rw [execution.inorder_eq,suffixWord]
      have ports : (RawComponent.suffix left right active.ports).portWord =
          active.portWord.drop (PathDecomposition.terminalIndex followsRight (source reference p)) := by
        rw [rank,RawComponent.suffix_portWord left right (d-1),same.portWord]
      have suffixRep := suffix_represents_of_words reference p d valid prepared active
        (RawComponent.suffix left right active.ports) represented word ports
      refine ⟨left,right,work,execution,representedAfter,suffixRep,rank,word,?_⟩
      have trace := splay_source_rearranges execution unique active.ports
      change SourcePointer.Rearranges active.closed
        (RawComponent.mk (.node left (d-1) right) active.ports).closed (3*work+1) at trace
      rw [RawComponent.prefix_suffix_closed] at trace
      exact trace

/-- Replacing the exact suffix by a prepared incoming component is the
paper's preference splice. Its potential bound uses the two actual roots. -/
theorem prepared_root_exchange {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d) (lower : a < d)
    (active incoming : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight (suffixSource reference q d valid) incoming) :
    ∃ left right : RawTree Nat, ∃ work : Nat,
      Splay (d-1) active.core (.node left (d-1) right) work ∧
      Represents cutKey followsRight (suffixSource reference p d valid)
        (RawComponent.suffix left right active.ports) ∧
      Represents cutKey followsRight (source reference (Secondary.spliceBits d p q))
        (RawComponent.join (RawComponent.prefixPart left active.ports) (d-1) incoming) ∧
      work+2*(potential (.node left (d-1) incoming.core)+potential right) ≤
        2*(potential active.core+potential incoming.core)+
          8*Nat.log 2 (source reference p).shape.height+1 := by
  obtain ⟨left,right,work,execution,exposedRep,suffixRep,index,suffixWord,physical⟩ :=
    prepared_root_split reference p d valid preparedP lower active activeRep
  have incomingWord : incoming.core.inorder = right.inorder := by
    rw [represented_suffix_keys reference q d valid preparedQ incomingRep,suffixWord,
      represented_keys reference p activeRep,
      SeparatorPath.word_terminal_congr reference q p d preparedQ preparedP]
  have sameWord : (RawComponent.join (RawComponent.prefixPart left active.ports) (d-1) incoming).core.inorder =
      active.core.inorder := by
    rw [RawComponent.join_word,incomingWord]
    exact execution.inorder_eq.symm
  have samePorts : (RawComponent.join (RawComponent.prefixPart left active.ports) (d-1) incoming).portWord =
      active.portWord.take (PathDecomposition.terminalIndex followsRight (source reference p)) ++
        incoming.portWord := by
    rw [RawComponent.join_portWord,index,RawComponent.prefix_portWord left right (d-1)]
    have same : Equivalent ⟨.node left (d-1) right,active.ports⟩ active :=
      ⟨execution.inorder_eq.symm,fun _ _ => rfl⟩
    rw [same.portWord]
  have joinedRep := splice_represents_of_words reference p q d valid preparedP preparedQ
    active incoming (RawComponent.join (RawComponent.prefixPart left active.ports) (d-1) incoming)
    activeRep incomingRep sameWord samePorts
  have fits : (ChaCha.MTR.Tree.node left (d-1) incoming.core).size ≤
      (source reference p).shape.height := by
    have sameSize := congrArg List.length sameWord
    simp only [ChaCha.MTR.Tree.length_inorder] at sameSize
    change (RawComponent.join (RawComponent.prefixPart left active.ports) (d-1) incoming).core.size ≤ _
    rw [sameSize]
    exact activeRep.size_height
  have unique := (represented_core_ordered activeRep (referenceCuts_source_ordered reference p)).imp
    (fun less => Nat.ne_of_lt less)
  exact ⟨left,right,work,execution,suffixRep,joinedRep,
    splay_exchange_amortized execution unique activeRep.size_height fits⟩

end ChaCha.Paper20261030.SplayAuxiliary
