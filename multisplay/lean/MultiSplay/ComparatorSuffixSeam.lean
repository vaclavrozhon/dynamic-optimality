import MultiSplay.ComparatorSuffixMemory
import MultiSplay.ComparatorSeam
import ChaCha.Paper20261030.SecondaryDecomposition

/-!
# The boundary seam is derived from the actual induced suffix

Follow the original reference route to the suffix start. Surviving crossing
intervals are structural and point left. The first untouched original
subtree is the genuine continuation. Its represented physical component
and every boundary sibling are extracted from the current representation;
they are not arbitrary future components or assumed preservation data.
-/

namespace MultiSplay.ComparatorSuffix

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition

theorem boundary_context_of_subset {x y a b : Nat} (original : DepthTree x y)
    (reference : DepthTree a b) (included : reference.nodes ⊆ original.nodes)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b) (memory : DepthSplit → Bool)
    (joined : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source (suffix reference start lower upper) (preference original start memory)) joined) :
    ∃ endDepth, ∃ genuine : DepthTree start endDepth,
      ∃ (continuation : AuxiliaryComponent Nat Nat (Tagged Payload))
        (frames : List (ContextFrame (α := Nat) followsRight)),
      genuine.nodes ⊆ original.nodes ∧
      Represents followsRight (source genuine memory) continuation ∧
      Equivalent joined (PreferredContext.wrap continuation frames) ∧
      PreferredContext.before frames = [] ∧
      PreferredContext.plug (source genuine memory) frames =
        source (suffix reference start lower upper) (preference original start memory) := by
  induction reference generalizing start joined with
  | leaf a =>
      have equal : start = a := by omega
      subst start
      exact ⟨a,.leaf a,joined,[],by simp [DepthTree.nodes],represented,.refl _,rfl,rfl⟩
  | @node a b cut ha hb left right ihl ihr =>
      by_cases begins : start = a
      · subst start
        let full := DepthTree.node cut ha hb left right
        have unchanged : source full (preference original a memory) = source full memory := by
          apply source_congr
          intro split member
          exact preference_genuine original a memory (included member) (full.node_bounds member).1
        have sourceEq : source (suffix full a le_rfl upper) (preference original a memory) = source full memory := by
          rw [suffix_minimum,unchanged]
        refine ⟨b,full,joined,[],included,?_,.refl _,rfl,sourceEq.symm⟩
        change Represents followsRight
          (source (suffix full a le_rfl upper) (preference original a memory)) joined at represented
        rwa [sourceEq] at represented
      · have structural : a < start := by omega
        by_cases retained : start ≤ cut
        · have rootMember : (⟨a,cut,b⟩ : DepthSplit) ∈ original.nodes :=
            included (by simp [DepthTree.nodes])
          have rootBit : preference original start memory ⟨start,cut,b⟩ = false := by
            simp only [preference,original_of_cut original rootMember,if_pos structural]
          let record : Cached := (0,⟨cut,((⟨start,cut,b⟩,preference original start memory ⟨start,cut,b⟩),false)⟩)
          have shaped : Represents followsRight
              (.fork record (source (suffix left start lower retained) (preference original start memory))
                (source right (preference original start memory))) joined := by
            simpa only [suffix,dif_pos retained,source] using represented
          obtain ⟨lc,rc,leftRep,rightRep,same⟩ := shaped.left_view rootBit
          have leftIncluded : left.nodes ⊆ original.nodes := by
            intro split member
            exact included (by simp [DepthTree.nodes,member])
          obtain ⟨endDepth,genuine,continuation,frames,genuineIncluded,continuationRep,innerSame,
            allLeft,sourceEq⟩ := ihl leftIncluded start lower retained lc leftRep
          let frame : ContextFrame (α := Nat) followsRight :=
            .left record (source right (preference original start memory)) rc rfl rootBit rightRep
          have outerSame : Equivalent joined
              (PreferredContext.wrap continuation (frames ++ [frame])) := by
            rw [PreferredContext.wrap_append]
            exact same.trans (innerSame.append _ _ _)
          refine ⟨endDepth,genuine,continuation,frames ++ [frame],genuineIncluded,continuationRep,
            outerSame,?_,?_⟩
          · simp only [PreferredContext.before_append,PreferredContext.before,ContextFrame.before,
              frame,allLeft,List.append_nil]
          · rw [PreferredContext.plug_append]
            simp only [PreferredContext.plug,ContextFrame.applyReference,frame,sourceEq,
              suffix,dif_pos retained,source,record]
        · have rightIncluded : right.nodes ⊆ original.nodes := by
            intro split member
            exact included (by simp [DepthTree.nodes,member])
          have rightRep : Represents followsRight
              (source (suffix right start (by omega) upper) (preference original start memory)) joined := by
            simpa only [suffix,dif_neg retained] using represented
          simpa only [suffix,dif_neg retained] using
            ihr rightIncluded start (by omega) upper joined rightRep

theorem boundary_context {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b) (memory : DepthSplit → Bool)
    (joined : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source (suffix reference start lower upper) (preference reference start memory)) joined) :
    ∃ endDepth, ∃ genuine : DepthTree start endDepth,
      ∃ (continuation : AuxiliaryComponent Nat Nat (Tagged Payload))
        (frames : List (ContextFrame (α := Nat) followsRight)),
      genuine.nodes ⊆ reference.nodes ∧
      Represents followsRight (source genuine memory) continuation ∧
      Equivalent joined (PreferredContext.wrap continuation frames) ∧
      PreferredContext.before frames = [] ∧
      PreferredContext.plug (source genuine memory) frames =
        source (suffix reference start lower upper) (preference reference start memory) :=
  boundary_context_of_subset reference reference (fun _ h => h) start lower upper memory joined represented

/-- The precise seam form is obtained by an actual paid split of every
represented suffix. The extracted continuation keeps its genuine memories. -/
theorem split_boundary_charged {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b) (memory : DepthSplit → Bool)
    (joined : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source (suffix reference start lower upper) (preference reference start memory)) joined) :
    ∃ endDepth, ∃ genuine : DepthTree start endDepth,
      ∃ (continuation administrative : AuxiliaryComponent Nat Nat (Tagged Payload))
        (frames : List (ContextFrame (α := Nat) followsRight)),
      genuine.nodes ⊆ reference.nodes ∧
      Represents followsRight (source genuine memory) continuation ∧
      Equivalent administrative (PreferredContext.wrap (terminal (closed continuation)) frames) ∧
      PreferredContext.before frames = [] ∧
      PreferredContext.plug (source genuine memory) frames =
        source (suffix reference start lower upper) (preference reference start memory) ∧
      SourcePointer.Rearranges (closed joined) (closed administrative)
        (6720 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 90) := by
  obtain ⟨endDepth,genuine,continuation,frames,included,continuationRep,same,allLeft,sourceEq⟩ :=
    boundary_context reference start lower upper memory joined represented
  have height : (PreferredContext.plug (source genuine memory) frames).shape.height ≤
      (LocalReferences.depthReference reference).height := by
    rw [sourceEq,source_shape]
    exact suffix_height reference start lower upper
  obtain ⟨actual,administrative,actualRep,_,adminSame,run⟩ :=
    ComparatorSeam.split_seam (source genuine memory) continuation joined frames continuationRep same
      allLeft (represented_ordered _ _ _ represented) _ height
  exact ⟨endDepth,genuine,actual,administrative,frames,included,actualRep,adminSame,allLeft,sourceEq,run⟩

end MultiSplay.ComparatorSuffix
