import MultiSplay.ComparatorPreparedSuffixSeam
import MultiSplay.ComparatorTailMemory
import TangoSquared.Paper20261030.MarkedJoin

/-! # Restoring an incoming tail at an existing separator

The incoming component has depths `d+1,...,b`; it contains no sentinel key
`d`. Its concrete represented boundary context determines where the
already existing separator `d` belongs. The context is extracted from the
incoming component itself, so its actual off-path components persist.
-/

namespace MultiSplay.ComparatorIncomingSeam

open TangoSquared
open Paper20261030
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition

/-- Recover the exact context simultaneously for the incoming tail and
for the same tail with its existing boundary separator attached. -/
theorem incoming_context {a b : Nat} (reference : DepthTree a b)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d < b)
    (prepared : (Secondary.decodeDepth reference memory).terminal = d)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference memory (d+1) ⟨by omega,by omega⟩) component) :
    ∃ endDepth, ∃ genuine : DepthTree (d+1) endDepth,
      ∃ (continuation : AuxiliaryComponent Nat Nat (Tagged Payload))
        (frames : List (ContextFrame (α := Nat) followsRight)) (pivot : Cached),
      pivot.2.1 = d ∧ entry pivot = false ∧ followsRight pivot = false ∧
      genuine.nodes ⊆ reference.nodes ∧
      Represents followsRight (source genuine memory) continuation ∧
      Equivalent component (PreferredContext.wrap continuation frames) ∧
      PreferredContext.before frames = [] ∧
      PreferredContext.plug (source genuine memory) frames =
        suffixSource reference memory (d+1) ⟨by omega,by omega⟩ ∧
      PreferredContext.plug (.fork pivot (terminalLeaf d) (source genuine memory)) frames =
        suffixSource reference memory d ⟨valid.1,by omega⟩ := by
  induction reference generalizing component with
  | leaf a => omega
  | @node a b cut ha hb left right ihl ihr =>
      cases bit : memory ⟨a,cut,b⟩ with
      | false =>
          have endpoint : (Secondary.decodeDepth left memory).terminal = d := by
            simpa only [Secondary.decodeDepth,PreferredProjection.PrefRouter.terminal,bit,
              Bool.false_eq_true,if_false] using prepared
          have bounds := (Secondary.decodeDepth_mem left memory d).mp
            (by rw [← endpoint]; exact PreferredProjection.PrefRouter.terminal_mem _)
          let record : Cached := (0,⟨cut,((⟨a,cut,b⟩,memory ⟨a,cut,b⟩),false)⟩)
          by_cases atCut : d = cut
          · cases atCut.symm
            have rightRep : Represents followsRight (source right memory) component := by
              simpa only [suffixSource,dif_neg (by omega : ¬d+1 ≤ d),suffixSource_minimum] using represented
            refine ⟨b,right,component,[],record,rfl,rfl,bit,?_,rightRep,.refl _,rfl,?_,?_⟩
            · intro split member
              simp [DepthTree.nodes,member]
            · simp only [PreferredContext.plug,suffixSource,dif_neg (by omega : ¬d+1 ≤ d),suffixSource_minimum]
            · simp only [PreferredContext.plug,suffixSource,dif_pos le_rfl,
                ComparatorPreparedSuffix.suffixSource_maximum left memory bounds.1,record]
          · have strict : d < cut := by omega
            have shaped : Represents followsRight
                (.fork record (suffixSource left memory (d+1) ⟨by omega,by omega⟩) (source right memory)) component := by
              simpa only [suffixSource,dif_pos (show d+1 ≤ cut by omega)] using represented
            obtain ⟨lc,rc,leftRep,rightRep,same⟩ := shaped.left_view bit
            obtain ⟨endDepth,genuine,continuation,frames,pivot,key,clean,direction,included,
              continuationRep,contSame,allLeft,sourceEq,insertedEq⟩ := ihl ⟨bounds.1,strict⟩ endpoint lc leftRep
            let frame : ContextFrame (α := Nat) followsRight :=
              .left record (source right memory) rc rfl bit rightRep
            refine ⟨endDepth,genuine,continuation,frames ++ [frame],pivot,key,clean,direction,
              ?_,continuationRep,?_,?_,?_,?_⟩
            · intro split member
              have present := included member
              simp [DepthTree.nodes,present]
            · rw [PreferredContext.wrap_append]
              exact same.trans (contSame.append _ _ _)
            · simp only [PreferredContext.before_append,PreferredContext.before,ContextFrame.before,
                frame,allLeft,List.append_nil]
            · rw [PreferredContext.plug_append]
              simp only [PreferredContext.plug,ContextFrame.applyReference,frame,sourceEq,
                suffixSource,dif_pos (show d+1 ≤ cut by omega),record]
            · rw [PreferredContext.plug_append]
              simp only [PreferredContext.plug,ContextFrame.applyReference,frame,insertedEq,
                suffixSource,dif_pos bounds.2,record]
      | true =>
          have endpoint : (Secondary.decodeDepth right memory).terminal = d := by
            simpa only [Secondary.decodeDepth,PreferredProjection.PrefRouter.terminal,bit,if_true] using prepared
          have bounds := (Secondary.decodeDepth_mem right memory d).mp
            (by rw [← endpoint]; exact PreferredProjection.PrefRouter.terminal_mem _)
          have rightRep : Represents followsRight
              (suffixSource right memory (d+1) ⟨by omega,by omega⟩) component := by
            simpa only [suffixSource,dif_neg (by omega : ¬d+1 ≤ cut)] using represented
          obtain ⟨endDepth,genuine,continuation,frames,pivot,key,clean,direction,included,
            continuationRep,same,allLeft,sourceEq,insertedEq⟩ := ihr ⟨bounds.1,valid.2⟩ endpoint component rightRep
          refine ⟨endDepth,genuine,continuation,frames,pivot,key,clean,direction,
            ?_,continuationRep,same,allLeft,?_,?_⟩
          · intro split member
            have present := included member
            simp [DepthTree.nodes,present]
          · simpa only [suffixSource,dif_neg (by omega : ¬d+1 ≤ cut)] using sourceEq
          · simpa only [suffixSource,dif_neg (by omega : ¬d ≤ cut)] using insertedEq


/-- Adding a first record commutes with an all-left outer context. This
is equality of every port, not just equality of separator inventories. -/
theorem prepend_wrap (key : Nat) (value : Tagged Payload key) (left : Source Nat Cached)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (frames : List (ContextFrame (α := Nat) followsRight))
    (allLeft : PreferredContext.before frames = []) :
    Equivalent (prepend key value left (PreferredContext.wrap component frames))
      (PreferredContext.wrap (prepend key value left component) frames) := by
  induction frames generalizing component with
  | nil => exact .refl _
  | cons frame frames ih =>
      obtain ⟨restEmpty,frameEmpty⟩ := List.append_eq_nil_iff.mp allLeft
      cases frame with
      | left record sibling outside clean direction represented =>
          have swap : Equivalent
              (prepend key value left (append component record.2.1 record.2.2 (closed outside)))
              (append (prepend key value left component) record.2.1 record.2.2 (closed outside)) := by
            apply equivalent_of_words
            · simp only [prepend_word,append_word,List.cons_append]
            · simp only [prepend_portWord,append_portWord,List.cons_append]
          exact (ih _ restEmpty).trans (PreferredContext.equivalent frames swap)
      | right record sibling outside clean direction represented =>
          simp only [ContextFrame.before,List.cons_ne_self] at frameEmpty

theorem join_terminal_prepend (key : Nat) (value : Tagged Payload key) (left : Source Nat Cached)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload)) :
    Equivalent (join key value (terminal left) component) (prepend key value left component) := by
  apply equivalent_of_words
  · simp only [join_word,prepend_word,terminal,toListModel_leaf,List.nil_append]
  · rw [join_portWord,prepend_portWord]
    simp [portWord,terminal,size_leaf]

theorem pivot_terminal_equivalent (pivot : Cached) (d : Nat)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload)) :
    Equivalent (prepend pivot.2.1 pivot.2.2 (terminalLeaf d) (terminal (closed component)))
      (append (terminal (terminalLeaf d)) pivot.2.1 pivot.2.2 (closed component)) := by
  apply equivalent_of_words
  · simp only [prepend_word,append_word,terminal,toListModel_leaf,List.nil_append]
  · rw [prepend_portWord,append_portWord]
    simp [portWord,terminal,size_leaf]

/-- Split the actual incoming boundary seam, then incorporate the existing
separator into that seam. The result is proved to represent the enlarged
prepared suffix. The initial fork already contains the separator: this
operation allocates no key or sentinel. -/
theorem attach_charged {a b : Nat} (reference : DepthTree a b)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d < b)
    (prepared : (Secondary.decodeDepth reference memory).terminal = d)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference memory (d+1) ⟨by omega,by omega⟩) component)
    (ordered : component.core.Ordered) :
    ∃ (pivot : Cached) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      pivot.2.1 = d ∧ entry pivot = false ∧ followsRight pivot = false ∧
      Represents followsRight (suffixSource reference memory d ⟨valid.1,by omega⟩) out ∧
      SourcePointer.Rearranges (.fork pivot (terminalLeaf d) (closed component)) (closed out)
        (7215 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 178) := by
  obtain ⟨endDepth,genuine,continuation,frames,pivot,key,clean,direction,included,
    continuationRep,same,allLeft,sourceEq,insertedEq⟩ :=
      incoming_context reference memory d valid prepared component represented
  have height : (PreferredContext.plug (source genuine memory) frames).shape.height ≤
      (LocalReferences.depthReference reference).height := by
    rw [sourceEq]
    exact suffixSource_height reference memory (d+1) _
  obtain ⟨actual,administrative,actualRep,actualSame,adminSame,split⟩ :=
    ComparatorSeam.split_seam (source genuine memory) continuation component frames
      continuationRep same allLeft ordered _ height
  let first := terminal (terminalLeaf d)
  let out := join pivot.2.1 pivot.2.2 first administrative
  have firstRep : Represents followsRight (terminalLeaf d) first := .leaf rfl (.refl _)
  have insertedRep : Represents followsRight (.fork pivot (terminalLeaf d) (source genuine memory))
      (append first pivot.2.1 pivot.2.2 (closed actual)) :=
    .left direction clean firstRep actualRep (.refl _)
  have outSame : Equivalent out
      (PreferredContext.wrap (append first pivot.2.1 pivot.2.2 (closed actual)) frames) :=
    (join_terminal_prepend pivot.2.1 pivot.2.2 (terminalLeaf d) administrative).trans
      ((adminSame.prepend pivot.2.1 pivot.2.2 (terminalLeaf d)).trans
        ((prepend_wrap pivot.2.1 pivot.2.2 (terminalLeaf d) (terminal (closed actual)) frames allLeft).trans
          (PreferredContext.equivalent frames (pivot_terminal_equivalent pivot d actual))))
  have outRep := (PreferredContext.represents frames insertedRep).equivalent outSame
  rw [insertedEq] at outRep
  have adminInvariant := ComparatorSeam.wrap_invariant (terminal (closed actual)) frames
    True.intro (fun _ _ => closed_entry actual)
  have adminClean := adminSame.clean adminInvariant.1
  have adminMarked := adminSame.marked adminInvariant.2
  have join := joinMarked_charged pivot.2.1 pivot.2.2 first administrative
    True.intro adminClean (fun _ _ => rfl) adminMarked pivot.1
  have firstClosed : closed first = terminalLeaf d := by
    rw [closed_terminal first rfl (fun _ _ => rfl)]
    rfl
  rw [firstClosed] at join
  have full := (split.right (l := terminalLeaf d) (record := pivot)).trans join
  have sizes : administrative.core.size ≤ (LocalReferences.depthReference reference).height := by
    rw [adminSame.size,PreferredContext.size]
    have sourceSize := (PreferredContext.represents frames continuationRep).size_height.trans height
    rw [PreferredContext.size] at sourceSize
    change 0 + frames.length ≤ _
    omega
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right sizes 1)
  refine ⟨pivot,out,key,clean,direction,outRep,full.mono ?_⟩
  simp only [first,terminal,size_leaf,Nat.zero_add,Nat.clog_one_right,Nat.add_zero] at *
  omega

end MultiSplay.ComparatorIncomingSeam
