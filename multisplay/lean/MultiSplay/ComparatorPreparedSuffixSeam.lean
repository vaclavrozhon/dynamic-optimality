import MultiSplay.ComparatorSeam
import TangoSquared.Paper20261030.PreparedSuffixCut

/-!
# The prepared cut produces the tail boundary seam

After the access to depth `d`, cutting at the existing separator `d`
removes its terminal gap and leaves exactly the administrative boundary
core for depths starting at `d+1`. Its first port is the unchanged genuine
continuation. This is derived from the actual represented component and
the exact balanced split; no tail representation is assumed.
-/

namespace MultiSplay.ComparatorPreparedSuffix

open TangoSquared
open Paper20261030
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition

theorem suffixSource_maximum {a b : Nat} (reference : DepthTree a b)
    (memory : DepthSplit → Bool) (valid : a ≤ b) :
    suffixSource reference memory b ⟨valid,le_rfl⟩ = terminalLeaf b := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb left right ihl ihr =>
      simpa only [suffixSource,dif_neg (by omega : ¬ b ≤ cut)] using ihr (by omega)

theorem prepared_tail_context {a b : Nat} (reference : DepthTree a b)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference memory).terminal = d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference memory d valid) component) :
    ∃ endDepth, ∃ genuine : DepthTree (d+1) endDepth,
      ∃ (continuation : AuxiliaryComponent Nat Nat (Tagged Payload))
        (frames : List (ContextFrame (α := Nat) followsRight)),
      genuine.nodes ⊆ reference.nodes ∧
      Represents followsRight (source genuine memory) continuation ∧
      PreferredContext.before frames = [] ∧
      PreferredContext.plug (source genuine memory) frames =
        suffixSource reference memory (d+1) ⟨by omega,by omega⟩ ∧
      (PreferredContext.wrap (terminal (closed continuation)) frames).core.toListModel =
        component.core.toListModel.filter (fun entry => decide (d < entry.1)) ∧
      (PreferredContext.wrap (terminal (closed continuation)) frames).portWord =
        component.portWord.drop 1 := by
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
          have shaped : Represents followsRight
              (.fork record (suffixSource left memory d bounds) (source right memory)) component := by
            simpa only [suffixSource,dif_pos bounds.2] using represented
          obtain ⟨lc,rc,leftRep,rightRep,same⟩ := shaped.left_view bit
          by_cases atCut : d = cut
          · cases atCut.symm
            have leftLeaf : Represents followsRight (terminalLeaf d) lc := by
              rw [suffixSource_maximum left memory bounds.1] at leftRep
              exact leftRep
            have leafSame : Equivalent lc (terminal (terminalLeaf d)) := by
              cases leftLeaf with
              | leaf marked leafSame => exact leafSame
            refine ⟨b,right,rc,[],?_,rightRep,rfl,?_,?_,?_⟩
            · intro split member
              simp [DepthTree.nodes,member]
            · simp only [PreferredContext.plug,suffixSource,dif_neg (by omega : ¬d+1 ≤ d),
                suffixSource_minimum]
            · rw [same.word,append_word,leafSame.word]
              simp [PreferredContext.wrap,terminal,record]
            · rw [same.portWord,append_portWord,leafSame.portWord]
              simp [PreferredContext.wrap,portWord,terminal,size_leaf]
          · have strict : d < cut := by omega
            obtain ⟨endDepth,genuine,continuation,frames,included,continuationRep,
              allLeft,sourceEq,word,ports⟩ := ihl bounds endpoint strict lc leftRep
            let frame : ContextFrame (α := Nat) followsRight :=
              .left record (source right memory) rc rfl bit rightRep
            refine ⟨endDepth,genuine,continuation,frames ++ [frame],?_,continuationRep,?_,?_,?_,?_⟩
            · intro split member
              have present := included member
              simp [DepthTree.nodes,present]
            · simp only [PreferredContext.before_append,PreferredContext.before,ContextFrame.before,
                frame,allLeft,List.append_nil]
            · rw [PreferredContext.plug_append]
              simp only [PreferredContext.plug,ContextFrame.applyReference,frame,sourceEq,
                suffixSource,dif_pos (show d+1 ≤ cut by omega),record]
            · rw [PreferredContext.wrap_append]
              change (append (PreferredContext.wrap (terminal (closed continuation)) frames)
                record.2.1 record.2.2 (closed rc)).core.toListModel = _
              rw [append_word,same.word,append_word,List.filter_append,word]
              simp only [record,List.filter_cons,decide_eq_true strict,if_true,List.filter_nil]
            · rw [PreferredContext.wrap_append]
              change (append (PreferredContext.wrap (terminal (closed continuation)) frames)
                record.2.1 record.2.2 (closed rc)).portWord = _
              rw [append_portWord,same.portWord,append_portWord,
                List.drop_append_of_le_length (by rw [portWord_length]; omega),ports]
      | true =>
          have endpoint : (Secondary.decodeDepth right memory).terminal = d := by
            simpa only [Secondary.decodeDepth,PreferredProjection.PrefRouter.terminal,bit,if_true] using prepared
          have bounds := (Secondary.decodeDepth_mem right memory d).mp
            (by rw [← endpoint]; exact PreferredProjection.PrefRouter.terminal_mem _)
          have notLeft : ¬ d ≤ cut := by omega
          have rightRep : Represents followsRight (suffixSource right memory d bounds) component := by
            simpa only [suffixSource,dif_neg notLeft] using represented
          obtain ⟨endDepth,genuine,continuation,frames,included,continuationRep,
            allLeft,sourceEq,word,ports⟩ := ihr bounds endpoint upper component rightRep
          refine ⟨endDepth,genuine,continuation,frames,?_,continuationRep,allLeft,?_,word,ports⟩
          · intro split member
            have present := included member
            simp [DepthTree.nodes,present]
          · simpa only [suffixSource,dif_neg (by omega : ¬d+1 ≤ cut)] using sourceEq

/-- Exact representation of the concrete balanced right fragment. The
separator is already present; only its suffix record word is retained. -/
theorem cutRight_seam {a b : Nat} (reference : DepthTree a b)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference memory).terminal = d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference memory d valid) component)
    (found : searchResult d component.core = true) :
    ∃ endDepth, ∃ genuine : DepthTree (d+1) endDepth,
      ∃ (continuation : AuxiliaryComponent Nat Nat (Tagged Payload))
        (frames : List (ContextFrame (α := Nat) followsRight)),
      genuine.nodes ⊆ reference.nodes ∧
      Represents followsRight (source genuine memory) continuation ∧
      Equivalent (cutRight component d found)
        (PreferredContext.wrap (terminal (closed continuation)) frames) ∧
      PreferredContext.before frames = [] ∧
      PreferredContext.plug (source genuine memory) frames =
        suffixSource reference memory (d+1) ⟨by omega,by omega⟩ := by
  obtain ⟨endDepth,genuine,continuation,frames,included,continuationRep,allLeft,sourceEq,word,ports⟩ :=
    prepared_tail_context reference memory d valid prepared upper component represented
  have ordered := represented_suffix_ordered reference memory d valid prepared component represented
  have minimum := represented_suffix_minimum reference memory d valid prepared component represented
  have empty := minimum_left_empty component ordered d found minimum
  refine ⟨endDepth,genuine,continuation,frames,included,continuationRep,?_,allLeft,sourceEq⟩
  apply equivalent_of_words
  · rw [cutRight_word_filter component ordered]
    exact word.symm
  · rw [cutRight_portWord_drop,empty,size_leaf,Nat.zero_add]
    exact ports.symm

/-- Expose the existing boundary key and remove its administrative seam.
The right endpoint is a represented tail on depths `d+1,...,b`, without
the old terminal gap or an extra sentinel separator in that tail. -/
theorem expose_tail_charged {a b : Nat} (reference : DepthTree a b)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference memory).terminal = d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference memory d valid) component) :
    ∃ (tail : AuxiliaryComponent Nat Nat (Tagged Payload)) (boundary : Cached),
      boundary.2.1 = d ∧
      Represents followsRight
        (suffixSource reference memory (d+1) ⟨by omega,by omega⟩) tail ∧
      SourcePointer.Rearranges (closed component)
        (.fork boundary (terminalLeaf d) (closed tail))
        (12450 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 96) := by
  let found := represented_suffix_boundary_found reference memory d valid prepared upper component represented
  let administrative := cutRight component d found
  let boundary : Cached := (component.core.size,⟨d,(splitAt d component.core component.balanced found).value⟩)
  obtain ⟨endDepth,genuine,continuation,frames,_,continuationRep,same,allLeft,sourceEq⟩ :=
    cutRight_seam reference memory d valid prepared upper component represented found
  have height : (PreferredContext.plug (source genuine memory) frames).shape.height ≤
      (LocalReferences.depthReference reference).height := by
    rw [sourceEq]
    exact suffixSource_height reference memory (d+1) _
  have ordered := represented_suffix_ordered reference memory d valid prepared component represented
  obtain ⟨tail,tailRep,_,merged⟩ := ComparatorSeam.merge_seam (source genuine memory)
    continuation administrative frames continuationRep same allLeft
    (cutRight_ordered component ordered d found) _ height
  rw [sourceEq] at tailRep
  obtain ⟨clean,marked⟩ := represented.invariant
  have minimum := represented_suffix_minimum reference memory d valid prepared component represented
  have empty := minimum_left_empty component ordered d found minimum
  have index : gapIndex d component.core = 0 := by
    rw [gapIndex_at_split component ordered d found,empty,size_leaf]
  have exposure := minimum_expose_charged component ordered d found minimum
  rw [index,represented_sentinel_port reference memory d valid prepared component represented] at exposure
  have first := (open_charged component clean marked).trans exposure
  have mergedInside := ((close_charged administrative).trans merged).right
    (l := terminalLeaf d) (record := boundary)
  have whole := first.trans mergedInside
  refine ⟨tail,boundary,rfl,tailRep,whole.mono ?_⟩
  have size := represented_suffix_size reference memory d valid component represented
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  omega

end MultiSplay.ComparatorPreparedSuffix
