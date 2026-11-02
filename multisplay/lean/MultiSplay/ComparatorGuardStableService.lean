import MultiSplay.ComparatorGuardIndexedExchange

/-! # A complete maintained service of one classical switch

The source transaction retains the old tail and updated main suffix. Its
literal port projection exposes the pivot and the two canonical guards;
the middle program executes exactly the classical split/join word.
-/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality ChaCha Paper20261030
open EndpointEncoding ClassicalSwitch ColoredStorage PreferredProjection PrimaryWings
open AuxiliaryComponent BoundaryObservations PathDecomposition SecondaryDecomposition
open ComparatorPrimary (routing projected projectedTree)
open ComparatorStableSuffix
open Primary (Key)
open CommonForest

theorem child_inorder {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) (side : Bool)
    (start count : Nat) (source : Source Nat Unit)
    (keys : source.shape.leaves = List.range' start count)
    (enough : (exits (childRouter state left right side)).length ≤ count) :
    (GapBST.gaps (projected start (childRouter state left right side) source)).inorder =
      (tail state side (.node left.toRaw pivot right.toRaw)).inorder := by
  cases side
  · exact projected_inorder_range (below state false) left start count source keys enough
  · exact projected_inorder_range (below state true) right start count source keys enough

/-- Every finite preferred reference path, including empty old or incoming
tails, admits the exact maintained classical comparator service. -/
theorem stable_service {lo hi bottom pivot top height : Nat}
    {state : State} {reference : BST lo hi} {address : Key} {spine : Spine Nat}
    {left : BST bottom pivot} {right : BST (pivot+1) top}
    (path : IndexedPath state reference address spine (.node left right))
    (secondary : DepthTree 0 height) (start : Nat)
    (upper : start+address.length < height)
    (old incoming : DepthSplit → Bool)
    (component incomingTail : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource secondary (bits start old) start ⟨Nat.zero_le _,by omega⟩) component)
    (incomingRep : Represents followsRight
      (suffixSource secondary (bits (start+address.length+1) incoming) (start+address.length+1)
        ⟨Nat.zero_le _,by omega⟩) incomingTail)
    (oldEnough : (exits (childRouter (restrict state address) left right ((restrict state address) []))).length ≤
      height+1-(start+address.length+1))
    (incomingEnough : (exits (childRouter (restrict state address) left right (!((restrict state address) [])))).length ≤
      height+1-(start+address.length+1)) :
    ∃ (main tail : AuxiliaryComponent Nat Nat (Tagged Payload)) (work : Nat),
      Represents followsRight
        (suffixSource secondary (bits start (Secondary.spliceBits (start+address.length)
          (ComparatorSuffix.writeGenuine start (start+address.length) old) incoming)) start
          ⟨Nat.zero_le _,by omega⟩) main ∧
      Represents followsRight
        (suffixSource secondary (bits (start+address.length+1) old) (start+address.length+1)
          ⟨Nat.zero_le _,by omega⟩) tail ∧
      Program [projectedTree state reference start (ComparatorRecords.erase (closed component)),
        GapBST.gaps (projected (start+address.length+1)
          (childRouter (restrict state address) left right (!((restrict state address) [])))
          (ComparatorRecords.erase (closed incomingTail)))]
        (eventWord reference.toRaw state address)
        [projectedTree (toggle state address) reference start (ComparatorRecords.erase (closed main)),
          GapBST.gaps (projected (start+address.length+1)
            (childRouter (restrict state address) left right ((restrict state address) []))
            (ComparatorRecords.erase (closed tail)))] work ∧
      work ≤ 100000000 * (ComparatorSuffix.genuineCost secondary start (start+address.length) old+1) *
        seamFactor secondary := by
  obtain ⟨kept,tail,main,tailRep,mainRep,first,last⟩ := stable_exchange secondary start
    (start+address.length) (Nat.zero_le _) (by omega) upper old incoming component incomingTail
    represented incomingRep
  have keptKeys := prefix_word secondary start (start+address.length) (Nat.zero_le _) (by omega) upper old
    component tail represented tailRep kept first
  simp only [Nat.add_sub_cancel_left] at keptKeys
  have tailKeys := ComparatorPrimary.stable_leaf_word secondary (start+address.length+1) _ old tail tailRep
  have incomingKeys := ComparatorPrimary.stable_leaf_word secondary (start+address.length+1) _ incoming incomingTail incomingRep
  obtain ⟨middle,middleBound,middleRun⟩ := indexed_exchange_service path start
    (height+1-(start+address.length+1)) kept (ComparatorRecords.erase (closed tail))
    (ComparatorRecords.erase (closed incomingTail)) keptKeys tailKeys incomingKeys oldEnough incomingEnough
  have oldWord := child_inorder (restrict state address) left right ((restrict state address) [])
    (start+address.length+1) (height+1-(start+address.length+1)) (ComparatorRecords.erase (closed tail)) tailKeys oldEnough
  have incomingWord := child_inorder (restrict state address) left right (!((restrict state address) []))
    (start+address.length+1) (height+1-(start+address.length+1)) (ComparatorRecords.erase (closed incomingTail)) incomingKeys incomingEnough
  have rootSide : restrict state address [] = state address := by simp only [restrict_eq,List.append_nil]
  rw [oldWord,incomingWord,rootSide] at middleRun
  have exactWord : eventWord reference.toRaw state address =
      ClassicalSwitch.word (state address) spine.lower spine.upper
        (ClassicalSwitch.tail (restrict state address) (state address) (.node left.toRaw pivot right.toRaw)).inorder
        (ClassicalSwitch.tail (restrict state address) (!(state address)) (.node left.toRaw pivot right.toRaw)).inorder pivot := by
    simp only [eventWord,path.raw.referenceAt,path.raw.componentSpine,BST.toRaw]
  rw [← exactWord] at middleRun
  obtain ⟨firstWork,firstBound,firstRun⟩ := ComparatorPrimary.projected_program state reference start first
  obtain ⟨lastWork,lastBound,lastRun⟩ := ComparatorPrimary.projected_program (toggle state address) reference start last
  refine ⟨main,tail,firstWork+middle+lastWork,mainRep,tailRep,?_,?_⟩
  · simpa only [List.nil_append,List.append_nil,List.singleton_append,rootSide] using
      ((firstRun.context [] [GapBST.gaps (projected (start+address.length+1)
        (childRouter (restrict state address) left right (!(state address)))
        (ComparatorRecords.erase (closed incomingTail)))]).append middleRun).append
        (lastRun.context [] [GapBST.gaps (projected (start+address.length+1)
          (childRouter (restrict state address) left right (state address))
          (ComparatorRecords.erase (closed tail)))])
  · have positive : 1 ≤ seamFactor secondary := by unfold seamFactor; omega
    nlinarith [Nat.zero_le (ComparatorSuffix.genuineCost secondary start (start+address.length) old * seamFactor secondary)]

end MultiSplay.ComparatorGuard
