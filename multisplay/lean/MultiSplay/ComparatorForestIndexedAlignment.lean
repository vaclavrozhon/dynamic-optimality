import MultiSplay.ComparatorForestSelectedGeometry
import MultiSplay.ComparatorGuardIndexedExchange
import MultiSplay.ClassicalSwitchLocalization
import MultiSplay.ClassicalSwitchMarkedUpdate

/-!
# Exact indexed locations of the selected reference children

An empty raw tree forgets its interval boundary. The lookup below retains
both bounds together with the indexed subtree, so an incoming or parked
empty component is identified with the actual child at its reference
address. This is ghost reference information; it changes no physical tree
or charged program.
-/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (BST RawTree)
open ChaCha
open Primary (Key)
open EndpointEncoding ClassicalSwitch

abbrev IndexedTree := Σ lower : Nat, Σ upper : Nat, BST lower upper

def pack {lower upper : Nat} (reference : BST lower upper) : IndexedTree :=
  ⟨lower,upper,reference⟩

/-- Lookup stops at an actual indexed empty child; addresses below that
child are absent rather than silently assigned an arbitrary empty bound. -/
def indexedAt : {lower upper : Nat} → BST lower upper → Key → Option IndexedTree
  | _,_,reference,[] => some (pack reference)
  | _,_,.empty _,_::_ => none
  | _,_,.node left _,false::rest => indexedAt left rest
  | _,_,.node _ right,true::rest => indexedAt right rest

theorem indexedAt_append {lower upper childLower childUpper : Nat}
    {reference : BST lower upper} {child : BST childLower childUpper} {address : Key}
    (located : indexedAt reference address = some (pack child)) (rest : Key) :
    indexedAt reference (address ++ rest) = indexedAt child rest := by
  induction address generalizing lower upper with
  | nil =>
      simp only [indexedAt] at located
      have same := Option.some.inj located
      change (⟨lower,upper,reference⟩ : IndexedTree) = ⟨childLower,childUpper,child⟩ at same
      cases same
      rfl
  | cons edge address ih =>
      cases reference with
      | empty => simp [indexedAt] at located
      | node left right =>
          cases edge with
          | false => exact ih located
          | true => exact ih located

theorem otherSlots_indexedAt {lower upper : Nat} (state : State) (reference : BST lower upper) :
    ∀ slot ∈ otherSlots state reference,
      indexedAt reference slot.rootAddress = some (pack slot.primary) := by
  induction reference generalizing state with
  | empty => simp [otherSlots]
  | node left right ihl ihr =>
      intro slot member
      simp only [otherSlots,List.mem_cons,List.mem_append] at member
      rcases member with rfl | inLeft | inRight
      · cases side : state [] <;> simp [Slot.lift,rootSlot,indexedAt]
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp inLeft
        exact ihl (below state false) child present
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp inRight
        exact ihr (below state true) child present

/-- The canonical slots retain the exact interval indices of their actual
reference subtrees, including all empty slots. -/
theorem slots_indexedAt {lower upper : Nat} (state : State) (reference : BST lower upper)
    {slot : Slot} (member : slot ∈ slots state reference) :
    indexedAt reference slot.rootAddress = some (pack slot.primary) := by
  rcases List.mem_cons.mp member with rfl | other
  · simp only [rootSlot,indexedAt]
  · exact otherSlots_indexedAt state reference slot other

theorem slot_primary_eq {lower upper childLower childUpper : Nat}
    {state : State} {reference : BST lower upper} {slot : Slot}
    (member : slot ∈ slots state reference) (child : BST childLower childUpper)
    (located : indexedAt reference slot.rootAddress = some (pack child)) :
    pack slot.primary = pack child :=
  Option.some.inj ((slots_indexedAt state reference member).symm.trans located)

end MultiSplay.ComparatorForest

namespace MultiSplay.ComparatorGuard

open DynamicOptimality (BST)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch
open ComparatorForest (indexedAt pack)

theorem IndexedPath.indexedAt {lo hi bottom top : Nat} {state : State} {reference : BST lo hi}
    {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus) :
    indexedAt reference address = some (pack focus) := by
  induction path with
  | here => simp only [ComparatorForest.indexedAt]
  | left agrees rest ih => exact ih
  | right agrees rest ih => exact ih

end MultiSplay.ComparatorGuard

namespace MultiSplay.ComparatorForest

open DynamicOptimality (BST RawTree)
open ChaCha
open Primary (Key)
open EndpointEncoding ClassicalSwitch

/-- The locally extracted indexed focus is the exact global subtree at
the emitted pivot, not merely a tree with the same raw keys. -/
theorem Pair.focus_indexedAt {lower upper bottom top : Nat} {state : State}
    {reference : BST lower upper} {address : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    {spine : Spine Nat} {focus : BST bottom top}
    (path : ComparatorGuard.IndexedPath (restrict state source.rootAddress) source.primary
      (address.drop (startDepth state address)) spine focus) :
    indexedAt reference address = some (pack focus) := by
  have root := (pair.geometry before after).1
  change source.rootAddress = address.take (startDepth state address) at root
  have located := slots_indexedAt state reference (before.mem_iff.mpr (by simp : source ∈ source::incoming::remainder))
  have combined := indexedAt_append located (address.drop (startDepth state address))
  rw [path.indexedAt,root,List.take_append_drop] at combined
  exact combined

/-- Exact dependent equalities with the two indexed focus children. These
equalities retain even the boundary of an empty incoming or parked child. -/
theorem Pair.child_primaries {lower upper bottom pivot top : Nat} {state : State}
    {reference : BST lower upper} {address : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    {spine : Spine Nat} {left : BST bottom pivot} {right : BST (pivot+1) top}
    (path : ComparatorGuard.IndexedPath (restrict state source.rootAddress) source.primary
      (address.drop (startDepth state address)) spine (.node left right)) :
    pack incoming.primary = (if state address then pack left else pack right) ∧
      pack parked.primary = (if state address then pack right else pack left) := by
  have focus := pair.focus_indexedAt before after path
  have leftAt : indexedAt reference (address++[false]) = some (pack left) := by
    simpa only [indexedAt] using indexedAt_append focus [false]
  have rightAt : indexedAt reference (address++[true]) = some (pack right) := by
    simpa only [indexedAt] using indexedAt_append focus [true]
  have incomingAt := slots_indexedAt state reference
    (before.mem_iff.mpr (by simp : incoming ∈ source::incoming::remainder))
  have parkedAt := slots_indexedAt (toggle state address) reference
    (after.mem_iff.mpr (by simp : parked ∈ target::parked::remainder))
  rw [pair.incoming_root] at incomingAt
  rw [pair.parked_root] at parkedAt
  cases side : state address with
  | false =>
      simp only [side,Bool.not_false] at incomingAt parkedAt
      exact ⟨Option.some.inj (incomingAt.symm.trans rightAt),Option.some.inj (parkedAt.symm.trans leftAt)⟩
  | true =>
      simp only [side,Bool.not_true] at incomingAt parkedAt
      exact ⟨Option.some.inj (incomingAt.symm.trans leftAt),Option.some.inj (parkedAt.symm.trans rightAt)⟩

/-- A dependent indexed equality may be used directly under the ordinary
key projection, without exposing casts to the local comparator program. -/
theorem projectedTree_primary_eq {lower upper : Nat} (state : State) (family : Family)
    (slot : Slot) (primary : BST lower upper) (same : pack slot.primary = pack primary) :
    projectedTree state family slot =
      ComparatorPrimary.projectedTree (restrict state slot.rootAddress) primary
        (startDepth state slot.endpoint)
        (ComparatorRecords.erase (ChaCha.Paper20261030.BoundaryObservations.closed (family slot.endpoint))) := by
  have transported := congrArg (fun indexed : IndexedTree => ComparatorPrimary.projectedTree
    (restrict state slot.rootAddress) indexed.2.2 (startDepth state slot.endpoint)
    (ComparatorRecords.erase (ChaCha.Paper20261030.BoundaryObservations.closed (family slot.endpoint)))) same
  simpa only [projectedTree,pack] using transported

open Paper20261030 ColoredStorage PrimaryWings

theorem Pair.local_state {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder)) :
    restrict (restrict state source.rootAddress) (address.drop (startDepth state address)) =
      restrict state address := by
  have root := (pair.geometry before after).1
  change source.rootAddress = address.take (startDepth state address) at root
  rw [root,← restrict_append,List.take_append_drop]

theorem Pair.local_toggle {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder)) :
    restrict (toggle state address) source.rootAddress =
      toggle (restrict state source.rootAddress) (address.drop (startDepth state address)) := by
  have root := (pair.geometry before after).1
  change source.rootAddress = address.take (startDepth state address) at root
  have decomposition : source.rootAddress ++ address.drop (startDepth state address) = address := by
    rw [root,List.take_append_drop]
  simpa only [decomposition] using restrict_toggle_append state source.rootAddress
    (address.drop (startDepth state address))

/-- The actual incoming and parked indexed slots route through exactly the
new and old children of the selected focus. The post-switch state agrees
inside both proper children. -/
theorem Pair.child_routers {lower upper bottom pivot top : Nat} {state : State}
    {reference : BST lower upper} {address : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    {spine : Spine Nat} {left : BST bottom pivot} {right : BST (pivot+1) top}
    (path : ComparatorGuard.IndexedPath (restrict state source.rootAddress) source.primary
      (address.drop (startDepth state address)) spine (.node left right)) :
    ComparatorPrimary.routing (restrict state incoming.rootAddress) incoming.primary =
      ComparatorGuard.childRouter
        (restrict (restrict state source.rootAddress) (address.drop (startDepth state address)))
        left right (!(state address)) ∧
    ComparatorPrimary.routing (restrict (toggle state address) parked.rootAddress) parked.primary =
      ComparatorGuard.childRouter
        (restrict (restrict state source.rootAddress) (address.drop (startDepth state address)))
        left right (state address) := by
  have children := pair.child_primaries before after path
  rw [pair.local_state before after,pair.incoming_root,restrict_child,
    pair.parked_root,restrict_toggle_child,restrict_child]
  cases side : state address with
  | false =>
      have incomingEq : pack incoming.primary = pack right := by simpa only [side,Bool.false_eq_true,↓reduceIte] using children.1
      have parkedEq : pack parked.primary = pack left := by simpa only [side,Bool.false_eq_true,↓reduceIte] using children.2
      exact ⟨congrArg (fun tree : IndexedTree => ComparatorPrimary.routing (below (restrict state address) true) tree.2.2) incomingEq,
        congrArg (fun tree : IndexedTree => ComparatorPrimary.routing (below (restrict state address) false) tree.2.2) parkedEq⟩
  | true =>
      have incomingEq : pack incoming.primary = pack left := by simpa only [side,↓reduceIte] using children.1
      have parkedEq : pack parked.primary = pack right := by simpa only [side,↓reduceIte] using children.2
      exact ⟨congrArg (fun tree : IndexedTree => ComparatorPrimary.routing (below (restrict state address) false) tree.2.2) incomingEq,
        congrArg (fun tree : IndexedTree => ComparatorPrimary.routing (below (restrict state address) true) tree.2.2) parkedEq⟩

/-- The child alignment is independent of the chosen source tree or its
virtual completion beyond the actual preferred-path terminal. -/
theorem Pair.child_projections {lower upper bottom pivot top : Nat} {state : State}
    {reference : BST lower upper} {address : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    {spine : Spine Nat} {left : BST bottom pivot} {right : BST (pivot+1) top}
    (path : ComparatorGuard.IndexedPath (restrict state source.rootAddress) source.primary
      (address.drop (startDepth state address)) spine (.node left right))
    {ρ : Type*} (start : Nat) (incomingSource oldSource : Source Nat ρ) :
    ComparatorPrimary.projectedTree (restrict state incoming.rootAddress) incoming.primary start incomingSource =
      GapBST.gaps (ComparatorPrimary.projected start
        (ComparatorGuard.childRouter
          (restrict (restrict state source.rootAddress) (address.drop (startDepth state address)))
          left right (!(state address))) incomingSource) ∧
    ComparatorPrimary.projectedTree (restrict (toggle state address) parked.rootAddress) parked.primary start oldSource =
      GapBST.gaps (ComparatorPrimary.projected start
        (ComparatorGuard.childRouter
          (restrict (restrict state source.rootAddress) (address.drop (startDepth state address)))
          left right (state address)) oldSource) := by
  have routers := pair.child_routers before after path
  simp only [ComparatorPrimary.projectedTree,routers.1,routers.2,and_self]

/-- Canonical slot geometry supplies both coverage inequalities required by
the local exchange, including an empty old or incoming child. -/
theorem Pair.child_coverage {lower upper bottom pivot top : Nat} {state : State}
    {reference : BST lower upper} {address : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    {spine : Spine Nat} {left : BST bottom pivot} {right : BST (pivot+1) top}
    (path : ComparatorGuard.IndexedPath (restrict state source.rootAddress) source.primary
      (address.drop (startDepth state address)) spine (.node left right)) :
    (exits (ComparatorGuard.childRouter
      (restrict (restrict state source.rootAddress) (address.drop (startDepth state address)))
      left right (state address))).length ≤ reference.height - (address.length+1) ∧
    (exits (ComparatorGuard.childRouter
      (restrict (restrict state source.rootAddress) (address.drop (startDepth state address)))
      left right (!(state address)))).length ≤ reference.height - (address.length+1) := by
  have routers := pair.child_routers before after path
  have incomingBound := (slots_valid state reference incoming (before.mem_iff.mpr (by simp))).within_height
  have parkedValid := slots_valid (toggle state address) reference parked (after.mem_iff.mpr (by simp))
  have parkedBound := parkedValid.within_height
  rw [pair.incoming_start before,routers.1] at incomingBound
  rw [routers.2,parkedValid.start,pair.parked_root,List.length_append,List.length_singleton] at parkedBound
  constructor <;> omega

end MultiSplay.ComparatorForest
