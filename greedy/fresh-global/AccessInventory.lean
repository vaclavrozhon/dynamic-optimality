import AccessDegree
import HeapFreshAllocation

/-! Fresh allocation for the actual access. The two source conversions
use the finite heap allocator; links preserve every live instance name in
its original owner/side slot. Counter advancement counts reserved names,
whereas rootConversionBirths counts the at-most-two instances created. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.PathPlateau
open GreedyMerge.HeapAllocation GreedyMerge.FreshIds

theorem appendGrower_liveIds (entry : Entry) (state : SideState) :
    liveIds (appendGrower entry state)=liveIds state := by
  cases hg : state.grower <;> simp [appendGrower,liveIds,hg,grow]

theorem linkState_liveIds {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (owner : External n) (side : Bool) :
    liveIds (linkState states source winner loser sourceSide targetSide entry owner side)=
      liveIds (states owner side) := by
  unfold linkState
  split_ifs
  · exact appendGrower_liveIds ..
  · exact eraseFrozenKey_id_support ..
  · rfl

theorem runLinks_liveIds {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : States n) (events : List (External n × External n))
    (owner : External n) (side : Bool) :
    liveIds (runLinks source sourceSide reader clock states events owner side)=liveIds (states owner side) := by
  induction events generalizing clock states with
  | nil => rfl
  | cons event rest ih =>
      rw [runLinks,ih,linkState_liveIds]

theorem inventory_of_same_liveIds {n : ℕ} (before after : States n) (next : ℕ)
    (inventory : HeapInventory before next)
    (same : ∀ owner side, liveIds (after owner side)=liveIds (before owner side)) :
    HeapInventory after next := by
  have tableSame : ∀ slot, liveIds (table after slot)=liveIds (table before slot) := by
    intro slot
    exact same _ _
  refine ⟨?_,?_,?_⟩
  · intro slot
    rw [tableSame]
    exact inventory.localUnique slot
  · intro first second id firstMember secondMember
    rw [tableSame] at firstMember secondMember
    exact inventory.locations first second id firstMember secondMember
  · intro slot id member
    rw [tableSame] at member
    exact inventory.below slot id member

theorem runLinks_inventory {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : States n) (events : List (External n × External n)) (next : ℕ)
    (inventory : HeapInventory states next) :
    HeapInventory (runLinks source sourceSide reader clock states events) next := by
  exact inventory_of_same_liveIds states _ next inventory (runLinks_liveIds source sourceSide reader clock states events)

noncomputable def rootNames {n : ℕ} (source : External n) (start : ℕ) (side : Bool) : ℕ :=
  start+(encode n (source,side)).val

theorem convertRoot_eq_convertHeap {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (start : ℕ) (states : States n) :
    convertRoot rank source (rootNames source start) (rootNames source start) states =
      (convertHeap rank (fun owner _ => decide (owner=source)) start states).1 := by
  funext owner side
  rw [convertHeap_apply]
  by_cases equal : owner=source
  · subst owner
    simp [convertRoot,rootNames]
  · simp [convertRoot,equal]

theorem convertHeap_next {n : ℕ} (rank : ℕ → ℕ)
    (selected : External n → Bool → Bool) (start : ℕ) (states : States n) :
    (convertHeap rank selected start states).2=start+2*(2*n+1) := by
  simp only [convertHeap,freshConversions,slot_count]

theorem convertRoot_inventory {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (start : ℕ) (states : States n) (inventory : HeapInventory states start) :
    HeapInventory (convertRoot rank source (rootNames source start) (rootNames source start) states)
      (start+2*(2*n+1)) := by
  rw [convertRoot_eq_convertHeap]
  rw [←convertHeap_next rank (fun owner _ => decide (owner=source)) start states]
  exact convertHeap_inventory rank _ start states inventory

theorem inventory_shrinking_nodup {n : ℕ} (states : States n) (next : ℕ)
    (inventory : HeapInventory states next) (owner : External n) (side : Bool) :
    ((states owner side).shrinking.map Frozen.id).Nodup := by
  have unique := inventory.localUnique (encode n (owner,side))
  simp only [table,Equiv.symm_apply_apply] at unique
  exact (List.nodup_append.mp unique).1

/-- Execute the exact access with fresh source replacement instances and
return the full ready/allocator invariant for the next operation. -/
theorem actual_access_allocated {n access : ℕ}
    (height : ℕ → ℤ) (raiseTime : ℤ) (comparator oldTree newTree : BST 0 n)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height comparator.depth oldOwner n)
    (newOwners : GreedyMerge.Surface.Owners
      (GreedyMerge.Surface.RaiseSurface height n access raiseTime) comparator.depth newOwner n)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (fresh : ∀ key, key<n → height key<raiseTime)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => comparator.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical
      (GreedyMerge.Surface.RaiseSurface height n access raiseTime)
      (fun key => comparator.depth (newOwner key)) newTree)
    (p : Decomposition oldTree access) (source : External n) (real : source.val=2*access+1)
    (states : States n) (K : ℤ) (clock next : ℕ)
    (ready : Ready comparator oldTree states) (histories : Histories states)
    (beforeClock : BeforeTime clock states) (inventory : HeapInventory states next) :
    ∃ data : AccessScheduleData comparator oldTree newTree p,
      let events := data.events
      let prepared := (convertHeap comparator.externalDepth (fun owner _ => decide (owner=source)) next states).1
      let reader := fun (_ : ℕ) (current : States n) => StateLabels.label comparator.externalDepth K current
      let sourceSide := fun event : External n × External n => decide (event.2.val<source.val)
      let after := runLinks source sourceSide reader clock prepared events
      Ready comparator newTree after ∧ Histories after ∧ BeforeTime (clock+events.length) after ∧
      HeapInventory after (next+2*(2*n+1)) ∧
      StateLabels.label comparator.externalDepth K after =
        GreedyForest.Phase.runLabels comparator.externalDepth (StateLabels.label comparator.externalDepth K states)
          (events.map eventKeys) ∧
      events.length+2=sourceDegree states source ∧
      events.length+rootConversionBirths source states ≤ sourceDegree states source := by
  obtain ⟨data,afterReady,afterHistory,afterClock,afterLabels,eventCount,birthBound⟩ :=
    actual_access_ready height raiseTime comparator oldTree newTree oldOwner newOwner oldOwners newOwners
      global fresh oldCanonical newCanonical p source real (rootNames source next) (rootNames source next)
      states K clock ready histories beforeClock
  simp only [convertRoot_eq_convertHeap] at afterReady afterHistory afterClock afterLabels
  refine ⟨data,afterReady,afterHistory,afterClock,?_,afterLabels,
    data.links_eq_degree global source real states ready,
    data.links_and_births_le_degree global source real states ready⟩
  apply runLinks_inventory
  rw [←convertRoot_eq_convertHeap]
  exact convertRoot_inventory comparator.externalDepth source next states inventory

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.runLinks_inventory
#print axioms GreedyMerge.ActualLinks.convertRoot_inventory
#print axioms GreedyMerge.ActualLinks.actual_access_allocated
