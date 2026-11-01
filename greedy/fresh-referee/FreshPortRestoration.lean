import HeapFreshAllocation
import FreshPaidInsertion

/-!
Sequential fresh allocation for actual-parent port restoration. The names
function is produced by execution, with each paid insertion sized from its
actual current receiving state. A root port is skipped without advancing
the reserved counter or creating a logical instance.
-/
namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds Primitives
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem heap_update {n : ℕ} (states : HeapSides n) (owner : External n) (side : Bool) (replacement : SideState) :
    heap (Function.update (table states) (encode n (owner,side)) replacement) =
      replaceSide states owner side replacement := by
  classical
  funext current currentSide
  by_cases place : current=owner ∧ currentSide=side
  · obtain ⟨rfl,rfl⟩ := place
    simp [heap,replaceSide]
  · have different : encode n (current,currentSide)≠encode n (owner,side) := by
      intro equal
      exact place (Prod.mk.inj ((encode n).injective equal))
    simp [heap,table,replaceSide,place,Function.update_of_ne different]

noncomputable def portNames {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (record : External n)
    (start : ℕ) (states : HeapSides n) : PaidNames :=
  match canonicalParent snapshot tree record with
  | none => ⟨start,start,start,start,start⟩
  | some owner => freshPaidNames owner.val (snapshot.rank owner) start
      (states owner (decide (record.val<owner.val)))

noncomputable def restoreNext {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (record : External n)
    (start : ℕ) (states : HeapSides n) : ℕ :=
  match canonicalParent snapshot tree record with
  | none => start
  | some _ => (portNames snapshot tree record start states).paidId+1

theorem restorePort_fresh_inventory {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (start : ℕ) (states : HeapSides n)
    (inventory : HeapInventory states start) :
    HeapInventory (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1
      (restoreNext snapshot tree record start states) := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa only [restorePort,restoreNext,parent] using inventory
  | some owner =>
      let side := decide (record.val<owner.val)
      let slot := encode n (owner,side)
      have supplied := freshPaidSlot_inventory slot owner.val (snapshot.rank owner) side start (makeEntry owner)
        (table states) inventory
      have receiver : table states slot=states owner side := by simp [table,slot]
      have mapped : HeapInventory
          (heap (freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).1)
          (freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).2 := by
        simpa only [HeapInventory,table_heap] using supplied
      dsimp only [freshPaidSlot] at mapped
      rw [receiver,heap_update] at mapped
      simpa only [restorePort,portNames,restoreNext,parent,freshPaidInsertion] using mapped

theorem restoreNext_monotone {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (record : External n)
    (start : ℕ) (states : HeapSides n) : start≤restoreNext snapshot tree record start states := by
  cases parent : canonicalParent snapshot tree record with
  | none => simp [restoreNext,parent]
  | some owner => simp [restoreNext,portNames,parent,freshPaidNames];omega

theorem restorePorts_names_congr {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (first second : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (stage : ℕ) (states : HeapSides n)
    (agree : ∀ query, stage≤query → query<stage+ports.length → first query=second query) :
    restorePorts snapshot tree first makeEntry ports stage states =
      restorePorts snapshot tree second makeEntry ports stage states := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons record rest ih =>
      have head := agree stage (le_refl _) (by simp)
      simp only [restorePorts,head]
      rw [ih (stage+1) _ (by intro query lo hi;apply agree query (by omega);simp only [List.length_cons];omega)]

theorem restorePorts_entries_congr {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (first second : ℕ → External n → External n → Entry)
    (ports : List (External n)) (stage : ℕ) (states : HeapSides n)
    (agree : ∀ query, stage≤query → query<stage+ports.length → first query=second query) :
    restorePorts snapshot tree names first ports stage states =
      restorePorts snapshot tree names second ports stage states := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons record rest ih =>
      have head := agree stage (le_refl _) (by simp)
      simp only [restorePorts,head]
      rw [ih (stage+1) _ (by intro query lo hi;apply agree query (by omega);simp only [List.length_cons];omega)]

structure FreshRestoration (n : ℕ) where
  names : ℕ → PaidNames
  makeEntry : ℕ → External n → External n → Entry
  states : HeapSides n
  next : ℕ

/-- The reader sees the actual state immediately before this paid port's
insertion. Returned immutable entry records retain those snapshot values. -/
noncomputable def freshRestorePorts {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) :
    List (External n) → ℕ → ℕ → HeapSides n → FreshRestoration n
  | [], _, start, states => ⟨fun _ => ⟨start,start,start,start,start⟩,
      fun query => reader query states,states,start⟩
  | record::rest, stage, start, states =>
      let headNames := portNames snapshot tree record start states
      let head := restorePort snapshot tree headNames (reader stage states record) record states
      let tail := freshRestorePorts snapshot tree reader rest (stage+1)
        (restoreNext snapshot tree record start states) head.1
      ⟨fun query => if query=stage then headNames else tail.names query,
        fun query => if query=stage then reader stage states else tail.makeEntry query,
        tail.states,tail.next⟩

theorem freshRestorePorts_inventory {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (ports : List (External n)) (stage start : ℕ)
    (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (freshRestorePorts snapshot tree reader ports stage start states).states
      (freshRestorePorts snapshot tree reader ports stage start states).next := by
  induction ports generalizing stage start states with
  | nil => exact inventory
  | cons record rest ih =>
      exact ih (stage+1) _ _ (restorePort_fresh_inventory snapshot tree record (reader stage states record) start states inventory)

theorem freshRestorePorts_monotone {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (ports : List (External n)) (stage start : ℕ)
    (states : HeapSides n) : start≤(freshRestorePorts snapshot tree reader ports stage start states).next := by
  induction ports generalizing stage start states with
  | nil => exact le_refl _
  | cons record rest ih => exact le_trans (restoreNext_monotone snapshot tree record start states) (ih (stage+1) _ _)

/-- The allocator returns literal parameters for the already verified
restorePorts implementation, including entries read from actual intermediate
states, rather than a separate state transition. -/
theorem freshRestorePorts_eq {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (ports : List (External n)) (stage start : ℕ)
    (states : HeapSides n) :
    let result := freshRestorePorts snapshot tree reader ports stage start states
    (restorePorts snapshot tree result.names result.makeEntry ports stage states).1=result.states := by
  induction ports generalizing stage start states with
  | nil => rfl
  | cons record rest ih =>
      let headNames := portNames snapshot tree record start states
      let head := restorePort snapshot tree headNames (reader stage states record) record states
      let tail := freshRestorePorts snapshot tree reader rest (stage+1)
        (restoreNext snapshot tree record start states) head.1
      let names := fun query => if query=stage then headNames else tail.names query
      let entries := fun query => if query=stage then reader stage states else tail.makeEntry query
      change (restorePorts snapshot tree names entries (record::rest) stage states).1=tail.states
      simp only [restorePorts,names,entries,↓reduceIte]
      have sameNames := restorePorts_names_congr snapshot tree names tail.names entries rest (stage+1) head.1
        (by intro query lo hi;dsimp [names];rw [if_neg (by omega)])
      have sameEntries := restorePorts_entries_congr snapshot tree tail.names entries tail.makeEntry rest (stage+1) head.1
        (by intro query lo hi;dsimp [entries];rw [if_neg (by omega)])
      rw [sameNames,sameEntries]
      exact ih (stage+1) _ _

/-- Any invariant shared by every possible reader call is inherited by the
returned factory, including queries outside the executed range. -/
theorem freshRestorePorts_entry_property {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (property : ℕ → External n → External n → Entry → Prop)
    (readerProperty : ∀ stage current record owner, property stage record owner (reader stage current record owner))
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    ∀ query record owner, property query record owner
      ((freshRestorePorts snapshot tree reader ports stage start states).makeEntry query record owner) := by
  induction ports generalizing stage start states with
  | nil => intro query record owner;exact readerProperty query states record owner
  | cons record rest ih =>
      intro query other owner
      dsimp only [freshRestorePorts]
      split_ifs with equal
      · subst query
        exact readerProperty stage states other owner
      · exact ih (stage+1) _ _ query other owner

theorem freshRestorePorts_keys {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage current record owner, (reader stage current record owner).key=record.val)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    ∀ query record owner, ((freshRestorePorts snapshot tree reader ports stage start states).makeEntry query record owner).key=record.val :=
  freshRestorePorts_entry_property snapshot tree reader (fun _ record _ entry => entry.key=record.val)
    readerKey ports stage start states

theorem freshRestorePorts_times {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (clock : ℕ)
    (readerTime : ∀ stage current record owner, (reader stage current record owner).joined=clock+stage)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    ∀ query record owner, ((freshRestorePorts snapshot tree reader ports stage start states).makeEntry query record owner).joined=clock+query :=
  freshRestorePorts_entry_property snapshot tree reader (fun query _ _ entry => entry.joined=clock+query)
    readerTime ports stage start states

#print axioms restorePort_fresh_inventory
#print axioms freshRestorePorts_inventory
#print axioms freshRestorePorts_eq
#print axioms freshRestorePorts_monotone
#print axioms freshRestorePorts_times

end GreedyMerge.HeapAllocation
