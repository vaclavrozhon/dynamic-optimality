import OrderedPortRestoration

/-!
The general local side-state type permits an absent grower, but a complete
algorithm state keeps two persistent growers for every record. Every
administrative constructor preserves that stronger invariant exactly.
-/
namespace GreedyMerge.OrderedBlocks

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

abbrev PersistentGrowers {n : ℕ} (states : HeapSides n) : Prop :=
  ∀ owner side, (states owner side).grower.isSome = true

theorem conversion_grower_isSome (owner family id base : ℕ) (state : SideState) :
    (convert owner family id base state).grower.isSome = state.grower.isSome := by
  cases same : state.grower with
  | none => simp [convert, same]
  | some grower =>
      by_cases empty : grower.members = [] <;> simp [convert, same, empty]

theorem prepareGrower_grower_isSome {n : ℕ} (before after : BST 0 n) (owner : External n)
    (family id : ℕ) (state : SideState) :
    (prepareGrower before after owner family id state).grower.isSome = state.grower.isSome := by
  unfold prepareGrower
  split_ifs
  · exact conversion_grower_isSome ..
  · rfl

theorem detachPort_grower_isSome (owner family id base key : ℕ) (state : SideState) :
    (detachPort owner family id base key state).grower.isSome = state.grower.isSome := by
  unfold detachPort eraseFrozenKey sealPortSource
  split_ifs
  · exact conversion_grower_isSome ..
  · rfl

theorem paidInsertion_grower_isSome (owner : ℕ) (side : Bool)
    (family id fresh paidId paidFamily base : ℕ) (entry : Primitives.Entry) (state : SideState) :
    (paidInsertion owner side family id fresh paidId paidFamily base entry state).grower.isSome =
      state.grower.isSome := by
  exact conversion_grower_isSome ..

theorem prepareCuts_grower_eq {n : ℕ} (allocate : NameSupply n) (cuts : List (ℕ × ℕ))
    (stage : ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    ((prepareCuts allocate cuts stage states).1 owner side).grower = (states owner side).grower := by
  induction cuts generalizing stage states with
  | nil => rfl
  | cons entry rest ih => exact ih (stage+1) _

theorem detachPorts_grower_isSome {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    ((detachPorts before families ids ports stage states).1 owner side).grower.isSome =
      (states owner side).grower.isSome := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons key rest ih =>
      change ((detachPorts before families ids rest (stage+1)
        (detachAll before key (families stage) (ids stage) states)).1 owner side).grower.isSome = _
      rw [ih]
      exact detachPort_grower_isSome ..

theorem sealOwners_grower_isSome {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    (sealOwners before owners families ids states owner side).grower.isSome =
      (states owner side).grower.isSome := by
  unfold sealOwners
  split_ifs
  · exact conversion_grower_isSome ..
  · rfl

theorem prepareComparator_grower_isSome {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    ((prepareComparator profile families ids ports bulkOwners states).1 owner side).grower.isSome =
      (states owner side).grower.isSome := by
  change ((prepareCuts ids profile.entries (ports.length+2)
    (sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1))
      (detachPorts before families ids ports 1
        (prepareAllGrowers before after (families 0) (ids 0) states)).1)).1 owner side).grower.isSome = _
  rw [prepareCuts_grower_eq, sealOwners_grower_isSome, detachPorts_grower_isSome]
  exact prepareGrower_grower_isSome ..

theorem prepareComparator_bulk_empty {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n)
    (owner : External n) (member : owner ∈ bulkOwners) (side : Bool) :
    growerEntries ((prepareComparator profile families ids ports bulkOwners states).1 owner side).grower = [] := by
  change growerEntries ((prepareCuts ids profile.entries (ports.length+2)
    (sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1))
      (detachPorts before families ids ports 1
        (prepareAllGrowers before after (families 0) (ids 0) states)).1)).1 owner side).grower = []
  rw [prepareCuts_grower_eq]
  exact sealOwners_empty before bulkOwners _ _ _ owner member side

theorem moveJunction_grower_eq {n : ℕ} (oldOwner newOwner : External n) (lo hi : ℕ)
    (fresh : Bool → ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    (moveJunction oldOwner newOwner lo hi fresh states owner side).grower =
      (states owner side).grower := by
  unfold moveJunction
  split_ifs with source receiver
  · subst owner
    rfl
  · subst owner
    rfl
  · rfl

theorem restorePort_grower_isSome {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Primitives.Entry) (record : External n)
    (states : HeapSides n) (owner : External n) (side : Bool) :
    ((restorePort snapshot tree names makeEntry record states).1 owner side).grower.isSome =
      (states owner side).grower.isSome := by
  cases parent : canonicalParent snapshot tree record with
  | none => simp [restorePort, parent]
  | some actualOwner =>
      simp only [restorePort, parent, replaceSide]
      split_ifs with location
      · obtain ⟨ownerEq, sideEq⟩ := location
        subst owner
        subst side
        exact paidInsertion_grower_isSome ..
      · rfl

theorem restorePorts_grower_isSome {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Primitives.Entry)
    (ports : List (External n)) (stage : ℕ) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    ((restorePorts snapshot tree names makeEntry ports stage states).1 owner side).grower.isSome =
      (states owner side).grower.isSome := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons record rest ih =>
      change ((restorePorts snapshot tree names makeEntry rest (stage+1)
        (restorePort snapshot tree (names stage) (makeEntry stage record) record states).1).1 owner side).grower.isSome = _
      rw [ih]
      exact restorePort_grower_isSome ..

#print axioms prepareComparator_grower_isSome
#print axioms prepareComparator_bulk_empty
#print axioms moveJunction_grower_eq
#print axioms restorePorts_grower_isSome

end GreedyMerge.OrderedBlocks
