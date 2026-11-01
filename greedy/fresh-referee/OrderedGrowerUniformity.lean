import OrderedPersistentGrowers

/-!
Every surviving growing entry has the same comparator-rank shift as its
persistent owner. This is established by the actual mismatch selection;
all subsequent administrative operations either keep the grower or empty it.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def GrowerUniform (shift : ℕ → ℤ) (owner : ℕ) (state : SideState) : Prop :=
  ∀ entry ∈ growerEntries state.grower, shift entry.key = shift owner

theorem convert_grower_uniform (shift : ℕ → ℤ) (owner family id base : ℕ) (state : SideState) :
    GrowerUniform shift owner (convert owner family id base state) := by
  intro entry member
  simp only [converted_grower_empty, List.not_mem_nil] at member

theorem prepareGrower_uniform {n : ℕ} (before after : BST 0 n) (owner : External n)
    (family id : ℕ) (state : SideState) :
    GrowerUniform (rankShift before after) owner.val
      (prepareGrower before after owner family id state) := by
  have resolved := prepareGrower_resolves before after owner family id state
  intro entry member
  cases same : (prepareGrower before after owner family id state).grower with
  | none => simp [same,growerEntries] at member
  | some grower =>
      simp only [GrowerMismatch,same] at resolved
      exact not_not.mp (fun mismatch => resolved ⟨entry,by simpa [same,growerEntries] using member,mismatch⟩)

theorem detachPort_grower_uniform (shift : ℕ → ℤ) (owner family id base key : ℕ)
    (state : SideState) (uniform : GrowerUniform shift owner state) :
    GrowerUniform shift owner (detachPort owner family id base key state) := by
  unfold detachPort eraseFrozenKey sealPortSource
  split_ifs
  · exact convert_grower_uniform shift owner family id base state
  · exact uniform

theorem detachPorts_grower_uniform {n : ℕ} (shift : ℕ → ℤ) (before : BST 0 n)
    (families ids : NameSupply n) (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (uniform : ∀ owner side, GrowerUniform shift owner.val (states owner side)) :
    ∀ owner side, GrowerUniform shift owner.val
      ((detachPorts before families ids ports stage states).1 owner side) := by
  induction ports generalizing stage states with
  | nil => exact uniform
  | cons key rest ih =>
      apply ih (stage+1)
      intro owner side
      exact detachPort_grower_uniform _ _ _ _ _ _ _ (uniform owner side)

theorem sealOwners_grower_uniform {n : ℕ} (shift : ℕ → ℤ) (before : BST 0 n)
    (owners : Finset (External n)) (families ids : External n → Bool → ℕ) (states : HeapSides n)
    (uniform : ∀ owner side, GrowerUniform shift owner.val (states owner side)) :
    ∀ owner side, GrowerUniform shift owner.val
      (sealOwners before owners families ids states owner side) := by
  intro owner side
  unfold sealOwners
  split_ifs
  · exact convert_grower_uniform shift owner.val (families owner side) (ids owner side) (before.externalDepth owner.val) (states owner side)
  · exact uniform owner side

theorem prepareComparator_grower_uniform {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n) :
    ∀ owner side, GrowerUniform (rankShift before after) owner.val
      ((prepareComparator profile families ids ports bulkOwners states).1 owner side) := by
  have prepared : ∀ owner side, GrowerUniform (rankShift before after) owner.val
      (prepareAllGrowers before after (families 0) (ids 0) states owner side) := by
    intro owner side
    exact prepareGrower_uniform before after owner (families 0 owner side) (ids 0 owner side) (states owner side)
  have detached := detachPorts_grower_uniform (rankShift before after) before families ids ports 1 _ prepared
  have sealed := sealOwners_grower_uniform (rankShift before after) before bulkOwners
    (families (ports.length+1)) (ids (ports.length+1)) _ detached
  intro owner side
  unfold GrowerUniform
  change ∀ entry ∈ growerEntries ((prepareCuts ids profile.entries (ports.length+2)
    (sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1))
      (detachPorts before families ids ports 1
        (prepareAllGrowers before after (families 0) (ids 0) states)).1)).1 owner side).grower,
      _
  rw [prepareCuts_grower_eq]
  exact sealed owner side

theorem moveJunction_grower_uniform {n : ℕ} (shift : ℕ → ℤ)
    (oldOwner newOwner : External n) (lo hi : ℕ) (fresh : Bool → ℕ) (states : HeapSides n)
    (uniform : ∀ owner side, GrowerUniform shift owner.val (states owner side)) :
    ∀ owner side, GrowerUniform shift owner.val
      (moveJunction oldOwner newOwner lo hi fresh states owner side) := by
  intro owner side
  unfold GrowerUniform
  rw [moveJunction_grower_eq]
  exact uniform owner side

#print axioms prepareComparator_grower_uniform
#print axioms moveJunction_grower_uniform

end GreedyMerge.OrderedBlocks
