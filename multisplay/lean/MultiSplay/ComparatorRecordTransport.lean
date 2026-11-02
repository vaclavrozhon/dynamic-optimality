import ChaCha.Paper20261030.SecondaryDecomposition
import ChaCha.Paper20261030.SourceRecordMap
import ChaCha.Paper20261030.GapBSTRepresentation

/-!
# Reinterpreting ghost interval names without changing an actual BST

The comparator charges rotations of original keys, not computation on its
mathematical interval names. Renaming a secondary interval preserves the
cached sizes, separator keys, preference bits, entry marks, all auxiliary
shapes, and the exact physical gap tree. The maintained decomposition is
transported by proof, rather than postulated after the renaming.
-/

namespace MultiSplay.ComparatorRecords

open ChaCha
open Paper20261030
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition

def value (rename : DepthSplit → DepthSplit) (_key : Nat) (old : Tagged Payload _key) : Tagged Payload _key :=
  ((rename old.1.1,old.1.2),old.2)

def record (rename : DepthSplit → DepthSplit) (old : Cached) : Cached :=
  (old.1,⟨old.2.1,value rename old.2.1 old.2.2⟩)

def component (rename : DepthSplit → DepthSplit)
    (old : AuxiliaryComponent Nat Nat (Tagged Payload)) : AuxiliaryComponent Nat Nat (Tagged Payload) :=
  ⟨old.core.map (value rename),
    (sameKeys_map (t := old.core) (f := value rename)).symm.balanced old.balanced,
    fun i => (old.ports i).mapRecords (record rename)⟩

theorem core_word (rename : DepthSplit → DepthSplit) (tree : Impl Nat (Tagged Payload)) :
    (tree.map (value rename)).toListModel =
      tree.toListModel.map (fun entry => ⟨entry.1,value rename entry.1 entry.2⟩) := by
  induction tree with
  | leaf => rfl
  | inner sz key entry left right ihl ihr =>
      simp only [Impl.map,toListModel_inner,List.map_append,List.map_cons,ihl,ihr]

theorem core_shape_size (rename : DepthSplit → DepthSplit) (tree : Impl Nat (Tagged Payload)) :
    (recordTree (tree.map (value rename))).size = (recordTree tree).size := by
  induction tree <;> simp_all [Impl.map,recordTree,MTR.Tree.size]

theorem encoded (rename : DepthSplit → DepthSplit) (tree : Impl Nat (Tagged Payload))
    (ports : Nat → Source Nat Cached) (base : Nat) :
    GapSource.encode (recordTree (tree.map (value rename)))
      (fun i => (ports i).mapRecords (record rename)) base =
        (GapSource.encode (recordTree tree) ports base).mapRecords (record rename) := by
  induction tree generalizing base with
  | leaf => rfl
  | inner sz key entry left right ihl ihr =>
      simp only [Impl.map,recordTree,GapSource.encode,Source.mapRecords,core_shape_size,ihl,ihr,record]

theorem tree (rename : DepthSplit → DepthSplit) (old : AuxiliaryComponent Nat Nat (Tagged Payload)) :
    (component rename old).tree = old.tree.mapRecords (record rename) :=
  encoded rename old.core old.ports 0

theorem closed_map (rename : DepthSplit → DepthSplit) (old : AuxiliaryComponent Nat Nat (Tagged Payload)) :
    closed (component rename old) = (closed old).mapRecords (record rename) := by
  simp only [closed,tree,Source.mapRecords_root,Source.mapRecords_setRoot]
  rfl

theorem equivalent (rename : DepthSplit → DepthSplit)
    {before after : AuxiliaryComponent Nat Nat (Tagged Payload)} (same : Equivalent before after) :
    Equivalent (component rename before) (component rename after) := by
  refine ⟨?_,?_⟩
  · simp only [component,core_word,same.word]
  · intro i bound
    change (before.ports i).mapRecords _ = (after.ports i).mapRecords _
    rw [same.ports i (by simpa only [component,size_map] using bound)]

theorem append_equivalent (rename : DepthSplit → DepthSplit)
    (old : AuxiliaryComponent Nat Nat (Tagged Payload)) (key : Nat) (entry : Tagged Payload key)
    (sibling : Source Nat Cached) :
    Equivalent (component rename (append old key entry sibling))
      (append (component rename old) key (value rename key entry) (sibling.mapRecords (record rename))) := by
  refine ⟨?_,?_⟩
  · change ((append old key entry sibling).core.map _).toListModel = _
    rw [core_word,append_word,append_word]
    simp only [component,core_word,List.map_append,List.map_cons,List.map_nil]
  · intro i _
    simp only [component,append,size_map]
    split <;> rfl

theorem prepend_equivalent (rename : DepthSplit → DepthSplit)
    (old : AuxiliaryComponent Nat Nat (Tagged Payload)) (key : Nat) (entry : Tagged Payload key)
    (sibling : Source Nat Cached) :
    Equivalent (component rename (prepend key entry sibling old))
      (prepend key (value rename key entry) (sibling.mapRecords (record rename)) (component rename old)) := by
  refine ⟨?_,?_⟩
  · change ((prepend key entry sibling old).core.map _).toListModel = _
    rw [core_word,prepend_word,prepend_word]
    simp only [component,core_word,List.map_cons]
  · intro i _
    simp only [component,prepend]
    split <;> rfl

theorem represents (rename : DepthSplit → DepthSplit) {logical : Source Nat Cached}
    {physical : AuxiliaryComponent Nat Nat (Tagged Payload)}
    (represented : Represents followsRight logical physical) :
    Represents followsRight (logical.mapRecords (record rename)) (component rename physical) := by
  induction represented with
  | leaf marked same =>
      exact .leaf marked (equivalent rename same)
  | @left old left right lc rc physical direction clean leftRep rightRep same ihl ihr =>
      apply Represents.left (record := record rename old) direction clean ihl ihr
      have mapped := (equivalent rename same).trans (append_equivalent rename lc old.2.1 old.2.2 (closed rc))
      simpa only [closed_map,record] using mapped
  | @right old left right lc rc physical direction clean leftRep rightRep same ihl ihr =>
      apply Represents.right (record := record rename old) direction clean ihl ihr
      have mapped := (equivalent rename same).trans (prepend_equivalent rename rc old.2.1 old.2.2 (closed lc))
      simpa only [closed_map,record] using mapped

theorem lastKey_map (rename : DepthSplit → DepthSplit) (logical : Source Nat Cached) :
    GapBST.lastKey (logical.mapRecords (record rename)) = GapBST.lastKey logical := by
  induction logical <;> simp_all [Source.mapRecords,GapBST.lastKey]

theorem gaps_map (rename : DepthSplit → DepthSplit) (logical : Source Nat Cached) :
    GapBST.gaps (logical.mapRecords (record rename)) = GapBST.gaps logical := by
  induction logical <;> simp_all [Source.mapRecords,GapBST.gaps,lastKey_map]

/-- These are identical ordinary BSTs, so no preparation or rotation is
hidden in the logical interval-name transport. -/
theorem physical_eq (rename : DepthSplit → DepthSplit)
    (old : AuxiliaryComponent Nat Nat (Tagged Payload)) :
    GapBST.gaps (closed (component rename old)) = GapBST.gaps (closed old) := by
  rw [closed_map,gaps_map]


/-- Erasing ghost records leaves exactly the same source, including all
external gaps. This form composes directly with primary unfolding. -/
def erase {α ρ : Type*} (source : Source α ρ) : Source α Unit :=
  source.mapRecords (fun _ => ())

theorem erase_map {α ρ τ : Type*} (rename : ρ → τ) (source : Source α ρ) :
    erase (source.mapRecords rename) = erase source := by
  induction source <;> simp_all [erase,Source.mapRecords]

theorem erase_component (rename : DepthSplit → DepthSplit)
    (old : AuxiliaryComponent Nat Nat (Tagged Payload)) :
    erase (closed (component rename old)) = erase (closed old) := by
  rw [closed_map,erase_map]

end MultiSplay.ComparatorRecords
