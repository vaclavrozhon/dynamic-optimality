import ChaCha.Paper20261030.DecompositionHeadRepair
import ChaCha.Paper20261030.SeparatorPathChange

/-!
# Instantiating the maintained decomposition with secondary references

Reference records retain their original split interval and preference.
The additional bit marks physical component entries; it is false in all
open cores and true at reference terminals. Every represented root core
has exactly the separator-sorted preferred-path word, hence is ordered
and has at most the reference height many records. This connects the
generic physical component invariant to the manuscript's depth references.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

abbrev Payload (_ : Nat) := DepthSplit × Bool
abbrev Cached := NodeRecord Nat (Tagged Payload)

def followsRight (record : Cached) : Bool := record.2.2.1.2

def source : {a b : Nat} → DepthTree a b → (DepthSplit → Bool) → Source Nat Cached
  | _,_,.leaf a,_ => .leaf a (0,⟨a,((⟨a,a,a⟩,false),true)⟩)
  | a,b,.node cut _ _ l r,p =>
      .fork (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) (source l p) (source r p)

def markEntry (e : SeparatorPath.Entry) : Sigma (Tagged Payload) := ⟨e.1,(e.2,false)⟩

theorem source_raw {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    Raw (source reference p) := by
  induction reference <;> simp_all [source,Raw,entry]

theorem source_shape {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    (source reference p).shape = LocalReferences.depthReference reference := by
  induction reference <;> simp_all [source,Source.shape,LocalReferences.depthReference]

theorem source_congr {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (h : ∀ split ∈ reference.nodes, p split = q split) : source reference p = source reference q := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    have hp := h ⟨a,cut,b⟩ (by simp [DepthTree.nodes])
    have hl := ihl (fun s hs => h s (by simp [DepthTree.nodes,hs]))
    have hr := ihr (fun s hs => h s (by simp [DepthTree.nodes,hs]))
    simp only [source,hp,hl,hr]

theorem source_flip_root {a b cut : Nat} (ha : a ≤ cut) (hb : cut < b)
    (l : DepthTree a cut) (r : DepthTree (cut + 1) b) (p : DepthSplit → Bool) (fresh : Bool) :
    source (.node cut ha hb l r) (Function.update p ⟨a,cut,b⟩ fresh) =
      .fork (0,⟨cut,((⟨a,cut,b⟩,fresh),false)⟩) (source l p) (source r p) := by
  have hl : source l (Function.update p ⟨a,cut,b⟩ fresh) = source l p := by
    apply source_congr
    intro s hs
    have hbounds := l.node_bounds hs
    have hne : s ≠ ⟨a,cut,b⟩ := by intro he; subst s; simp only at hbounds; omega
    exact Function.update_of_ne hne _ _
  have hr : source r (Function.update p ⟨a,cut,b⟩ fresh) = source r p := by
    apply source_congr
    intro s hs
    have hbounds := r.node_bounds hs
    have hne : s ≠ ⟨a,cut,b⟩ := by intro he; subst s; simp only at hbounds; omega
    exact Function.update_of_ne hne _ _
  simp only [source,Function.update_self,hl,hr]

theorem skeleton_word {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    (fromRecordTree (PathPorts.skeleton followsRight (source reference p))).toListModel =
      (SeparatorPath.word reference p).map markEntry := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : p ⟨a,cut,b⟩ <;>
      simp [source,PathPorts.skeleton,followsRight,hp,fromRecordTree,Impl.toListModel,
        SeparatorPath.word,markEntry,ihl,ihr]

theorem represented_word {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (h : Represents followsRight (source reference p) c) :
    c.core.toListModel = (SeparatorPath.word reference p).map markEntry := by
  rw [h.word,skeleton_word]

theorem represented_ordered {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (h : Represents followsRight (source reference p) c) : c.core.Ordered := by
  change c.core.toListModel.Pairwise _
  rw [represented_word reference p c h,List.pairwise_map]
  simpa only [markEntry,Nat.compare_eq_lt] using SeparatorPath.keys_increasing reference p

theorem represented_size {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (h : Represents followsRight (source reference p) c) :
    c.core.size ≤ (LocalReferences.depthReference reference).height := by
  simpa only [source_shape] using h.size_height

theorem initialize_representation {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    Represents followsRight (source reference p) (initializeMarked followsRight (source reference p)) :=
  initialize_represents followsRight _ (source_raw reference p)

end ChaCha.Paper20261030.SecondaryDecomposition
