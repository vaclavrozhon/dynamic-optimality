import ChaCha.Paper20261030.SourcePayloads
import ChaCha.Paper20261030.LeafVisit

/-!
# Constant record capacity at primary attachment roots

A primary component concatenates its two optional routing wings and its
own bottom leaf. Its root is either an empty-record concatenation vertex
or the bottom leaf carrying its header. Thus the root has at most the
header capacity, independently of all descendant components.

Grafting a source leaf adds its bounded source prefix and one delimiter
at that root. The bound is `sourceCapacity + 1 + headerCapacity`, not a
sum over the number of primary ancestors. Interior payload vertices keep
their already established bound.
-/

namespace ChaCha.Paper20261030.ColoredStorage

variable {α ρ : Type*}

abbrev Source.Bounded (capacity : Nat) (t : Source α (List ρ)) : Prop := t.toStored.Bounded capacity

theorem Source.Bounded.root {capacity : Nat} {t : Source α (List ρ)} (h : t.Bounded capacity) :
    t.rootRecord.length ≤ capacity := by
  cases t with
  | leaf => exact h
  | fork => exact h.1

theorem Source.Bounded.setRoot {capacity : Nat} {t : Source α (List ρ)} (h : t.Bounded capacity)
    (fresh : List ρ) (bound : fresh.length ≤ capacity) : (t.setRoot fresh).Bounded capacity := by
  cases t with
  | leaf => exact bound
  | fork => exact ⟨bound,h.2⟩

end ChaCha.Paper20261030.ColoredStorage

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage

variable {α β ρ : Type*}

theorem graft_bounded (payload : α → Source β (List (Option ρ)))
    (t : Source α (List ρ)) (sourceCapacity headerCapacity capacity : Nat)
    (sourceBound : t.Bounded sourceCapacity)
    (payloadBound : ∀ key, (payload key).Bounded capacity)
    (payloadRoot : ∀ key, (payload key).rootRecord.length ≤ headerCapacity)
    (room : sourceCapacity + 1 + headerCapacity ≤ capacity) : (graft payload t).Bounded capacity := by
  induction t with
  | leaf key records =>
    apply (payloadBound key).setRoot
    simp only [List.length_append,List.length_map,List.length_cons]
    have bound := payloadRoot key
    change records.length ≤ sourceCapacity at sourceBound
    omega
  | fork records l r ihl ihr =>
    refine ⟨?_,ihl sourceBound.2.1,ihr sourceBound.2.2⟩
    change (records.map some).length ≤ capacity
    rw [List.length_map]
    have bound := sourceBound.1
    omega

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.PrimaryPhysical

open ColoredStorage SourcePointer

variable {α ρ : Type*}

abbrev Wing (α ρ : Type*) := Option (Source α (List (Option ρ)))

def component (left right : Wing α ρ) (bottom : α) (header : List ρ) : Source α (List (Option ρ)) :=
  let leaf := Source.leaf bottom (header.map some)
  match left,right with
  | none,none => leaf
  | some l,none => .fork [] l leaf
  | none,some r => .fork [] leaf r
  | some l,some r => .fork [] (.fork [] l leaf) r

def wingLeaves : Wing α ρ → List α
  | none => []
  | some t => t.shape.leaves

def WingBounded (capacity : Nat) : Wing α ρ → Prop
  | none => True
  | some t => t.Bounded capacity

theorem component_root_bound (left right : Wing α ρ) (bottom : α) (header : List ρ) :
    (component left right bottom header).rootRecord.length ≤ header.length := by
  cases left <;> cases right <;> simp [component,Source.rootRecord]

theorem component_root_no_delimiter (left right : Wing α ρ) (bottom : α) (header : List ρ) :
    none ∉ (component left right bottom header).rootRecord := by
  cases left <;> cases right <;> simp [component,Source.rootRecord]

theorem component_bounded (left right : Wing α ρ) (bottom : α) (header : List ρ) (capacity : Nat)
    (leftBound : WingBounded capacity left) (rightBound : WingBounded capacity right)
    (headerBound : header.length ≤ capacity) : (component left right bottom header).Bounded capacity := by
  cases left <;> cases right
  · simpa only [component,Source.Bounded,Source.toStored,Stored.Bounded,List.length_map] using headerBound
  · exact ⟨Nat.zero_le _,by simpa only [Source.toStored,Stored.Bounded,List.length_map] using headerBound,rightBound⟩
  · exact ⟨Nat.zero_le _,leftBound,by simpa only [Source.toStored,Stored.Bounded,List.length_map] using headerBound⟩
  · exact ⟨Nat.zero_le _,⟨Nat.zero_le _,leftBound,by simpa only [Source.toStored,Stored.Bounded,List.length_map] using headerBound⟩,rightBound⟩

theorem component_leaves (left right : Wing α ρ) (bottom : α) (header : List ρ) :
    (component left right bottom header).shape.leaves = wingLeaves left ++ [bottom] ++ wingLeaves right := by
  cases left <;> cases right <;> simp [component,wingLeaves,Source.shape,RouterProjection.Router.leaves]

theorem component_header_visit (left right : Wing α ρ) (bottom : α) (header : List ρ) :
    VisitsLeaf bottom (component left right bottom header) (component left right bottom header) 5 := by
  intro rest
  cases left with
  | none =>
    cases right with
    | none =>
      refine ⟨⟨.leaf bottom (header.map some),rest⟩,header.map some,[],[],0,1,.nil _,rfl,?_,by decide⟩
      exact .read (.nil _)
    | some r =>
      refine ⟨⟨.leaf bottom (header.map some),.left [] r :: rest⟩,header.map some,[],[],1,2,
        .step (.left _ _ _ _) (.nil _),rfl,?_,by decide⟩
      exact .read (.step (.upLeft _ _ _ _) (.nil _))
  | some l =>
    cases right with
    | none =>
      refine ⟨⟨.leaf bottom (header.map some),.right l [] :: rest⟩,header.map some,[],[],1,2,
        .step (.right _ _ _ _) (.nil _),rfl,?_,by decide⟩
      exact .read (.step (.upRight _ _ _ _) (.nil _))
    | some r =>
      refine ⟨⟨.leaf bottom (header.map some),.right l [] :: .left [] r :: rest⟩,header.map some,[],[],2,3,
        .step (.left _ _ _ _) (.step (.right _ _ _ _) (.nil _)),rfl,?_,by decide⟩
      exact .read (.step (.upRight _ _ _ _) (.step (.upLeft _ _ _ _) (.nil _)))

end ChaCha.Paper20261030.PrimaryPhysical
