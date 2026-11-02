import MultiSplay.ComparatorGuardPorts

/-! # A prefix or tail uses precisely its own reference port interval -/

namespace MultiSplay.ComparatorGuard

open ChaCha Paper20261030 ColoredStorage PreferredProjection PrimaryWings
open ComparatorPrimary (signature)

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def blockLeaves (block : Block Nat) : List Nat := block.toList.flatMap (fun tree => tree.shape.leaves)

@[simp] theorem blockLeaves_join (left right : Block Nat) :
    blockLeaves (join left right) = blockLeaves left ++ blockLeaves right := by
  cases left <;> cases right <;> simp [blockLeaves,join,Source.shape,RouterProjection.Router.leaves]

def selectPort (side : Bool) (entry : Option (Bool × Nat)) : Option Nat :=
  entry.bind (fun port => if port.1 = side then some port.2 else none)

def selectPorts {ρ : Type*} (ports : Nat → Option (Bool × Nat)) (side : Bool) : Source Nat ρ → Block Nat
  | .leaf key _ => (selectPort side (ports key)).map (fun value => .leaf value ())
  | .fork _ left right => join (selectPorts ports side left) (selectPorts ports side right)

theorem selectPorts_congr {ρ : Type*} (first second : Nat → Option (Bool × Nat)) (side : Bool)
    (source : Source Nat ρ) (same : ∀ key ∈ source.shape.leaves, first key = second key) :
    selectPorts first side source = selectPorts second side source := by
  induction source with
  | leaf key record => simp only [selectPorts,same key (by simp [Source.shape,RouterProjection.Router.leaves])]
  | fork record left right ihl ihr =>
      rw [selectPorts,selectPorts,ihl (fun key member => same key (by
        simpa [Source.shape,RouterProjection.Router.leaves] using Or.inl member)),
        ihr (fun key member => same key (by simpa [Source.shape,RouterProjection.Router.leaves] using Or.inr member))]

theorem selectPorts_leaves {ρ : Type*} (ports : Nat → Option (Bool × Nat)) (side : Bool)
    (source : Source Nat ρ) :
    blockLeaves (selectPorts ports side source) = source.shape.leaves.filterMap (fun key => selectPort side (ports key)) := by
  induction source with
  | leaf key record =>
      cases selected : selectPort side (ports key) <;>
        simp [selectPorts,blockLeaves,Source.shape,RouterProjection.Router.leaves,selected]
  | fork record left right ihl ihr =>
      simp only [selectPorts,blockLeaves_join,Source.shape,RouterProjection.Router.leaves,List.filterMap_append,ihl,ihr]

theorem portAt_map {α β : Type*} (f : α → β) (start depth : Nat) (ports : List α) :
    portAt start (ports.map f) depth = (portAt start ports depth).map f := by
  unfold portAt
  split <;> simp [List.getElem?_map]

/-- Packing and collapsing an exit depend only on its side and boundary. -/
theorem boundaryWing_selectPorts {ρ : Type*} (start : Nat) (primary : PrefRouter Nat)
    (side : Bool) (source : Source Nat ρ) :
    boundaryWing start primary side source = selectPorts (portAt start (signature primary)) side source := by
  induction source with
  | leaf key record =>
      simp only [selectPorts,signature,portAt_map]
      cases found : portAt start (exits primary) key with
      | none => simp [boundaryWing,select,PackedPrimary.color,PackedPrimary.label,found,selectPort]
      | some port =>
          by_cases agrees : port.leftOfEndpoint = side <;>
            simp [boundaryWing,select,PackedPrimary.color,PackedPrimary.label,found,selectPort,agrees,Source.relabel]
  | fork record left right ihl ihr =>
      rw [boundaryWing_fork,selectPorts,ihl,ihr]

theorem portAt_front {α : Type*} (start depth : Nat) (front tail : List α)
    (inside : depth < start+front.length) :
    portAt start (front++tail) depth = portAt start front depth := by
  unfold portAt
  split
  · exact List.getElem?_append_left (by omega)
  · rfl

theorem portAt_after {α : Type*} (start depth : Nat) (front tail : List α)
    (below : start+front.length ≤ depth) :
    portAt start (front++tail) depth = portAt (start+front.length) tail depth := by
  simp only [portAt,if_pos (by omega : start ≤ depth),if_pos below]
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

theorem boundaryWing_tail {ρ : Type*} (start afterStart : Nat) (primary child : PrefRouter Nat)
    (front : List (Bool × Nat)) (side : Bool) (source : Source Nat ρ)
    (ports : signature primary = front ++ signature child)
    (offset : afterStart = start+front.length)
    (below : ∀ key ∈ source.shape.leaves, afterStart ≤ key) :
    boundaryWing start primary side source = boundaryWing afterStart child side source := by
  rw [boundaryWing_selectPorts,boundaryWing_selectPorts]
  apply selectPorts_congr
  intro key member
  rw [ports,offset]
  exact portAt_after start key front _ (offset ▸ below key member)

theorem boundaryWing_prefix_congr {ρ : Type*} (start : Nat) (before after : PrefRouter Nat)
    (front old fresh : List (Bool × Nat)) (side : Bool) (source : Source Nat ρ)
    (beforePorts : signature before = front++old) (afterPorts : signature after = front++fresh)
    (inside : ∀ key ∈ source.shape.leaves, key < start+front.length) :
    boundaryWing start before side source = boundaryWing start after side source := by
  rw [boundaryWing_selectPorts,boundaryWing_selectPorts]
  apply selectPorts_congr
  intro key member
  rw [beforePorts,afterPorts,portAt_front start key front old (inside key member),
    portAt_front start key front fresh (inside key member)]

/-- Exact word of one colored prefix wing. -/
theorem prefixWing_word (start : Nat) (primary : PrefRouter Nat)
    (front tail : List (Bool × Nat)) (kept : Option (Source Nat Unit)) (side : Bool)
    (ports : signature primary = front++tail)
    (keys : kept.toList.flatMap (fun tree => tree.shape.leaves) = List.range' start front.length) :
    blockLeaves (prefixWing start primary side kept) =
      (front.filter (fun port => decide (port.1 = side))).map Prod.snd := by
  have filtered : (List.range' start front.length).filterMap
      (fun key => selectPort side (portAt start (front++tail) key)) =
      (front.filter (fun port => decide (port.1 = side))).map Prod.snd := by
    have same : (List.range' start front.length).filterMap
        (fun key => selectPort side (portAt start (front++tail) key)) =
        (List.range' start front.length).filterMap (fun key => selectPort side (portAt start front key)) := by
      apply List.filterMap_congr
      intro key member
      rw [portAt_front start key front tail (by obtain ⟨index,inside,equal⟩ := List.mem_range'.mp member; omega)]
    rw [same]
    change (List.range' start front.length).filterMap
      (fun key => (portAt start front key).bind (fun port => if port.1 = side then some port.2 else none)) = _
    rw [← List.filterMap_filterMap,portAt_word]
    clear ports keys same primary kept tail start
    induction front with
    | nil => rfl
    | cons port rest ih =>
        by_cases agrees : port.1 = side <;> simp [agrees,ih]
  cases kept with
  | none =>
      have empty : front = [] := by
        have length := congrArg List.length keys
        have zero : front.length = 0 := by simpa using length.symm
        exact List.eq_nil_of_length_eq_zero zero
      simp [prefixWing,blockLeaves,empty]
  | some source =>
      simp only [Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil] at keys
      simp only [prefixWing,Option.bind_some,boundaryWing_selectPorts,selectPorts_leaves,keys,ports]
      exact filtered

end MultiSplay.ComparatorGuard
