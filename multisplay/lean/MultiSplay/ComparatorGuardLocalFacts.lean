import MultiSplay.ComparatorGuardPortSelection

/-! # Literal prefix, tail and boundary facts for a local switch -/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality ChaCha Paper20261030
open ColoredStorage PreferredProjection PrimaryWings
open ComparatorPrimary (routing signature lastGap projected)

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem signature_boundary (start : Nat) (primary : PrefRouter Nat)
    (front tail : List (Bool × Nat)) (side : Bool) (value : Nat)
    (ports : signature primary = front ++ (side,value)::tail) :
    PackedPrimary.color start primary (start+front.length) = some side ∧
      lastGap (PackedPrimary.label start primary (start+front.length)).subtree = value := by
  have lookup : portAt start (signature primary) (start+front.length) = some (side,value) := by
    rw [ports]
    simp [portAt,List.getElem?_append_right]
  rw [signature,portAt_map] at lookup
  cases found : portAt start (exits primary) (start+front.length) with
  | none => simp [found] at lookup
  | some exit =>
      have values : exit.leftOfEndpoint = side ∧ lastGap exit.subtree = value := by simpa [found] using lookup
      simp [PackedPrimary.color,PackedPrimary.label,found,values]

theorem prefixWing_congr (start : Nat) (before after : PrefRouter Nat)
    (front old fresh : List (Bool × Nat)) (kept : Option (Source Nat Unit)) (side : Bool)
    (beforePorts : signature before = front++old) (afterPorts : signature after = front++fresh)
    (keys : kept.toList.flatMap (fun tree => tree.shape.leaves) = List.range' start front.length) :
    prefixWing start before side kept = prefixWing start after side kept := by
  cases kept with
  | none => rfl
  | some source =>
      apply boundaryWing_prefix_congr start before after front old fresh side source beforePorts afterPorts
      intro key member
      have word : source.shape.leaves = List.range' start front.length := by simpa using keys
      rw [word] at member
      obtain ⟨index,inside,equal⟩ := List.mem_range'.mp member
      omega

theorem range_leaves_lower (start count : Nat) {ρ : Type*} (source : Source Nat ρ)
    (keys : source.shape.leaves = List.range' start count) :
    ∀ key ∈ source.shape.leaves, start ≤ key := by
  intro key member
  rw [keys] at member
  obtain ⟨index,inside,equal⟩ := List.mem_range'.mp member
  omega

theorem range_ports {ρ : Type*} (start count : Nat) (primary : PrefRouter Nat) (source : Source Nat ρ)
    (keys : source.shape.leaves = List.range' start count)
    (enough : (exits primary).length ≤ count) :
    source.shape.leaves.filterMap (portAt start (exits primary)) = exits primary := by
  rw [keys]
  exact ComparatorPrimary.portAt_extended_word start _ count enough

/-- The terminal boundary belongs to the leaf source, and is absent from
the actual ordinary BST. Its value is fixed by the indexed reference. -/
theorem projected_last {lower upper : Nat} {ρ : Type*} (state : EndpointEncoding.State)
    (reference : BST lower upper) (start count : Nat) (source : Source Nat ρ)
    (keys : source.shape.leaves = List.range' start count)
    (enough : (exits (routing state reference)).length ≤ count) :
    GapBST.lastKey (projected start (routing state reference) source) = upper := by
  have words := (GapBST.gaps_word (projected start (routing state reference) source)).trans
    ((ComparatorPrimary.projected_leaves start (routing state reference) source
      (range_ports start count _ source keys enough)).trans
      (ComparatorPrimary.gapWord_routing state reference))
  have last := congrArg List.getLast? words
  simpa only [List.getLast?_append_cons,List.getLast?_singleton,Option.some.injEq] using last

theorem componentBlock_last {lower upper : Nat} {ρ : Type*} (state : EndpointEncoding.State)
    (reference : BST lower upper) (start count : Nat) (source : Source Nat ρ)
    (keys : source.shape.leaves = List.range' start count)
    (enough : (exits (routing state reference)).length ≤ count) :
    GapBST.lastKey (componentBlock (boundaryWing start (routing state reference) true source)
      ((boundaryWing start (routing state reference) false source).map Source.mirror)
      (routing state reference).terminal) = upper := by
  rw [← projected_erase,last_eraseRecords]
  exact projected_last state reference start count source keys enough

theorem projected_inorder_range {lower upper : Nat} {ρ : Type*} (state : EndpointEncoding.State)
    (reference : BST lower upper) (start count : Nat) (source : Source Nat ρ)
    (keys : source.shape.leaves = List.range' start count)
    (enough : (exits (routing state reference)).length ≤ count) :
    (ComparatorPrimary.projectedTree state reference start source).inorder =
      (ClassicalSwitch.preferred state reference.toRaw).inorder :=
  ComparatorPrimary.projectedTree_inorder state reference start source
    (range_ports start count _ source keys enough)

end MultiSplay.ComparatorGuard
