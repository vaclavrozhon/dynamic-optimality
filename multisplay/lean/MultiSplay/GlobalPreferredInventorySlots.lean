import MultiSplay.GlobalPreferredInventoryInitial

/-!
# Empty slots and exact pair replacement

There are always more analytical slots than real keys. Therefore an empty
incoming component can use an existing empty slot. Pair replacement preserves
the number of slots and does not reset any nonempty auxiliary tree.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open EndpointEncoding ClassicalSwitch CommonForest

variable {α : Type*}

theorem mem_rootPart {tree selected : RawTree α} :
    selected ∈ rootPart tree ↔ selected = tree ∧ tree ≠ .empty := by
  cases tree <;> simp [rootPart]

theorem mem_core_part {trees : List (RawTree α)} {selected : RawTree α} :
    selected ∈ trees.flatMap rootPart ↔ selected ∈ trees ∧ selected ≠ .empty := by
  simp only [List.mem_flatMap,mem_rootPart]
  constructor
  · rintro ⟨tree,member,rfl,nonempty⟩
    exact ⟨member,nonempty⟩
  · rintro ⟨member,nonempty⟩
    exact ⟨selected,member,rfl,nonempty⟩

theorem empty_slot {trees : List (RawTree α)}
    (room : (trees.map Tree.size).sum < trees.length) : Tree.empty ∈ trees := by
  by_contra absent
  have bounded : trees.length ≤ (trees.map Tree.size).sum := by
    have one := List.length_le_sum_of_one_le (trees.map Tree.size) (by
      intro n sizeMember
      obtain ⟨tree,treeMember,rfl⟩ := List.mem_map.mp sizeMember
      cases tree with
      | empty => exact False.elim (absent treeMember)
      | node left key right => simp [Tree.size]; omega)
    simpa only [List.length_map] using one
  omega

/-- Extract the exact selected physical pair, including an existing empty
slot when the incoming tree is empty. The remainder's nonempty inventory
is precisely the old remainder. -/
theorem extract_pair {trees remainder : List (RawTree α)} {source incoming : RawTree α}
    (sourceNonempty : source ≠ .empty)
    (room : (trees.map Tree.size).sum < trees.length)
    (parts : (trees.flatMap rootPart).Perm (rootPart source ++ rootPart incoming ++ remainder)) :
    ∃ rest, trees.Perm (source :: incoming :: rest) ∧
      (rest.flatMap rootPart).Perm remainder := by
  classical
  have sourceMember : source ∈ trees := by
    apply (mem_core_part.mp ?_).1
    apply parts.mem_iff.mpr
    simp [rootPart_nonempty sourceNonempty]
  have first := List.perm_cons_erase sourceMember
  have firstPart := (first.flatMap_right rootPart).symm.trans parts
  simp only [List.flatMap_cons,rootPart_nonempty sourceNonempty,List.singleton_append] at firstPart
  have remaining := firstPart.cons_inv
  have incomingMember : incoming ∈ trees.erase source := by
    by_cases nonempty : incoming = .empty
    · subst incoming
      have present := first.mem_iff.mp (empty_slot room)
      rcases List.mem_cons.mp present with equal | member
      · exact False.elim (sourceNonempty equal.symm)
      · exact member
    · apply (mem_core_part.mp ?_).1
      apply remaining.mem_iff.mpr
      simp [rootPart_nonempty nonempty]
  have second := List.perm_cons_erase incomingMember
  refine ⟨(trees.erase source).erase incoming,first.trans (second.cons source),?_⟩
  have rest := (second.flatMap_right rootPart).symm.trans remaining
  simp only [List.flatMap_cons] at rest
  cases incoming with
  | empty => simpa [rootPart] using rest
  | node left key right =>
      exact (show (.node left key right :: List.flatMap rootPart ((trees.erase source).erase
        (.node left key right))).Perm (.node left key right :: remainder) from rest).cons_inv

private theorem trace_inventory [DecidableEq α]
    {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (run : SplayTrace before word after cost) (key : α) :
    Accounting.liveCount after key = Accounting.liveCount before key + Accounting.change word key := by
  induction run with
  | nil => simp [Accounting.change]
  | cons step rest ih =>
      have head := Accounting.step_inventory step key
      rw [Accounting.change_append]
      omega

theorem trace_mass [DecidableEq α] {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (run : SplayTrace before word after cost) (balanced : Accounting.Balanced word) :
    (after.map Tree.size).sum = (before.map Tree.size).sum := by
  classical
  have perm : (after.flatMap Tree.inorder).Perm (before.flatMap Tree.inorder) := by
    apply List.perm_iff_count.mpr
    intro key
    have conserved := trace_inventory run key
    rw [balanced key,Int.add_zero] at conserved
    unfold Accounting.liveCount at conserved
    exact_mod_cast conserved
  have lengths := perm.length_eq
  simpa only [List.length_flatMap,Tree.length_inorder] using lengths

/-- Lift one literal local word to the persistent analytical forest. Both
the word and its exact cost are unchanged; only zero-cost permutations and
the unchanged forest context are inserted. -/
theorem inventory_pair [DecidableEq α] {state nextState : State} {reference before after : RawTree α}
    {trees core nextCore remainder : List (RawTree α)}
    {source incoming target parked : RawTree α} {word : List (Event α)} {cost : Nat}
    (inventory : Inventory state reference before trees)
    (next : Core nextState reference after nextCore)
    (same : (trees.flatMap rootPart).Perm core)
    (first : core.Perm (rootPart source ++ rootPart incoming ++ remainder))
    (last : nextCore.Perm (rootPart target ++ rootPart parked ++ remainder))
    (sourceNonempty : source ≠ .empty)
    (run : SplayTrace [source,incoming] word [target,parked] cost)
    (balanced : Accounting.Balanced word) :
    ∃ result, Inventory nextState reference after result ∧ SplayTrace trees word result cost := by
  obtain ⟨stored,represented,storedOrder,length,mass⟩ := inventory
  obtain ⟨rest,reorder,restOrder⟩ := extract_pair sourceNonempty (by omega) (same.trans first)
  let result := target :: parked :: rest
  have trace : SplayTrace trees word result cost := by
    have main := run.context [] rest
    simpa only [List.nil_append,List.cons_append,List.nil_append,Nat.zero_add] using
      Trace.cons (Step.reorder reorder) main
  refine ⟨result,⟨nextCore,next,?_,?_,?_⟩,trace⟩
  · have remaining := (List.Perm.refl (rootPart target ++ rootPart parked)).append restOrder
    have order : (result.flatMap rootPart).Perm
        (rootPart target ++ rootPart parked ++ remainder) := by
      simpa only [result,List.flatMap_cons,List.append_assoc] using remaining
    exact order.trans last.symm
  · have count := reorder.length_eq
    simp only [result,List.length_cons] at count ⊢
    omega
  · exact (trace_mass trace balanced).trans mass

end MultiSplay.Global.Preferred
