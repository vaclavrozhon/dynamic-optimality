import MultiSplay.EndpointEncoding
import Mathlib.Data.List.Nodup

/-!
# The actual bottom-up switch order

The search path is its Boolean reference address. `ancestorEmissions` lists
exactly the ancestors whose preferred side disagrees with that path, from the
root down. `actualEmissions` reverses these ancestors and appends the mandatory
switch at the requested node. Its key set and count agree with `nodeSwitches`.
This records the standard order, rather than silently replacing it by sorted
depths when subsequently analyzing the secondary ledger.
-/

namespace MultiSplay.EndpointEncoding

open ChaCha.Primary (Key branch owners mem_owners)

def below (state : State) (edge : Bool) : State := fun owner => state (edge :: owner)

def ancestorEmissions (state : State) : Key → List Key
  | [] => []
  | edge :: rest =>
      (if state [] = edge then [] else [[]]) ++
        (ancestorEmissions (below state edge) rest).map (edge :: ·)

def ascendingEmissions (state : State) (address : Key) : List Key :=
  ancestorEmissions state address ++ [address]

def actualEmissions (state : State) (address : Key) : List Key :=
  (ancestorEmissions state address).reverse ++ [address]

theorem ascendingEmissions_cons (state : State) (edge : Bool) (rest : Key) :
    ascendingEmissions state (edge :: rest) =
      (if state [] = edge then [] else [[]]) ++
        (ascendingEmissions (below state edge) rest).map (edge :: ·) := by
  simp [ascendingEmissions, ancestorEmissions, List.map_append, List.append_assoc]

theorem actualEmissions_perm (state : State) (address : Key) :
    (actualEmissions state address).Perm (ascendingEmissions state address) :=
  (List.reverse_perm _).append_right _

theorem ascendingEmissions_nodup (state : State) (address : Key) :
    (ascendingEmissions state address).Nodup := by
  induction address generalizing state with
  | nil => simp [ascendingEmissions, ancestorEmissions]
  | cons edge rest ih =>
      rw [ascendingEmissions_cons]
      have tail := (ih (below state edge)).map (f := (edge :: ·)) (fun _ _ same => List.cons.inj same |>.2)
      by_cases same : state [] = edge
      · simpa [same] using tail
      · simpa [same] using tail

theorem ascendingEmissions_mem {state : State} {address owner : Key} :
    owner ∈ ascendingEmissions state address ↔ changes (state owner) (nodeWrite state address owner) := by
  induction address generalizing state owner with
  | nil =>
      cases owner with
      | nil =>
          cases h : state [] <;> simp [ascendingEmissions, ancestorEmissions, changes, nodeWrite, h]
      | cons edge rest =>
          simp [ascendingEmissions, ancestorEmissions, changes, nodeWrite, branch]
  | cons edge rest ih =>
      rw [ascendingEmissions_cons]
      cases owner with
      | nil =>
          cases state [] <;> cases edge <;>
            simp [changes, nodeWrite, branch]
      | cons other owner =>
          by_cases same : other = edge
          · subst other
            simp only [List.mem_append, List.mem_map]
            have absent : (edge :: owner) ∉ (if state [] = edge then [] else [[]]) := by
              split <;> simp
            simp only [absent, false_or, List.cons.injEq, true_and, exists_eq_right]
            rw [ih]
            simp [below, nodeWrite, branch, List.cons_prefix_cons]
          · have absent : (other :: owner) ∉ (if state [] = edge then [] else [[]]) := by
              split <;> simp
            simp [absent, same, Ne.symm same, changes, nodeWrite, branch, List.cons_prefix_cons]

theorem ascendingEmissions_prefix {state : State} {address owner : Key}
    (member : owner ∈ ascendingEmissions state address) : owner.IsPrefix address := by
  induction address generalizing state owner with
  | nil => simpa [ascendingEmissions, ancestorEmissions] using member
  | cons edge rest ih =>
      rw [ascendingEmissions_cons] at member
      simp only [List.mem_append, List.mem_map] at member
      rcases member with here | ⟨child, inChild, rfl⟩
      · have empty : owner = [] := by
          split at here
          · simp at here
          · simpa using here
        subst owner
        exact List.nil_prefix
      · exact List.cons_prefix_cons.mpr ⟨rfl, ih inChild⟩

theorem ascendingEmissions_toFinset {height : Nat} (state : State) (address : Key)
    (inside : address.length < height) :
    (ascendingEmissions state address).toFinset = nodeSwitches height state address := by
  ext owner
  simp only [List.mem_toFinset, nodeSwitches, Finset.mem_filter, mem_owners]
  constructor
  · intro member
    have shorter := (ascendingEmissions_prefix member).length_le
    exact ⟨by omega, ascendingEmissions_mem.mp member⟩
  · intro member
    exact ascendingEmissions_mem.mpr member.2

theorem actualEmissions_count {height : Nat} (state : State) (address : Key)
    (inside : address.length < height) :
    (actualEmissions state address).length = (nodeSwitches height state address).card := by
  rw [(actualEmissions_perm state address).length_eq,
    ← ascendingEmissions_toFinset state address inside,
    List.toFinset_card_of_nodup (ascendingEmissions_nodup state address)]

theorem actualEmissions_nodup (state : State) (address : Key) :
    (actualEmissions state address).Nodup :=
  (actualEmissions_perm state address).nodup_iff.mpr (ascendingEmissions_nodup state address)

def toggle (state : State) (owner : Key) : State := fun node =>
  if node = owner then !state node else state node

def applySwitches (state : State) : List Key → State
  | [] => state
  | owner :: rest => applySwitches (toggle state owner) rest

theorem applySwitches_lookup (state : State) {switches : List Key}
    (distinct : switches.Nodup) (owner : Key) :
    applySwitches state switches owner = if owner ∈ switches then !state owner else state owner := by
  induction switches generalizing state with
  | nil => simp [applySwitches]
  | cons first rest ih =>
      rw [List.nodup_cons] at distinct
      rw [applySwitches, ih _ distinct.2]
      by_cases same : owner = first
      · subst owner
        simp [toggle, distinct.1]
      · simp [toggle, same]

/-- Executing the ancestor switches bottom-up and then the final toggle gives
exactly the state used to generate the next endpoint request. -/
theorem actualEmissions_state (state : State) (address : Key) :
    applySwitches state (actualEmissions state address) = nodeStep state address := by
  funext owner
  rw [applySwitches_lookup state (actualEmissions_nodup state address)]
  have member : owner ∈ actualEmissions state address ↔
      changes (state owner) (nodeWrite state address owner) :=
    (actualEmissions_perm state address).mem_iff.trans ascendingEmissions_mem
  simp only [member]
  cases write : nodeWrite state address owner with
  | none => simp [nodeStep, changes, write]
  | some side =>
      cases side <;> cases h : state owner <;> simp [nodeStep, changes, write, h]

/-- This is the complete chronological owner list for the preference protocol;
each original request has exactly its own final emission. -/
def actualHistory (state : State) : List Key → List Key
  | [] => []
  | address :: rest => actualEmissions state address ++ actualHistory (nodeStep state address) rest

theorem actualHistory_length {height : Nat} (state : State) (addresses : List Key)
    (inside : ∀ address ∈ addresses, address.length < height) :
    (actualHistory state addresses).length = nodeCost height state addresses := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address rest ih =>
      simp only [actualHistory, List.length_append, nodeCost]
      rw [actualEmissions_count state address (inside address (by simp)),
        ih _ (fun address member => inside address (List.mem_cons_of_mem _ member))]

end MultiSplay.EndpointEncoding
