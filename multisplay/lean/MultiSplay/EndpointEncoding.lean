import ChaCha.Primary
import Mathlib.Data.Finset.Card

/-!
# Encoding the mandatory final switch as a leaf access

An original reference node is its Boolean root-to-node address. Its preferred
direction is one bit. A node access writes the search direction at each proper
ancestor and toggles the bit at the requested node, including a reference leaf.
The latter bit is analytical when that leaf has no physical children.

`core` doubles every address bit. `copy` adds the unequal pair `side, !side`
and pads with right edges to the common height `2*height`. The unequal pair
prevents the request from entering any deeper original core node.
`step_aligned` and `run_cost_le` connect these operations to the existing Tango
primary-reference `branch`, with the final switch included.
-/

namespace MultiSplay.EndpointEncoding

open ChaCha.Primary (Key branch owners mem_owners)

abbrev State := Key → Bool

def core : Key → Key
  | [] => []
  | b :: rest => b :: b :: core rest

@[simp] theorem core_length (address : Key) : (core address).length = 2 * address.length := by
  induction address <;> simp_all [core] <;> omega

theorem core_injective : Function.Injective core := by
  intro a b same
  induction a generalizing b with
  | nil => cases b <;> simp_all [core]
  | cons x xs ih =>
      cases b with
      | nil => simp [core] at same
      | cons y ys =>
          simp only [core, List.cons.injEq] at same
          exact congrArg₂ List.cons same.1 (ih same.2.2)

def copy (height : Nat) (address : Key) (side : Bool) : Key :=
  core address ++ [side, !side] ++ List.replicate (2 * (height - address.length - 1)) true

theorem copy_length {height : Nat} {address : Key} (inside : address.length < height) (side : Bool) :
    (copy height address side).length = 2 * height := by
  simp only [copy, List.length_append, core_length, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

private theorem branch_cons (a b : Bool) (u x : Key) :
    branch (a :: u) (b :: x) = if a = b then branch u x else none := by
  by_cases same : a = b
  · subst b
    simp [branch, List.cons_prefix_cons]
  · simp [branch, List.cons_prefix_cons, same]

/-- Even-depth core pivots see exactly the original proper-ancestor branch,
or the selected copy side at the requested node itself. -/
theorem branch_core (owner address : Key) (side : Bool) (padding : Key) :
    branch (core owner) (core address ++ side :: (!side) :: padding) =
      if owner = address then some side else branch owner address := by
  induction owner generalizing address with
  | nil =>
      cases address <;> simp [core, branch]
  | cons a owner ih =>
      cases address with
      | nil =>
          cases a <;> cases side <;> simp [core, branch, List.cons_prefix_cons]
      | cons b address =>
          simp only [core, List.cons_append, branch_cons]
          by_cases same : a = b
          · subst b
            simpa only [ite_true, List.cons.injEq, true_and] using ih address
          · simp [same]

/-- The standard final switch writes the direction opposite to the current
one. Proper ancestors receive the direction toward the requested node. -/
def nodeWrite (state : State) (address owner : Key) : Option Bool :=
  if owner = address then some (!state owner) else branch owner address

def nodeStep (state : State) (address : Key) : State := fun owner =>
  (nodeWrite state address owner).getD (state owner)

def leafStep (state : State) (leaf : Key) : State := fun owner =>
  (branch owner leaf).getD (state owner)

def request (height : Nat) (state : State) (address : Key) : Key :=
  copy height address (!state address)

def Matches (nodeState leafState : State) : Prop :=
  ∀ owner, leafState (core owner) = nodeState owner

theorem writes_match (height : Nat) (state : State) (address owner : Key) :
    branch (core owner) (request height state address) = nodeWrite state address owner := by
  unfold request copy
  rw [List.append_assoc]
  have h := branch_core owner address (!state address)
    (List.replicate (2 * (height - address.length - 1)) true)
  by_cases same : owner = address
  · subst owner
    simpa [nodeWrite] using h
  · simpa [nodeWrite, same] using h

theorem step_aligned {nodeState leafState : State} (aligned : Matches nodeState leafState)
    (height : Nat) (address : Key) :
    Matches (nodeStep nodeState address) (leafStep leafState (request height nodeState address)) := by
  intro owner
  simp only [leafStep, nodeStep, writes_match, aligned owner]

def changes (before : Bool) (write : Option Bool) : Bool :=
  match write with
  | none => false
  | some after => decide (before ≠ after)

def nodeSwitches (height : Nat) (state : State) (address : Key) : Finset Key :=
  (owners height).filter (fun owner => changes (state owner) (nodeWrite state address owner))

def leafSwitches (height : Nat) (state : State) (leaf : Key) : Finset Key :=
  (owners height).filter (fun owner => changes (state owner) (branch owner leaf))

/-- A requested reference leaf still contributes its mandatory final toggle. -/
theorem final_mem_switches {height : Nat} (state : State) {address : Key}
    (inside : address.length < height) : address ∈ nodeSwitches height state address := by
  simp only [nodeSwitches, Finset.mem_filter, mem_owners]
  refine ⟨inside, ?_⟩
  cases h : state address <;> simp [changes, nodeWrite, h]

theorem switches_embed {nodeState leafState : State} (aligned : Matches nodeState leafState)
    (height : Nat) (address : Key) :
    (nodeSwitches height nodeState address).image core ⊆
      leafSwitches (2 * height) leafState (request height nodeState address) := by
  intro owner member
  obtain ⟨original, active, rfl⟩ := Finset.mem_image.mp member
  simp only [nodeSwitches, Finset.mem_filter, mem_owners] at active
  simp only [leafSwitches, Finset.mem_filter, mem_owners, core_length, writes_match, aligned original]
  exact ⟨by omega, active.2⟩

theorem switch_count_le {nodeState leafState : State} (aligned : Matches nodeState leafState)
    (height : Nat) (address : Key) :
    (nodeSwitches height nodeState address).card ≤
      (leafSwitches (2 * height) leafState (request height nodeState address)).card := by
  have bound := Finset.card_le_card (switches_embed aligned height address)
  rwa [Finset.card_image_of_injective _ core_injective] at bound

def encode (height : Nat) (state : State) : List Key → List Key
  | [] => []
  | address :: rest => request height state address :: encode height (nodeStep state address) rest

def nodeCost (height : Nat) (state : State) : List Key → Nat
  | [] => 0
  | address :: rest =>
      (nodeSwitches height state address).card + nodeCost height (nodeStep state address) rest

def leafCost (height : Nat) (state : State) : List Key → Nat
  | [] => 0
  | leaf :: rest =>
      (leafSwitches height state leaf).card + leafCost height (leafStep state leaf) rest

theorem encode_length (height : Nat) (state : State) (addresses : List Key) :
    (encode height state addresses).length = addresses.length := by
  induction addresses generalizing state <;> simp_all [encode]

theorem encode_on_leaves {height : Nat} (state : State) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height) :
    ∀ leaf ∈ encode height state addresses, leaf.length = 2 * height := by
  induction addresses generalizing state with
  | nil => simp [encode]
  | cons address rest ih =>
      intro leaf member
      simp only [encode, List.mem_cons] at member
      rcases member with rfl | later
      · exact copy_length (inside address (by simp)) _
      · exact ih _ (fun address member => inside address (List.mem_cons_of_mem _ member)) _ later

/-- The initialized node-switch count, including every final switch, is
bounded by initialized primary flips of the actual encoded leaf history. -/
theorem run_cost_le {nodeState leafState : State} (aligned : Matches nodeState leafState)
    (height : Nat) (addresses : List Key) :
    nodeCost height nodeState addresses ≤
      leafCost (2 * height) leafState (encode height nodeState addresses) := by
  induction addresses generalizing nodeState leafState with
  | nil => exact le_rfl
  | cons address rest ih =>
      have first := switch_count_le aligned height address
      have remaining := ih (step_aligned aligned height address)
      simpa only [nodeCost, leafCost, encode] using Nat.add_le_add first remaining

end MultiSplay.EndpointEncoding
