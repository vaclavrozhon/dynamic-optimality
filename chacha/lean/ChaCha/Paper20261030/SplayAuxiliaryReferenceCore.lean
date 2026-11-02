import ChaCha.Paper20261030.SplayAuxiliarySecondary
import ChaCha.Paper20261030.PathPorts

/-!
# Shared raw references underlying the source decomposition

Reference records may contain ghost preferences and cached annotations.
The physical splay identities are only their mapped separator keys. These
definitions expose the same reference and preferred-hole table as the
existing arbitrary-shape `Global.Preferred` invariant.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage
open MultiSplay EndpointEncoding ClassicalSwitch Global.Preferred

variable {α ρ κ : Type*}

def referenceCuts (key : ρ → κ) : Source α ρ → RawTree κ
  | .leaf _ _ => .empty
  | .fork record left right => .node (referenceCuts key left) (key record) (referenceCuts key right)

def referenceState (right : ρ → Bool) : Source α ρ → State
  | .leaf _ _,_ => false
  | .fork record _ _,[] => right record
  | .fork _ left _,false::rest => referenceState right left rest
  | .fork _ _ rightChild,true::rest => referenceState right rightChild rest

@[simp] theorem referenceState_left (right : ρ → Bool) (record : ρ) (l r : Source α ρ) :
    below (referenceState right (.fork record l r)) false = referenceState right l := rfl

@[simp] theorem referenceState_right (right : ρ → Bool) (record : ρ) (l r : Source α ρ) :
    below (referenceState right (.fork record l r)) true = referenceState right r := rfl

theorem preferred_referenceCuts (key : ρ → κ) (right : ρ → Bool) (reference : Source α ρ) :
    preferred (referenceState right reference) (referenceCuts key reference) =
      Auxiliary.map key (PathPorts.skeleton right reference) := by
  induction reference with
  | leaf label record => rfl
  | fork record l r ihl ihr =>
      cases direction : right record <;>
        simp [preferred,referenceCuts,referenceState,direction,PathPorts.skeleton,
          Auxiliary.map,← ihl,← ihr,below]

def referenceEntries (right : ρ → Bool) : Source α ρ → List (ChaCha.Primary.Key × Source α ρ)
  | .leaf label record => [([],.leaf label record)]
  | .fork record l r =>
      if right record then
        ([false],l)::((referenceEntries right r).map (fun e => (true::e.1,e.2)))
      else
        ((referenceEntries right l).map (fun e => (false::e.1,e.2)))++[([true],r)]

theorem referenceEntries_raw (key : ρ → κ) (right : ρ → Bool) (reference : Source α ρ) :
    (referenceEntries right reference).map (fun e => (e.1,referenceCuts key e.2)) =
      preferredHoles (referenceState right reference) (referenceCuts key reference) := by
  induction reference with
  | leaf label record => rfl
  | fork record l r ihl ihr =>
      cases direction : right record <;>
        simp [referenceEntries,preferredHoles,referenceCuts,referenceState,direction,
          prefixHoles,List.map_map,Function.comp_def,below,← ihl,← ihr]

theorem referenceEntries_state (right : ρ → Bool) (reference : Source α ρ)
    {entry : ChaCha.Primary.Key × Source α ρ} (member : entry ∈ referenceEntries right reference) :
    referenceState right entry.2 = restrict (referenceState right reference) entry.1 := by
  induction reference generalizing entry with
  | leaf label record =>
      simp only [referenceEntries,List.mem_singleton] at member
      subst entry
      rfl
  | fork record l r ihl ihr =>
      cases direction : right record with
      | false =>
          simp only [referenceEntries,direction,Bool.false_eq_true,↓reduceIte,
            List.mem_append,List.mem_singleton] at member
          rcases member with child | rfl
          · obtain ⟨e,present,rfl⟩ := List.mem_map.mp child
            simpa only [restrict,referenceState_left] using ihl present
          · rfl
      | true =>
          simp only [referenceEntries,direction,↓reduceIte,List.mem_cons] at member
          rcases member with rfl | child
          · rfl
          · obtain ⟨e,present,rfl⟩ := List.mem_map.mp child
            simpa only [restrict,referenceState_right] using ihr present

theorem referenceEntries_smaller (key : ρ → κ) (right : ρ → Bool)
    (record : ρ) (l r : Source α ρ)
    {entry : ChaCha.Primary.Key × Source α ρ}
    (member : entry ∈ referenceEntries right (.fork record l r)) :
    (referenceCuts key entry.2).size < (referenceCuts key (.fork record l r)).size := by
  have included : (entry.1,referenceCuts key entry.2) ∈
      preferredHoles (referenceState right (.fork record l r)) (referenceCuts key (.fork record l r)) := by
    rw [← referenceEntries_raw]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  exact preferredHoles_size_lt _ (by simp [referenceCuts]) included

end ChaCha.Paper20261030.SplayAuxiliary
