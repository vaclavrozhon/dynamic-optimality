import MultiSplay.Obstructions.ClassicalBalancedFamily
import MultiSplay.ClassicalSwitchPartition
import MultiSplay.ClassicalSwitchEventWord
import MultiSplay.SecondaryEmissionWords

/-! Exact primary switches and owner-indexed secondary writes for the cold
maximum access. A leaf toggle changes no preferred-path component. The
secondary identity holds for every ordered depth tree, not just midpoint. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open ChaCha (DepthTree DepthSplit changesFrom edgeChange)
open ChaCha.MTR.Tree
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

local instance (split : DepthSplit) (a b : Nat) : Decidable (split.Separates a b) :=
  inferInstanceAs (Decidable (split.lo ≤ a ∧ a ≤ split.cut ∧ split.cut < b ∧ b ≤ split.hi))

def allRight : State := fun _ => true

@[simp] theorem allRight_below (edge : Bool) : below allRight edge = allRight := rfl

 theorem right_ancestors (depth : Nat) :
    ancestorEmissions allRight (List.replicate depth true) = [] := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [List.replicate_succ,ancestorEmissions,allRight_below,allRight,ih]

 theorem right_emissions (depth : Nat) :
    actualEmissions allRight (List.replicate depth true) = [List.replicate depth true] := by
  simp [actualEmissions,right_ancestors]

 theorem perfect_maximum (depth key : Nat) :
    referenceAt (perfect (depth+1) key) (List.replicate depth true) = .node .empty key .empty := by
  induction depth with
  | zero => simp [perfect,referenceAt]
  | succ depth ih => simpa only [List.replicate_succ,perfect,referenceAt,if_true] using ih

/-- The preference bit stored at a real reference leaf has no effect on
any preferred component, including the retained empty component slots. -/
 theorem leaf_toggle_partition {α : Type*} (state : State) (reference : RawTree α)
    (address : Key) (key : α)
    (leaf : referenceAt reference address = .node .empty key .empty) :
    preferred (toggle state address) reference = preferred state reference ∧
    otherComponents (toggle state address) reference = otherComponents state reference := by
  induction address generalizing state reference with
  | nil =>
    simp only [referenceAt] at leaf
    subst reference
    cases side : state [] <;> simp [preferred,otherComponents,toggle,side]
  | cons edge rest ih =>
    cases reference with
    | empty => simp [referenceAt,referenceAt_empty] at leaf
    | node left root right =>
      have unchanged : toggle state (edge::rest) [] = state [] := by simp [toggle]
      cases edge with
      | false =>
        have child := ih (below state false) left (by simpa only [referenceAt,Bool.false_eq_true,if_false] using leaf)
        have other := below_toggle_other state false true rest (by decide)
        cases side : state [] <;>
          simp only [preferred,otherComponents,unchanged,side,Bool.false_eq_true,if_false,if_true,
            below_toggle_cons,other,child.1,child.2,true_and]
      | true =>
        have child := ih (below state true) right (by simpa only [referenceAt,if_true] using leaf)
        have other := below_toggle_other state true false rest (by decide)
        cases side : state [] <;>
          simp only [preferred,otherComponents,unchanged,side,Bool.false_eq_true,if_false,if_true,
            below_toggle_cons,other,child.1,child.2,true_and]

 theorem leaf_toggle_forest {α : Type*} (state : State) (reference : RawTree α)
    (address : Key) (key : α)
    (leaf : referenceAt reference address = .node .empty key .empty) :
    forest (toggle state address) reference = forest state reference := by
  obtain ⟨preferredEq,othersEq⟩ := leaf_toggle_partition state reference address key leaf
  simp only [forest,preferredEq,othersEq]

private theorem penultimate_row (depth : Nat) (split : DepthSplit)
    (bounds : split.lo ≤ split.cut ∧ split.cut < split.hi ∧ split.hi ≤ depth+1)
    (owner : Key) :
    changesFrom true (Secondary.actualRow ⟨split,owner⟩ allRight [List.replicate depth true]) =
      if owner = (List.replicate depth true).take split.lo ∧ split.Separates depth (depth+1)
        then 1 else 0 := by
  simp only [Secondary.actualRow,right_emissions,List.filterMap_cons,List.filterMap_nil,List.append_nil,
    Secondary.project,List.length_replicate]
  unfold DepthSplit.Separates
  split_ifs <;> simp_all [changesFrom,edgeChange] <;> omega

/-- A single mandatory maximum-node switch emits the penultimate depth
label. From all-right persistent memory it changes exactly one owner row.
This uses the literal `actualLedger`, including its owner addresses. -/
 theorem penultimate_secondary_ledger (depth : Nat) (reference : DepthTree 0 (depth+1)) :
    Secondary.actualLedger reference (fun _ => true) allRight [List.replicate depth true] = 1 := by
  obtain ⟨split,⟨member,separates⟩,unique⟩ := reference.unique_separating (Nat.zero_le depth)
    (Nat.lt_succ_self depth) le_rfl
  let owner := (List.replicate depth true).take split.lo
  let row : Secondary.Row := ⟨split,owner⟩
  have present : row ∈ Secondary.rows reference := by
    simp only [Secondary.rows,Finset.mem_sigma,ChaCha.Primary.mem_level]
    refine ⟨member,?_⟩
    change owner.length = split.lo
    simp only [owner,List.length_take,List.length_replicate]
    exact Nat.min_eq_left separates.1
  have selected : changesFrom true (Secondary.actualRow row allRight [List.replicate depth true]) = 1 := by
    rw [penultimate_row depth split (reference.node_bounds member).2 owner]
    simp only [owner,separates,and_self,if_true]
  unfold Secondary.actualLedger
  rw [Finset.sum_eq_single row]
  · exact selected
  · intro other inRows different
    obtain ⟨otherSplit,otherOwner⟩ := other
    have otherPresent := (Finset.mem_sigma.mp inRows).1
    rw [penultimate_row depth otherSplit (reference.node_bounds otherPresent).2 otherOwner]
    apply if_neg
    rintro ⟨ownerEq,separator⟩
    have equal := unique otherSplit ⟨otherPresent,separator⟩
    subst otherSplit
    apply different
    simp only [row,ownerEq,owner]
  · exact fun absent => False.elim (absent present)

 theorem maximum_counters (depth key : Nat) (reference : DepthTree 0 (depth+1)) :
    ancestorEmissions allRight (List.replicate depth true) = [] ∧
    actualEmissions allRight (List.replicate depth true) = [List.replicate depth true] ∧
    forest (nodeStep allRight (List.replicate depth true)) (perfect (depth+1) key) =
      forest allRight (perfect (depth+1) key) ∧
    Secondary.actualLedger reference (fun _ => true) allRight [List.replicate depth true] = 1 := by
  have final : beforeFinal allRight (List.replicate depth true) = allRight := by
    simp [beforeFinal,right_ancestors,applySwitches]
  have endpoint := final_toggle allRight (List.replicate depth true)
  rw [final] at endpoint
  exact ⟨right_ancestors depth,right_emissions depth,
    endpoint ▸ leaf_toggle_forest allRight _ _ key (perfect_maximum depth key),
    penultimate_secondary_ledger depth reference⟩

end MultiSplay.Obstructions.Classical
