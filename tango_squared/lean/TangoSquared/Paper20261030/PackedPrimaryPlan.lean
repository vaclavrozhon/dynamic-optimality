import TangoSquared.Paper20261030.PrimaryPhysicalExpansion
import TangoSquared.Paper20261030.SourceRelabel
import TangoSquared.Paper20261030.PackedRearrangements
import TangoSquared.Paper20261030.VirtualStorage
import TangoSquared.Paper20261030.DepthPorts

/-!
# Actual packed depth trees provide the primary physical plans

Real depth ports are colored by their actual primary exit side. Completion
and sentinel are virtual. Pack the three colors, relabel retained real
ports by their exits, and mirror the right routing skeleton before any
payload is attached. The two plan words are exactly the required ordered
exit lists. Real routing vertices hold at most three source records; at
most two virtual leaves give a header of at most twelve source records.
-/

namespace TangoSquared.Paper20261030.PackedPrimary

open PreferredProjection RouterProjection ColoredStorage PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

local instance depthPortColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def color (start : Nat) (t : PrefRouter α) (d : Nat) : Option Bool :=
  (portAt start (exits t) d).map Exit.leftOfEndpoint

def label (start : Nat) (t : PrefRouter α) (d : Nat) : Exit α :=
  (portAt start (exits t) d).getD ⟨false,t⟩

def wing (start : Nat) (t : PrefRouter α) (side : Bool) (source : Source Nat ρ) : RoutingWing α ρ :=
  (packed (color start t) (some side) source).map (Source.relabel (label start t))

def plan (start : Nat) (t : PrefRouter α) (source : Source Nat ρ) : Plan α ρ :=
  ⟨wing start t true source,(wing start t false source).map Source.mirror⟩

def header (start : Nat) (t : PrefRouter α) (source : Source Nat ρ) : List ρ :=
  headerRecords (color start t) source

def optionalLeaves {κ η : Type*} : Option (Source κ η) → List κ
  | none => []
  | some t => t.shape.leaves

theorem routingWord_eq (t : RoutingWing α ρ) : routingWord t = optionalLeaves t := by
  cases t <;> rfl

theorem packed_leaves (colors : Nat → Option Bool) (q : Option Bool) (source : Source Nat ρ) :
    optionalLeaves (packed colors q source) = source.shape.leaves.filter (fun d => decide (colors d = q)) := by
  cases hp : packed colors q source with
  | none =>
    have empty := packed_none_shape colors q source hp
    have words := congrArg Router.leaves empty
    change [] = source.shape.leaves.filter _
    change (source.shape.prune (fun d => decide (colors d = q))).leaves = [] at words
    exact (Router.leaves_prune _ _).symm.trans words |>.symm
  | some t =>
    rw [optionalLeaves,packed_shape colors q source hp,Router.leaves_prune]
    rfl

theorem optionalLeaves_relabel {κ τ η : Type*} (f : κ → τ) (t : Option (Source κ η)) :
    optionalLeaves (t.map (Source.relabel f)) = (optionalLeaves t).map f := by
  cases t with
  | none => rfl
  | some t => exact Source.relabel_leaves f t

theorem optionalLeaves_mirror {κ η : Type*} (t : Option (Source κ η)) :
    optionalLeaves (t.map Source.mirror) = (optionalLeaves t).reverse := by
  cases t with
  | none => rfl
  | some t => exact Source.mirror_leaves t

theorem selected_word (ports : Nat → Option (Exit α)) (fallback : Exit α)
    (word : List Nat) (side : Bool) :
    ((word.filter (fun d => decide ((ports d).map Exit.leftOfEndpoint = some side))).map
      (fun d => (ports d).getD fallback)) =
      (word.filterMap ports).filter (fun e => decide (e.leftOfEndpoint = side)) := by
  induction word with
  | nil => rfl
  | cons d ds ih =>
    cases port : ports d with
    | none => simpa only [List.filter_cons,port,Option.map_none,reduceCtorEq,
        decide_false,Bool.false_eq_true,if_false,List.filterMap_cons] using ih
    | some e =>
      by_cases bit : e.leftOfEndpoint = side
      · simpa [port,bit] using congrArg (List.cons e) ih
      · simpa [port,bit] using ih

theorem wing_word (start : Nat) (t : PrefRouter α) (side : Bool) (source : Source Nat ρ) :
    routingWord (wing start t side source) =
      (source.shape.leaves.filterMap (portAt start (exits t))).filter (fun e => decide (e.leftOfEndpoint = side)) := by
  rw [routingWord_eq]
  unfold wing
  rw [optionalLeaves_relabel,packed_leaves]
  exact selected_word (portAt start (exits t)) ⟨false,t⟩ source.shape.leaves side

theorem plan_words (start : Nat) (t : PrefRouter α) (source : Source Nat ρ)
    (ports : source.shape.leaves.filterMap (portAt start (exits t)) = exits t) :
    routingWord (plan start t source).left = (exits t).filter (·.leftOfEndpoint) ∧
      routingWord (plan start t source).right = ((exits t).filter (fun e => !e.leftOfEndpoint)).reverse := by
  constructor
  · rw [plan,wing_word,ports]
    apply List.filter_congr
    intro e he
    cases e.leftOfEndpoint <;> rfl
  · rw [routingWord_eq]
    change optionalLeaves ((wing start t false source).map Source.mirror) = _
    rw [optionalLeaves_mirror]
    rw [← routingWord_eq]
    rw [wing_word,ports]
    congr 1
    apply List.filter_congr
    intro e he
    cases e.leftOfEndpoint <;> rfl

theorem packed_capacity (colors : Nat → Option Bool) (q : Option Bool) (source : Source Nat ρ)
    {actual : Source Nat (List ρ)} (present : packed colors q source = some actual) : actual.Bounded 3 := by
  have full : Paper20261030.Router.Full (pack colors q source).shape := by
    rw [pack_shape]
    exact Paper20261030.Router.full_prune _ _
  have same := (pack colors q source).toSource_roundtrip full
  change storedOption (packed colors q source) = pack colors q source at same
  rw [present] at same
  change actual.toStored = pack colors q source at same
  change actual.toStored.Bounded 3
  rw [same]
  simpa using pack_bounded_colors colors q source

theorem wing_bounded (start : Nat) (t : PrefRouter α) (side : Bool) (source : Source Nat ρ) :
    RoutingBounded 3 (wing start t side source) := by
  unfold wing
  cases present : packed (color start t) (some side) source with
  | none => trivial
  | some actual => exact (packed_capacity _ _ _ present).relabel (label start t)

theorem plan_bounded (start : Nat) (t : PrefRouter α) (source : Source Nat ρ) :
    RoutingBounded 3 (plan start t source).left ∧ RoutingBounded 3 (plan start t source).right := by
  refine ⟨wing_bounded start t true source,?_⟩
  change RoutingBounded 3 ((wing start t false source).map Source.mirror)
  have bound := wing_bounded start t false source
  cases h : wing start t false source with
  | none => trivial
  | some actual =>
    rw [h] at bound
    exact Source.Bounded.mirror bound

theorem none_count {κ η : Type*} (f : κ → Option η) (word : List κ) :
    (word.filter (fun x => (f x).isNone)).length + (word.filterMap f).length = word.length := by
  induction word with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h] <;> omega

theorem virtual_bound (start : Nat) (t : PrefRouter α) (source : Source Nat ρ)
    (ports : source.shape.leaves.filterMap (portAt start (exits t)) = exits t)
    (size : source.shape.leaves.length ≤ (exits t).length + 2) :
    virtualCount (color start t) source ≤ 2 := by
  have count := none_count (portAt start (exits t)) source.shape.leaves
  rw [ports] at count
  have predicate : (fun d => (color start t d).isNone) = (fun d => (portAt start (exits t) d).isNone) := by
    funext d
    simp only [color]
    cases portAt start (exits t) d <;> rfl
  unfold virtualCount
  rw [predicate]
  omega

theorem header_bound (start : Nat) (t : PrefRouter α) (source : Source Nat ρ)
    (ports : source.shape.leaves.filterMap (portAt start (exits t)) = exits t)
    (size : source.shape.leaves.length ≤ (exits t).length + 2) : (header start t source).length ≤ 12 := by
  have bound := header_size (color start t) source
  have virtual := virtual_bound start t source ports size
  simp only [Fintype.card_bool] at bound
  exact bound.trans (by omega)

end TangoSquared.Paper20261030.PackedPrimary
