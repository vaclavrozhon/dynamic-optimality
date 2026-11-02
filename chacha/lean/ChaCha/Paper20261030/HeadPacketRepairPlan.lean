import ChaCha.Paper20261030.MixedPacketRepairAgreement

set_option autoImplicit false

/-!
# The physical-field repair blueprint computed from observed masks

Left real wings use the original child order and right wings use its
reverse. Primary joins reset the component parent, and nested attachments
add one real leaf layer and its delimiter. Logical prefix merging does
not change this blueprint. Only raw header lengths are needed from the
bounded header values.
-/

namespace ChaCha.Paper20261030.HeadPacketRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers MixedPacketRepair

variable {κ α β ρ ι η : Type*}

abbrev Layout (κ : Type*) := Option (Source κ Layers)

def realJoin (reverse : Bool) : Layout κ → Layout κ → Layout κ
  | none,right => right
  | left,none => left
  | some left,some right => some (.fork (.fork reverse) left right)

def primaryJoin : Layout κ → Layout κ → Layout κ
  | none,right => right
  | left,none => left
  | some left,some right => some (.fork .base left right)

def block (bits : κ → Bool) (key : κ) : Layout κ := if bits key then some (.leaf key .prefix) else none

def bottom (key : κ) (count : Nat) : Layout κ := some (.leaf key (.raw count .base))

def attachment (child : Layout κ) : Layout κ := child.map (fun source => source.setRoot (.leaf (.raw 1 source.rootRecord)))

theorem logical_match (plan : Layout κ) (layout : HeadPacketLayout.Layout κ α ρ ι)
    (same : LayoutMatches plan layout) (records : List ρ) :
    LayoutMatches plan (HeadPacketLayout.push (HeadPacketLayout.addLogical records) layout) := by
  cases plan <;> cases layout <;> try exact False.elim same
  · trivial
  · exact same.logical records

theorem realJoin_match (reverse : Bool) (markerId : ι) (records : List ρ)
    (leftPlan rightPlan : Layout κ) (left right : HeadPacketLayout.Layout κ α ρ ι)
    (hl : LayoutMatches leftPlan left) (hr : LayoutMatches rightPlan right) :
    LayoutMatches (realJoin reverse leftPlan rightPlan) (HeadPacketLayout.realJoin markerId records left right) := by
  cases leftPlan <;> cases left <;> try exact False.elim hl
  all_goals cases rightPlan <;> cases right <;> try exact False.elim hr
  · trivial
  · exact logical_match _ _ hr records
  · exact logical_match _ _ hl records
  · exact .fork _ _ _ _ _ _ (.fork reverse markerId records placeholder) hl hr

theorem primaryJoin_match (leftPlan rightPlan : Layout κ) (left right : HeadPacketLayout.Layout κ α ρ ι)
    (hl : LayoutMatches leftPlan left) (hr : LayoutMatches rightPlan right) :
    LayoutMatches (primaryJoin leftPlan rightPlan) (HeadPacketLayout.primaryJoin left right) := by
  cases leftPlan <;> cases left <;> try exact False.elim hl
  all_goals cases rightPlan <;> cases right <;> try exact False.elim hr
  · trivial
  · exact hr
  · exact hl
  · exact .fork _ _ _ _ _ _ .base hl hr

theorem block_match (bits : κ → Bool) (key : κ) :
    LayoutMatches (block bits key) (HeadPacketLayout.block (α := α) (ρ := ρ) (ι := ι) bits key) := by
  cases present : bits key <;> simp only [block,HeadPacketLayout.block,present,Bool.false_eq_true,if_false,if_true]
  · trivial
  · exact .leaf key _ _ (.prefix [])

theorem bottom_match (key : κ) (header : Packet α ρ ι) :
    LayoutMatches (bottom key header.length) (HeadPacketLayout.bottom key header) :=
  .leaf key _ _ (.raw header .base .base .base)

theorem attachment_match (markerId : ι) (record : ρ) (plan : Layout κ) (layout : HeadPacketLayout.Layout κ α ρ ι)
    (same : LayoutMatches plan layout) :
    LayoutMatches (attachment plan) (HeadPacketLayout.attachment markerId record layout) := by
  cases plan <;> cases layout <;> try exact False.elim same
  · trivial
  · exact same.setRoot _ _ (.leaf markerId [record] placeholder _ _ (.raw [none] _ _ same.root))

def dormant (bits : Fin 8 → Bool) (l b r : Fin 8) (headerLength : Nat) : Layout (Fin 8) :=
  primaryJoin (primaryJoin (block bits l) (bottom b headerLength)) (block bits r)

def active (bits : Fin 8 → Bool) (l r tl b tr : Fin 8) (child : Layout (Fin 8)) (direction : Bool) (headerLength : Nat) : Layout (Fin 8) :=
  let attached := attachment child
  let left := if direction then realJoin false attached (block bits tl) else block bits tl
  let right := if direction then block bits tr else realJoin true (block bits tr) attached
  primaryJoin (primaryJoin (realJoin false (block bits l) left) (bottom b headerLength))
    (realJoin true right (block bits r))

theorem dormant_match (markerId : ι) (bits : Fin 8 → Bool) (l b r : Fin 8)
    (high : HeadBoundary.Record ρ η (Option Bool)) (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    LayoutMatches (dormant bits l b r header.length) (HeadPacketLayout.dormant markerId bits l b r high header) :=
  primaryJoin_match _ _ _ _
    (primaryJoin_match _ _ _ _ (logical_match _ _ (block_match bits l) _) (bottom_match b header))
    (logical_match _ _ (block_match bits r) _)

theorem active_match (markerId : ι) (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (plan : Layout (Fin 8)) (layout : HeadPacketLayout.Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (same : LayoutMatches plan layout) (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    LayoutMatches (active bits l r tl b tr plan direction header.length)
      (HeadPacketLayout.active markerId bits l r tl b tr layout direction low high terminal header) := by
  have attached := attachment_match markerId terminal plan layout same
  cases direction
  · exact primaryJoin_match _ _ _ _
      (primaryJoin_match _ _ _ _
        (realJoin_match false markerId _ _ _ _ _ (block_match bits l) (logical_match _ _ (block_match bits tl) _))
        (bottom_match b header))
      (realJoin_match true markerId _ _ _ _ _
        (realJoin_match true markerId _ _ _ _ _ (block_match bits tr) attached) (block_match bits r))
  · exact primaryJoin_match _ _ _ _
      (primaryJoin_match _ _ _ _
        (realJoin_match false markerId _ _ _ _ _ (block_match bits l)
          (realJoin_match false markerId _ _ _ _ _ attached (block_match bits tl))) (bottom_match b header))
      (realJoin_match true markerId _ _ _ _ _ (logical_match _ _ (block_match bits tr) _) (block_match bits r))

def after (bits : Fin 8 → Bool) (direction : Bool) (newLength dormantLength : Nat) : Layout (Fin 8) :=
  active bits 0 7 4 5 6 (dormant bits 1 2 3 dormantLength) (!direction) newLength

theorem after_match (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool) (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    LayoutMatches (after bits direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId bits direction records newHeader dormantHeader) :=
  active_match markerId bits 0 7 4 5 6 _ _ (dormant_match markerId bits 1 2 3 records.oldHigh dormantHeader)
    (!direction) records.low records.incomingHigh records.incomingTerminal newHeader

theorem output_fits (markerId : ι) (direction : Bool) (old fresh : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (context : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some context)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (source : Source β (Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)) (repacked : Reached.Repacked blocks context source) :
    ∃ plan, after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some plan ∧
      TreeMatches plan context ∧ Fits plan source ∧ plan.shape.leaves.length ≤ 8 := by
  have same := after_match markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader
  rw [found] at same
  cases actual : after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length with
  | none => rw [actual] at same; exact False.elim same
  | some plan =>
    rw [actual] at same
    refine ⟨plan,rfl,same,same.repacked_fits blocks source repacked,?_⟩
    rw [same.shape]
    exact HeadPacketLayout.after_size markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader rfl rfl context found

end ChaCha.Paper20261030.HeadPacketRepair
