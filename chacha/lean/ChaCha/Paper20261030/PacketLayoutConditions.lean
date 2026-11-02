import ChaCha.Paper20261030.MixedPacketRepresentation

/-!
# Exactly which residual roots a mixed layout requires

A requirement on an opaque packet is consulted only at a prefix layer.
Whole packets, raw headers, and primary joins introduce no such condition.
Both head layouts impose exactly the same requirements on the six
possibly present real-wing blocks; their two virtual bottoms are exempt.
-/

namespace ChaCha.Paper20261030.PacketConditions

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers HeadPacketLayout

variable {κ α β ρ ι η : Type*}

def packet (require : Packet α ρ ι → Prop) (base : Packet α ρ ι) : Expression α ρ ι → Prop
  | .base => True
  | .raw _ rest | .whole _ _ _ rest => packet require base rest
  | .prefix _ => require base

def tree (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι)) : Source κ (Expression α ρ ι) → Prop
  | .leaf key expression => packet require (blocks key).rootRecord expression
  | .fork expression left right => packet require [] expression ∧ tree require blocks left ∧ tree require blocks right

def layout (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι)) (value : Layout κ α ρ ι) : Prop :=
  ∀ source, value = some source → tree require blocks source

def wings (require : Packet α ρ ι → Prop) (bits : Fin 8 → Bool) (blocks : Fin 8 → Source β (Packet α ρ ι)) : Prop :=
  ∀ key, key ≠ 2 → key ≠ 5 → bits key = true → require (blocks key).rootRecord

theorem packet_ready (base : Packet α ρ ι) (expression : Expression α ρ ι) :
    packet (fun base => Ready base (.prefix [])) base expression ↔ Ready base expression := by
  induction expression <;> simp_all only [packet,Ready]

theorem packet_ordinary (markerId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι) :
    packet (fun base => OrdinaryBase markerId base (.prefix [])) base expression ↔ OrdinaryBase markerId base expression := by
  induction expression <;> simp_all only [packet,OrdinaryBase]

theorem tree_ordinary (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (context : Source κ (Expression α ρ ι)) :
    tree (fun base => OrdinaryBase markerId base (.prefix [])) blocks context ↔ Reached.Ordinary markerId blocks context := by
  induction context <;> simp_all only [tree,Reached.Ordinary,packet_ordinary]

theorem push_iff (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (edit : Expression α ρ ι → Expression α ρ ι)
    (same : ∀ base expression, packet require base (edit expression) ↔ packet require base expression)
    (value : Layout κ α ρ ι) : layout require blocks (push edit value) ↔ layout require blocks value := by
  cases value with
  | none => simp [layout,push]
  | some source =>
    cases source <;> simp [layout,push,Source.setRoot,Source.rootRecord,tree,same]

theorem logical_iff (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (records : List ρ) (value : Layout κ α ρ ι) :
    layout require blocks (push (addLogical records) value) ↔ layout require blocks value :=
  push_iff require blocks _ (by intro base expression; cases expression <;> rfl) value

theorem realJoin_iff (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (markerId : ι) (records : List ρ) (left right : Layout κ α ρ ι) :
    layout require blocks (realJoin markerId records left right) ↔ layout require blocks left ∧ layout require blocks right := by
  cases left <;> cases right <;>
    simp only [realJoin,logical_iff] <;> simp [layout,tree,packet]

theorem primaryJoin_iff (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (left right : Layout κ α ρ ι) :
    layout require blocks (primaryJoin left right) ↔ layout require blocks left ∧ layout require blocks right := by
  cases left <;> cases right <;> simp [primaryJoin,layout,tree,packet]

theorem block_iff (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (bits : κ → Bool) (key : κ) :
    layout require blocks (block bits key) ↔ (bits key = true → require (blocks key).rootRecord) := by
  cases present : bits key <;> simp [block,present,layout,tree,packet]

theorem bottom_true (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (key : κ) (header : Packet α ρ ι) : layout require blocks (bottom key header) := by
  simp [bottom,layout,tree,packet]

theorem attachment_iff (require : Packet α ρ ι → Prop) (blocks : κ → Source β (Packet α ρ ι))
    (markerId : ι) (record : ρ) (value : Layout κ α ρ ι) :
    layout require blocks (attachment markerId record value) ↔ layout require blocks value :=
  push_iff require blocks _ (by intro base expression; rfl) value

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem dormant_iff (require : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (markerId : ι) (bits : Fin 8 → Bool) (l b r : Fin 8) (high : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    layout require blocks (dormant markerId bits l b r high header) ↔
      layout require blocks (block bits l) ∧ layout require blocks (block bits r) := by
  simp only [dormant,primaryJoin_iff,logical_iff,bottom_true,and_true]

theorem active_iff (require : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (markerId : ι) (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (child : Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι) (direction : Bool)
    (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    layout require blocks (active markerId bits l r tl b tr child direction low high terminal header) ↔
      layout require blocks (block bits l) ∧ layout require blocks (block bits r) ∧
      layout require blocks (block bits tl) ∧ layout require blocks (block bits tr) ∧ layout require blocks child := by
  cases direction <;>
    simp only [active,Bool.false_eq_true,if_false,if_true,primaryJoin_iff,realJoin_iff,logical_iff,
      attachment_iff,bottom_true,and_true] <;> tauto

theorem before_iff (require : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool) (records : HeadBoundary.Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    layout require blocks (before markerId bits direction records oldHeader incomingHeader) ↔ wings require bits blocks := by
  simp only [before,active_iff,dormant_iff,block_iff]
  constructor
  · rintro ⟨h0,h7,h1,h3,h4,h6⟩ key not2 not5 present
    fin_cases key
    · exact h0 present
    · exact h1 present
    · exact False.elim (not2 rfl)
    · exact h3 present
    · exact h4 present
    · exact False.elim (not5 rfl)
    · exact h6 present
    · exact h7 present
  · intro good
    exact ⟨good 0 (by decide) (by decide),good 7 (by decide) (by decide),good 1 (by decide) (by decide),
      good 3 (by decide) (by decide),good 4 (by decide) (by decide),good 6 (by decide) (by decide)⟩

theorem after_iff (require : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool) (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    layout require blocks (after markerId bits direction records newHeader dormantHeader) ↔ wings require bits blocks := by
  simp only [after,active_iff,dormant_iff,block_iff]
  constructor
  · rintro ⟨h0,h7,h4,h6,h1,h3⟩ key not2 not5 present
    fin_cases key
    · exact h0 present
    · exact h1 present
    · exact False.elim (not2 rfl)
    · exact h3 present
    · exact h4 present
    · exact False.elim (not5 rfl)
    · exact h6 present
    · exact h7 present
  · intro good
    exact ⟨good 0 (by decide) (by decide),good 7 (by decide) (by decide),good 4 (by decide) (by decide),
      good 6 (by decide) (by decide),good 1 (by decide) (by decide),good 3 (by decide) (by decide)⟩

end ChaCha.Paper20261030.PacketConditions
