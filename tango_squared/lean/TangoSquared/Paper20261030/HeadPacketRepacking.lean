import TangoSquared.Paper20261030.LocalReachedPacketRepacking

/-! The packet layout computed from actual boundary records satisfies
the residual-packet precondition of local repacking. Only a present
routing block needs an ordinary root packet. The two virtual bottom
blocks do not need real packets, and absent wings impose no condition.
-/

namespace TangoSquared.Paper20261030.HeadPacketLayout

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers HeadBoundary

variable {κ α β ρ ι η : Type*}

def Good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (layout : Layout κ α ρ ι) : Prop :=
  ∀ tree, layout = some tree → Reached.Ordinary markerId blocks tree

theorem addLogical_ordinary (markerId : ι) (records : List ρ) (base : Packet α ρ ι) (expression : Expression α ρ ι) :
    OrdinaryBase markerId base (addLogical records expression) ↔ OrdinaryBase markerId base expression := by
  cases expression <;> rfl

private theorem good_push (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (edit : Expression α ρ ι → Expression α ρ ι)
    (preserves : ∀ base expression, OrdinaryBase markerId base expression → OrdinaryBase markerId base (edit expression))
    (layout : Layout κ α ρ ι) (good : Good markerId blocks layout) : Good markerId blocks (push edit layout) := by
  intro tree found
  cases layout with
  | none => cases found
  | some original =>
    simp only [push,Option.map_some,Option.some.injEq] at found
    subst tree
    have valid := good original rfl
    cases original with
    | leaf key expression => exact preserves _ _ valid
    | fork expression left right => exact ⟨preserves _ _ valid.1,valid.2⟩

theorem logical_good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (records : List ρ)
    (layout : Layout κ α ρ ι) (good : Good markerId blocks layout) :
    Good markerId blocks (push (addLogical records) layout) :=
  good_push markerId blocks _ (fun base expression => (addLogical_ordinary markerId records base expression).mpr) layout good

theorem realJoin_good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (records : List ρ)
    (left right : Layout κ α ρ ι) (hl : Good markerId blocks left) (hr : Good markerId blocks right) :
    Good markerId blocks (realJoin markerId records left right) := by
  cases left with
  | none => cases right with
    | none => intro tree found; cases found
    | some right => exact logical_good markerId blocks records _ hr
  | some left => cases right with
    | none => exact logical_good markerId blocks records _ hl
    | some right =>
      intro tree found
      cases found
      exact ⟨trivial,hl left rfl,hr right rfl⟩

theorem primaryJoin_good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (left right : Layout κ α ρ ι) (hl : Good markerId blocks left) (hr : Good markerId blocks right) :
    Good markerId blocks (primaryJoin left right) := by
  cases left with
  | none => exact hr
  | some left => cases right with
    | none => exact hl
    | some right =>
      intro tree found
      cases found
      exact ⟨trivial,hl left rfl,hr right rfl⟩

theorem block_good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (bits : κ → Bool) (key : κ)
    (packet : bits key = true → OrdinaryBase markerId (blocks key).rootRecord (.prefix [])) :
    Good markerId blocks (block bits key) := by
  intro tree found
  unfold block at found
  split at found
  · rename_i present
    cases found
    exact packet present
  · cases found

theorem bottom_good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (key : κ) (header : Packet α ρ ι) :
    Good markerId blocks (bottom key header) := by
  intro tree found
  cases found
  trivial

theorem attachment_good (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (record : ρ) (child : Layout κ α ρ ι) (good : Good markerId blocks child) :
    Good markerId blocks (attachment markerId record child) :=
  good_push markerId blocks (fun expression => .whole markerId [record] placeholder (.raw [none] expression))
    (fun _ _ valid => valid) child good

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem dormant_good (markerId : ι)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (bits : Fin 8 → Bool) (l b r : Fin 8) (high : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (hl : Good markerId blocks (block bits l)) (hr : Good markerId blocks (block bits r)) :
    Good markerId blocks (dormant markerId bits l b r high header) :=
  primaryJoin_good _ _ _ _ (primaryJoin_good _ _ _ _
    (logical_good _ _ _ _ hl) (bottom_good _ _ _ _)) (logical_good _ _ _ _ hr)

theorem active_good (markerId : ι)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (boundary : Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (hl : Good markerId blocks (block bits l)) (hr : Good markerId blocks (block bits r))
    (htl : Good markerId blocks (block bits tl)) (htr : Good markerId blocks (block bits tr))
    (hb : Good markerId blocks boundary) :
    Good markerId blocks (active markerId bits l r tl b tr boundary direction low high terminal header) := by
  have child := attachment_good markerId blocks terminal boundary hb
  cases direction
  · exact primaryJoin_good _ _ _ _ (primaryJoin_good _ _ _ _
      (realJoin_good _ _ _ _ _ hl (logical_good _ _ _ _ htl)) (bottom_good _ _ _ _))
      (realJoin_good _ _ _ _ _ (realJoin_good _ _ _ _ _ htr child) hr)
  · exact primaryJoin_good _ _ _ _ (primaryJoin_good _ _ _ _
      (realJoin_good _ _ _ _ _ hl (realJoin_good _ _ _ _ _ child htl)) (bottom_good _ _ _ _))
      (realJoin_good _ _ _ _ _ (logical_good _ _ _ _ htr) hr)

def WingRoots (markerId : ι) (bits : Fin 8 → Bool) (blocks : Fin 8 → Source β (Packet α ρ ι)) : Prop :=
  ∀ key, key ≠ 2 → key ≠ 5 → bits key = true → OrdinaryBase markerId (blocks key).rootRecord (.prefix [])

theorem after_good (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : WingRoots markerId bits blocks) :
    Good markerId blocks (after markerId bits direction records newHeader dormantHeader) := by
  have blockGood (key : Fin 8) (h2 : key ≠ 2) (h5 : key ≠ 5) := block_good markerId blocks bits key (ordinary key h2 h5)
  exact active_good markerId blocks bits 0 7 4 5 6 _ (!direction) _ _ _ newHeader
    (blockGood 0 (by decide) (by decide)) (blockGood 7 (by decide) (by decide))
    (blockGood 4 (by decide) (by decide)) (blockGood 6 (by decide) (by decide))
    (dormant_good markerId blocks bits 1 2 3 records.oldHigh dormantHeader
      (blockGood 1 (by decide) (by decide)) (blockGood 3 (by decide) (by decide)))

theorem before_good (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : WingRoots markerId bits blocks) :
    Good markerId blocks (before markerId bits direction records oldHeader incomingHeader) := by
  have blockGood (key : Fin 8) (h2 : key ≠ 2) (h5 : key ≠ 5) := block_good markerId blocks bits key (ordinary key h2 h5)
  exact active_good markerId blocks bits 0 7 1 2 3 _ direction _ _ _ oldHeader
    (blockGood 0 (by decide) (by decide)) (blockGood 7 (by decide) (by decide))
    (blockGood 1 (by decide) (by decide)) (blockGood 3 (by decide) (by decide))
    (dormant_good markerId blocks bits 4 5 6 records.incomingHigh incomingHeader
      (blockGood 4 (by decide) (by decide)) (blockGood 6 (by decide) (by decide)))

end TangoSquared.Paper20261030.HeadPacketLayout
