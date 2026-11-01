import MultiSplay.ComparatorGuardBlocks
import MultiSplay.ComparatorStableTransaction

/-! # Exposed depth forks give the literal opaque block configurations -/

namespace MultiSplay.ComparatorGuard

open TangoSquared Paper20261030 ColoredStorage PreferredProjection

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

@[simp] theorem join_none {α : Type*} (block : Block α) : join block none = block := by cases block <;> rfl
@[simp] theorem none_join {α : Type*} (block : Block α) : join none block = block := rfl

theorem join_relabel {α β : Type*} (f : α → β) (left right : Block α) :
    (join left right).map (Source.relabel f) = join (left.map (Source.relabel f)) (right.map (Source.relabel f)) := by
  cases left <;> cases right <;> rfl

theorem join_mirror {α : Type*} (left right : Block α) :
    (join left right).map Source.mirror = join (right.map Source.mirror) (left.map Source.mirror) := by
  cases left <;> cases right <;> rfl

theorem boundaryWing_fork {ρ : Type*} (start : Nat) (primary : PrefRouter Nat) (side : Bool)
    (record : ρ) (left right : Source Nat ρ) :
    boundaryWing start primary side (.fork record left right) =
      join (boundaryWing start primary side left) (boundaryWing start primary side right) := by
  unfold boundaryWing
  exact join_relabel _ _ _

theorem boundaryWing_leaf {ρ : Type*} (start : Nat) (primary : PrefRouter Nat)
    (side direction : Bool) (depth key : Nat) (record : ρ)
    (color : PackedPrimary.color start primary depth = some direction)
    (label : ComparatorPrimary.lastGap (PackedPrimary.label start primary depth).subtree = key) :
    boundaryWing start primary side (.leaf depth record) =
      if direction = side then some (.leaf key ()) else none := by
  simp only [boundaryWing,select,color,Option.some.injEq]
  split <;> simp_all [Source.relabel]

def prefixWing (start : Nat) (primary : PrefRouter Nat) (side : Bool)
    (kept : Option (Source Nat Unit)) : Block Nat :=
  kept.bind (boundaryWing start primary side)

/-- No front block is introduced at a component-root switch. -/
theorem boundaryWing_prefix (start : Nat) (primary : PrefRouter Nat) (side : Bool)
    (kept : Option (Source Nat Unit)) (tail : Source Nat Unit) :
    boundaryWing start primary side (ComparatorStableSuffix.prefixPlug kept tail) =
      join (prefixWing start primary side kept) (boundaryWing start primary side tail) := by
  cases kept with
  | none => rfl
  | some tree => exact boundaryWing_fork _ _ _ _ _ _

/-- The exact old-left tree provided by a prepared depth fork. -/
theorem exposed_left (start : Nat) (primary : PrefRouter Nat)
    (kept : Option (Source Nat Unit)) (depth upper : Nat) (tail : Source Nat Unit)
    (color : PackedPrimary.color start primary depth = some false)
    (label : ComparatorPrimary.lastGap (PackedPrimary.label start primary depth).subtree = upper) :
    eraseRecords (ComparatorPrimary.projected start primary (ComparatorStableSuffix.exchangeShape kept depth tail)) =
      leftSource (prefixWing start primary true kept)
        ((prefixWing start primary false kept).map Source.mirror)
        (boundaryWing start primary true tail) ((boundaryWing start primary false tail).map Source.mirror)
        primary.terminal upper := by
  rw [projected_erase]
  simp only [ComparatorStableSuffix.exchangeShape,boundaryWing_prefix,boundaryWing_fork,
    boundaryWing_leaf start primary true false depth upper () color label,
    boundaryWing_leaf start primary false false depth upper () color label,
    Bool.false_eq_true,if_false,if_true,none_join,join_mirror,Option.map_some,Source.mirror]
  rfl

/-- The exact new-right tree after replacing the old depth tail. -/
theorem exposed_right (start : Nat) (primary : PrefRouter Nat)
    (kept : Option (Source Nat Unit)) (depth pivot : Nat) (tail : Source Nat Unit)
    (color : PackedPrimary.color start primary depth = some true)
    (label : ComparatorPrimary.lastGap (PackedPrimary.label start primary depth).subtree = pivot) :
    eraseRecords (ComparatorPrimary.projected start primary (ComparatorStableSuffix.exchangeShape kept depth tail)) =
      rightSource (prefixWing start primary true kept)
        ((prefixWing start primary false kept).map Source.mirror)
        (boundaryWing start primary true tail) ((boundaryWing start primary false tail).map Source.mirror)
        primary.terminal pivot := by
  rw [projected_erase]
  simp only [ComparatorStableSuffix.exchangeShape,boundaryWing_prefix,boundaryWing_fork,
    boundaryWing_leaf start primary true true depth pivot () color label,
    boundaryWing_leaf start primary false true depth pivot () color label,
    Bool.true_eq_false,if_false,if_true,none_join,join_mirror,Option.map_some,Option.map_none,join_none,Source.mirror]
  rfl

end MultiSplay.ComparatorGuard
