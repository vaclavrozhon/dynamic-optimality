import MultiSplay.ComparatorVirtualProjection

/-! # Literal record-free blocks of the original-key projection

Erasing records leaves the actual packed physical shape unchanged. These
identities expose the constant number of joins at a prepared depth fork;
the contents of the prefix and tail blocks remain opaque.
-/

namespace MultiSplay.ComparatorGuard

open ChaCha Paper20261030
open ColoredStorage PrimaryPhysical PrimaryWings

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Plain (α : Type*) := Source α Unit
abbrev Block (α : Type*) := Option (Plain α)

def eraseRecords {α ρ : Type*} (tree : Source α ρ) : Plain α :=
  tree.mapRecords (fun _ => ())

def eraseBlock {α ρ : Type*} (tree : Option (Source α ρ)) : Block α :=
  tree.map eraseRecords

def join {α : Type*} : Block α → Block α → Block α
  | none,right => right
  | left,none => left
  | some left,some right => some (.fork () left right)

def select {α ρ C : Type*} [DecidableEq C] (color : α → C) (side : C) :
    Source α ρ → Block α
  | .leaf key _ => if color key = side then some (.leaf key ()) else none
  | .fork _ left right => join (select color side left) (select color side right)

@[simp] theorem eraseRecords_setRoot {α ρ : Type*} (tree : Source α ρ) (record : ρ) :
    eraseRecords (tree.setRoot record) = eraseRecords tree := by cases tree <;> rfl

@[simp] theorem eraseRecords_mapRecords {α ρ τ : Type*} (f : ρ → τ) (tree : Source α ρ) :
    eraseRecords (tree.mapRecords f) = eraseRecords tree := by
  induction tree <;> simp_all [eraseRecords,Source.mapRecords]

@[simp] theorem eraseRecords_relabel {α β ρ : Type*} (f : α → β) (tree : Source α ρ) :
    eraseRecords (tree.relabel f) = (eraseRecords tree).relabel f := by
  induction tree <;> simp_all [eraseRecords,Source.mapRecords,Source.relabel]

@[simp] theorem eraseRecords_mirror {α ρ : Type*} (tree : Source α ρ) :
    eraseRecords tree.mirror = (eraseRecords tree).mirror := by
  induction tree <;> simp_all [eraseRecords,Source.mapRecords,Source.mirror]

@[simp] theorem eraseBlock_join {α ρ : Type*} (left right : ProjectionLocal.Projected α ρ) :
    eraseBlock (ProjectionLocal.join left right) = join (eraseBlock left) (eraseBlock right) := by
  cases left <;> cases right <;> rfl

@[simp] theorem eraseBlock_attach {α ρ : Type*} (active : Bool) (record : ρ)
    (tree : ProjectionLocal.Projected α ρ) :
    eraseBlock (ProjectionLocal.attach active record tree) = eraseBlock tree := by
  cases active <;> cases tree <;> simp [ProjectionLocal.attach,
    eraseBlock,eraseRecords_setRoot]

/-- Record ownership affects stored payloads, never these physical blocks. -/
theorem eraseBlock_packed {α ρ C : Type*} [DecidableEq α] [LinearOrder C]
    (color : α → C) (side : C) (tree : Source α ρ) :
    eraseBlock (packed color side tree) = select color side tree := by
  induction tree with
  | leaf key record =>
      by_cases yes : color key = side <;>
        simp [packed,pack,yes,Stored.toSource,eraseBlock,eraseRecords,Source.mapRecords,select]
  | fork record left right ihl ihr =>
      rw [packed_fork,eraseBlock_attach,eraseBlock_join,ihl,ihr]
      rfl

@[simp] theorem gaps_eraseRecords {α ρ : Type*} (tree : Source α ρ) :
    GapBST.gaps (eraseRecords tree) = GapBST.gaps tree := by
  have last : ∀ tree : Source α ρ, GapBST.lastKey (eraseRecords tree) = GapBST.lastKey tree := by
    intro tree
    induction tree <;> simp_all [eraseRecords,Source.mapRecords,GapBST.lastKey]
  induction tree <;> simp_all [eraseRecords,Source.mapRecords,GapBST.gaps]

@[simp] theorem last_eraseRecords {α ρ : Type*} (tree : Source α ρ) :
    GapBST.lastKey (eraseRecords tree) = GapBST.lastKey tree := by
  induction tree <;> simp_all [eraseRecords,Source.mapRecords,GapBST.lastKey]

/-- Substitute the actual original boundary key for each retained port. -/
def boundaryWing {ρ : Type*} (start : Nat) (primary : PreferredProjection.PrefRouter Nat)
    (side : Bool) (source : Source Nat ρ) : Block Nat :=
  (select (PackedPrimary.color start primary) (some side) source).map
    (Source.relabel (fun key => ComparatorPrimary.lastGap
      (PackedPrimary.label start primary key).subtree))

def componentBlock {α : Type*} (left right : Block α) (terminal : α) : Plain α :=
  match left,right with
  | none,none => .leaf terminal ()
  | some left,none => .fork () left (.leaf terminal ())
  | none,some right => .fork () (.leaf terminal ()) right
  | some left,some right => .fork () (.fork () left (.leaf terminal ())) right

private theorem erase_graft_collapsed {ρ : Type*}
    (tree : Source (Exit Nat) (List (PackedPrimary.Datum ρ))) :
    eraseRecords (SourcePayloads.graft (ComparatorPrimary.collapsed ρ) tree) =
      (eraseRecords tree).relabel (fun exit => ComparatorPrimary.lastGap exit.subtree) := by
  induction tree <;>
    simp_all [SourcePayloads.graft,ComparatorPrimary.collapsed,Source.setRoot,
      eraseRecords,Source.mapRecords,Source.relabel]

private theorem erase_wing {ρ : Type*} (wing : RoutingWing Nat ρ) :
    eraseBlock (graftWing (ComparatorPrimary.collapsed ρ) (PackedPrimary.liftWing wing)) =
      (eraseBlock wing).map (Source.relabel (fun exit => ComparatorPrimary.lastGap exit.subtree)) := by
  cases wing with
  | none => rfl
  | some tree =>
      simp only [graftWing,PackedPrimary.liftWing,Option.map_some,eraseBlock,erase_graft_collapsed,
        eraseRecords_mapRecords]

private theorem relabel_relabel {α β γ ρ : Type*} (f : α → β) (g : β → γ)
    (tree : Source α ρ) : (tree.relabel f).relabel g = tree.relabel (g ∘ f) := by
  induction tree <;> simp_all [Source.relabel]

private theorem mirror_relabel {α β ρ : Type*} (f : α → β) (tree : Source α ρ) :
    tree.mirror.relabel f = (tree.relabel f).mirror := by
  induction tree <;> simp_all [Source.relabel,Source.mirror]

@[simp] theorem eraseBlock_relabel {α β ρ : Type*} (f : α → β) (tree : Option (Source α ρ)) :
    eraseBlock (tree.map (Source.relabel f)) = (eraseBlock tree).map (Source.relabel f) := by
  cases tree <;> simp [eraseBlock]

@[simp] theorem eraseBlock_mirror {α ρ : Type*} (tree : Option (Source α ρ)) :
    eraseBlock (tree.map Source.mirror) = (eraseBlock tree).map Source.mirror := by
  cases tree <;> simp [eraseBlock]

private theorem erase_plan_left {ρ : Type*} (start : Nat)
    (primary : PreferredProjection.PrefRouter Nat) (source : Source Nat ρ) :
    eraseBlock (graftWing (ComparatorPrimary.collapsed ρ)
      (PackedPrimary.liftWing (PackedPrimary.plan start primary source).left)) =
      boundaryWing start primary true source := by
  rw [erase_wing]
  simp only [PackedPrimary.plan,PackedPrimary.wing,eraseBlock_relabel,eraseBlock_packed,
    Option.map_map]
  unfold boundaryWing
  congr 1
  funext tree
  exact relabel_relabel _ _ tree

private theorem erase_plan_right {ρ : Type*} (start : Nat)
    (primary : PreferredProjection.PrefRouter Nat) (source : Source Nat ρ) :
    eraseBlock (graftWing (ComparatorPrimary.collapsed ρ)
      (PackedPrimary.liftWing (PackedPrimary.plan start primary source).right)) =
      (boundaryWing start primary false source).map Source.mirror := by
  rw [erase_wing]
  simp only [PackedPrimary.plan]
  rw [eraseBlock_mirror]
  simp only [PackedPrimary.wing,eraseBlock_relabel,eraseBlock_packed,Option.map_map]
  unfold boundaryWing
  rw [Option.map_map]
  congr 1
  funext tree
  simp only [Function.comp_apply,mirror_relabel,relabel_relabel]
  rfl

/-- Exact physical shape, with every record erased and every real key retained. -/
theorem projected_erase {ρ : Type*} (start : Nat)
    (primary : PreferredProjection.PrefRouter Nat) (source : Source Nat ρ) :
    eraseRecords (ComparatorPrimary.projected start primary source) =
      componentBlock (boundaryWing start primary true source)
        ((boundaryWing start primary false source).map Source.mirror) primary.terminal := by
  have component : ∀ (left right : Wing Nat (PackedPrimary.Datum ρ)) (terminal : Nat),
      eraseRecords (PrimaryPhysical.component left right terminal []) =
        componentBlock (eraseBlock left) (eraseBlock right) terminal := by
    intro left right terminal
    cases left <;> cases right <;> rfl
  rw [ComparatorPrimary.projected,component,erase_plan_left,erase_plan_right]

/-- Therefore the same identity holds for the actual ordinary BST. -/
theorem projectedTree_blocks {lower upper : Nat} {ρ : Type*}
    (state : EndpointEncoding.State) (reference : DynamicOptimality.BST lower upper)
    (start : Nat) (source : Source Nat ρ) :
    ComparatorPrimary.projectedTree state reference start source =
      GapBST.gaps (componentBlock
        (boundaryWing start (ComparatorPrimary.routing state reference) true source)
        ((boundaryWing start (ComparatorPrimary.routing state reference) false source).map Source.mirror)
        (ComparatorPrimary.routing state reference).terminal) := by
  rw [← projected_erase,gaps_eraseRecords]
  rfl

end MultiSplay.ComparatorGuard
