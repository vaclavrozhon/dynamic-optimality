import ChaCha.Paper20261030.LocalPackedContextStaging

/-!
# Suppressing absent blocks in a finite packet context

`prune` removes absent leaves and contracts vertices with one remaining
child. Their prefixes are concatenated at the reached surviving vertex.
Only the finite context and block-presence bits are inspected. The scalar
blueprint is obtained by the same recursion with addition of lengths.

The result has exactly the surviving leaves in their original order and
realizes precisely the original decorated projection. In particular an
eight-block context produces a physical staging traversal with at most
eight blocks, even when several logical boundaries share one vertex.
-/

namespace ChaCha.Paper20261030.PacketContext

open ColoredStorage SourcePointer ProjectionLocal OrderedContext

variable {κ α ρ σ τ : Type*}

def push (combine : σ → σ → σ) (record : σ) (context : Source κ σ) : Source κ σ :=
  context.setRoot (combine record context.rootRecord)

def combine (merge : σ → σ → σ) (record : σ) : Option (Source κ σ) → Option (Source κ σ) → Option (Source κ σ)
  | none,none => none
  | some left,none => some (push merge record left)
  | none,some right => some (push merge record right)
  | some left,some right => some (.fork record left right)

def prune (merge : σ → σ → σ) (bits : κ → Bool) : Source κ σ → Option (Source κ σ)
  | .leaf key record => if bits key then some (.leaf key record) else none
  | .fork record left right => combine merge record (prune merge bits left) (prune merge bits right)

private theorem push_shape (merge : σ → σ → σ) (record : σ) (context : Source κ σ) :
    (push merge record context).shape = context.shape := by cases context <;> rfl

private theorem push_root (merge : σ → σ → σ) (record : σ) (context : Source κ σ) :
    (push merge record context).rootRecord = merge record context.rootRecord := by cases context <;> rfl

private theorem map_push (f : σ → τ) (merge : σ → σ → σ) (next : τ → τ → τ)
    (respects : ∀ a b, f (merge a b) = next (f a) (f b)) (record : σ) (context : Source κ σ) :
    (push merge record context).mapRecords f = push next (f record) (context.mapRecords f) := by
  cases context <;> simp only [push,Source.rootRecord,Source.setRoot,Source.mapRecords,respects]

private theorem map_twice {υ : Type*} (f : σ → τ) (g : τ → υ) (context : Source κ σ) :
    (context.mapRecords f).mapRecords g = context.mapRecords (g ∘ f) := by
  induction context <;> simp_all only [Source.mapRecords,Function.comp_def]

theorem map_prune (f : σ → τ) (merge : σ → σ → σ) (next : τ → τ → τ)
    (respects : ∀ a b, f (merge a b) = next (f a) (f b)) (bits : κ → Bool) (context : Source κ σ) :
    (prune merge bits context).map (Source.mapRecords f) = prune next bits (context.mapRecords f) := by
  induction context with
  | leaf key record => cases present : bits key <;> simp only [prune,present,Source.mapRecords,
      Bool.false_eq_true,if_false,if_true,Option.map_none,Option.map_some]
  | fork record left right ihl ihr =>
    simp only [prune,Source.mapRecords,← ihl,← ihr]
    cases prune merge bits left <;> cases prune merge bits right <;>
      simp only [combine,Option.map_none,Option.map_some,Source.mapRecords,map_push f merge next respects]

theorem lengths (bits : κ → Bool) (context : Source κ (List ρ)) :
    (prune List.append bits context).map (Source.mapRecords List.length) =
      prune Nat.add bits (context.mapRecords List.length) :=
  map_prune List.length List.append Nat.add (fun _ _ => List.length_append) bits context

def all (blocks : κ → Source α (List ρ)) : Source κ (List ρ) → Source α (List ρ)
  | .leaf key records => (blocks key).setRoot (records++(blocks key).rootRecord)
  | .fork records left right => .fork records (all blocks left) (all blocks right)

theorem all_decorated (blocks : κ → Source α (List ρ)) (context : Source κ (List ρ)) :
    some (all blocks context) = decorated (fun key => some (blocks key)) context := by
  induction context with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [all,decorated,← ihl,← ihr,join,decorate,Option.map_some,
      Source.rootRecord,Source.setRoot,List.append_nil]

private theorem all_push (blocks : κ → Source α (List ρ)) (records : List ρ) (context : Source κ (List ρ)) :
    all blocks (push List.append records context) =
      (all blocks context).setRoot (records++(all blocks context).rootRecord) := by
  cases context with
  | leaf key tail =>
    cases blockEq : blocks key <;>
      simp only [all,push,Source.setRoot,Source.rootRecord,blockEq] <;>
      congr 1 <;> exact List.append_assoc _ _ _
  | fork => rfl

private theorem realize_combine (blocks : κ → Source α (List ρ)) (records : List ρ)
    (left right : Option (Source κ (List ρ))) :
    (combine List.append records left right).map (all blocks) =
      decorate records (join (left.map (all blocks)) (right.map (all blocks))) := by
  cases left <;> cases right <;> simp only [combine,Option.map_none,Option.map_some,
    join,decorate,all,all_push,Source.setRoot,Source.rootRecord,List.append_nil]

/-- The target context contains only physically present blocks. -/
theorem realizes (bits : κ → Bool) (blocks : κ → Source α (List ρ)) (context : Source κ (List ρ)) :
    (prune List.append bits context).map (all blocks) =
      decorated (fun key => if bits key then some (blocks key) else none) context := by
  induction context with
  | leaf key records =>
    cases present : bits key <;> simp only [prune,present,Bool.false_eq_true,if_false,if_true,
      Option.map_none,Option.map_some,decorated,decorate,all]
  | fork records left right ihl ihr =>
    simp only [prune,realize_combine,decorated,ihl,ihr]

def leaves : Option (Source κ σ) → List κ
  | none => []
  | some context => context.shape.leaves

private theorem leaves_combine (merge : σ → σ → σ) (record : σ)
    (left right : Option (Source κ σ)) :
    leaves (combine merge record left right) = leaves left ++ leaves right := by
  cases left <;> cases right <;> simp only [combine,leaves,push_shape,
    Source.shape,RouterProjection.Router.leaves,List.nil_append,List.append_nil]

theorem surviving_leaves (merge : σ → σ → σ) (bits : κ → Bool) (context : Source κ σ) :
    leaves (prune merge bits context) = context.shape.leaves.filter bits := by
  induction context with
  | leaf key record =>
    cases present : bits key <;> simp only [prune,present,Bool.false_eq_true,if_false,if_true,
      leaves,Source.shape,RouterProjection.Router.leaves,List.filter_cons,List.filter_nil]
  | fork record left right ihl ihr =>
    simp only [prune,leaves_combine,Source.shape,RouterProjection.Router.leaves,List.filter_append,ihl,ihr]

theorem size_le (merge : σ → σ → σ) (bits : κ → Bool) (context target : Source κ σ)
    (found : prune merge bits context = some target) :
    target.shape.leaves.length ≤ context.shape.leaves.length := by
  have equal := surviving_leaves merge bits context
  rw [found] at equal
  change target.shape.leaves = _ at equal
  rw [equal]
  exact List.length_filter_le _ _

theorem eight_bounds (merge : σ → σ → σ) (bits : κ → Bool) (context target : Source κ σ)
    (eight : context.shape.leaves.length = 8) (found : prune merge bits context = some target) :
    PhysicalPacketStaging.Context.budget target ≤ 58 := by
  have size := size_le merge bits context target found
  have cost := PhysicalPacketStaging.Context.budget_leaves target
  rw [eight] at size
  omega

theorem staged_all {β ι : Type*} (markerId : ι)
    (blocks : κ → Source β (PhysicalPacketStaging.Packet α ρ ι))
    (context : Source κ (PhysicalPacketStaging.Context.ContextRecord ρ ι)) :
    PhysicalPacketStaging.Context.stagedTree markerId blocks context =
      all blocks (context.mapRecords (fun record => record.1.map (PhysicalPacketStaging.marker markerId))) := by
  induction context <;> simp_all only [PhysicalPacketStaging.Context.stagedTree,all,Source.mapRecords]

/-- The execution is generated from the pruned scalar blueprint. Its
output is the original decorated context, with absent blocks suppressed.
Physical ids and old pointer fields occur only in the input invariant. -/
theorem stage_pruned {β ι : Type*} (markerId : ι) (bits : κ → Bool)
    (blocks : κ → Source β (PhysicalPacketStaging.Packet α ρ ι))
    (packets : ∀ key, PhysicalPacketStaging.Context.RootPacket (blocks key))
    (original : Source κ (List ρ))
    (context : Source κ (PhysicalPacketStaging.Context.ContextRecord ρ ι))
    (found : prune List.append bits original = some (context.mapRecords Prod.fst)) :
    RecordEditScript.Transforms (PhysicalPacketStaging.Context.edit markerId)
      (PhysicalPacketStaging.Context.commands (context.mapRecords (fun record => record.1.length)))
      (PhysicalPacketStaging.Context.inputTree blocks context)
      (PhysicalPacketStaging.Context.stagedTree markerId blocks context)
      (PhysicalPacketStaging.Context.budget context) ∧
    some (PhysicalPacketStaging.Context.stagedTree markerId blocks context) =
      decorated (fun key => if bits key then some (blocks key) else none)
        (original.mapRecords (List.map (PhysicalPacketStaging.marker markerId))) := by
  refine ⟨PhysicalPacketStaging.Context.stage markerId blocks packets context,?_⟩
  have normalized := map_prune (List.map (PhysicalPacketStaging.marker (α := α) markerId))
    List.append List.append (fun _ _ => List.map_append) bits original
  rw [found,Option.map_some,map_twice] at normalized
  rw [← realizes,← normalized,Option.map_some,staged_all]
  rfl

end ChaCha.Paper20261030.PacketContext
