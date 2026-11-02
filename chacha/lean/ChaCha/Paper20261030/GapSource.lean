import ChaCha.Paper20261030.SourcePointer
import ChaCha.Paper20261030.GraftedMetadata

/-!
# Separator records with actual depth ports in their gaps

Each auxiliary separator becomes an internal record vertex. Its inorder
gaps hold existing leaf-oriented port trees. Thus `k` separators produce
`k+1` ports, not extra leaves for the separator records. Actual pointer
and metadata traces lift to this record-decorated representation with
exactly the same cost.
-/

namespace ChaCha.Paper20261030.GapSource

open ChaCha.MTR ColoredStorage

variable {α ρ : Type*}

def encode (t : MTR.Tree ρ) (ports : Nat → Source α ρ) (base : Nat) : Source α ρ :=
  match t with
  | .empty => ports base
  | .node l record r => .fork record (encode l ports base) (encode r ports (base + l.size + 1))

theorem encode_leaves (t : MTR.Tree ρ) (ports : Nat → Source α ρ) (base : Nat) :
    (encode t ports base).shape.leaves =
      (List.range' base (t.size + 1)).flatMap (fun i => (ports i).shape.leaves) := by
  induction t generalizing base with
  | empty => simp [encode,MTR.Tree.size,List.range']
  | node l record r ihl ihr =>
    simp only [encode,Source.shape,RouterProjection.Router.leaves,ihl,ihr,MTR.Tree.size]
    have hn : l.size + 1 + r.size + 1 = (l.size + 1) + (r.size + 1) := by omega
    rw [hn]
    symm
    rw [← List.range'_append_1,List.flatMap_append]
    simp only [Nat.add_assoc]

theorem encode_port_word (t : MTR.Tree ρ) (record : Nat → ρ) (base : Nat) :
    (encode t (fun i => Source.leaf i (record i)) base).shape.leaves = List.range' base (t.size + 1) := by
  simpa only [Source.shape,RouterProjection.Router.leaves,List.flatMap_singleton'] using
    encode_leaves t (fun i => Source.leaf i (record i)) base

def frames (ports : Nat → Source α ρ) (base focusSize : Nat) :
    List (Pointer.Frame ρ) → List (SourcePointer.Frame α ρ)
  | [] => []
  | .left record r :: rest =>
    .left record (encode r ports (base + PointerGraft.offset rest + focusSize + 1)) ::
      frames ports base (focusSize + 1 + r.size) rest
  | .right l record :: rest =>
    .right (encode l ports (base + PointerGraft.offset rest)) record ::
      frames ports base (l.size + 1 + focusSize) rest

def cursor (ports : Nat → Source α ρ) (base : Nat) (c : Pointer.Cursor ρ) : SourcePointer.Cursor α ρ :=
  ⟨encode c.focus ports (base + PointerGraft.offset c.ancestors),frames ports base c.focus.size c.ancestors⟩

theorem plug_frames (ports : Nat → Source α ρ) (base : Nat)
    (focus : MTR.Tree ρ) (ancestors : List (Pointer.Frame ρ)) :
    SourcePointer.plug (encode focus ports (base + PointerGraft.offset ancestors))
      (frames ports base focus.size ancestors) = encode (Pointer.plug focus ancestors) ports base := by
  induction ancestors generalizing focus with
  | nil => simp [PointerGraft.offset,frames,Pointer.plug,SourcePointer.plug]
  | cons frame rest ih =>
    cases frame with
    | left record r =>
      simpa only [PointerGraft.offset,frames,Pointer.plug,SourcePointer.plug,encode,MTR.Tree.size,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (.node focus record r)
    | right l record =>
      simpa only [PointerGraft.offset,frames,Pointer.plug,SourcePointer.plug,encode,MTR.Tree.size,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (.node l record focus)

theorem cursor_tree (ports : Nat → Source α ρ) (base : Nat) (c : Pointer.Cursor ρ) :
    (cursor ports base c).tree = encode c.tree ports base :=
  plug_frames ports base c.focus c.ancestors

theorem nav {c d : Pointer.Cursor ρ} (h : Pointer.Step c d)
    (ports : Nat → Source α ρ) (base : Nat) :
    SourcePointer.Step (cursor ports base c) (cursor ports base d) := by
  cases h <;> simp only [cursor,PointerGraft.offset,frames,encode,MTR.Tree.size]
  all_goals simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · exact .left _ _ _ _
  · exact .right _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _

variable {κ : Type*} {β : κ → Type*}

theorem metadata_step {c d : Auxiliary.Metadata.Cursor κ β} (h : Auxiliary.Metadata.Step c d)
    (ports : Nat → Source α (Auxiliary.NodeRecord κ β)) (base : Nat) :
    SourcePointer.Step (cursor ports base c) (cursor ports base d) := by
  cases h with
  | nav move => exact nav move ports base
  | write => exact .write _ _ _
  | writeValue => exact .write _ _ _

theorem metadata_trace {c d : Auxiliary.Metadata.Cursor κ β}
    {reads : List (Auxiliary.NodeRecord κ β)} {cost : Nat}
    (h : Auxiliary.Metadata.Trace c reads d cost)
    (ports : Nat → Source α (Auxiliary.NodeRecord κ β)) (base : Nat) :
    SourcePointer.Trace (cursor ports base c) reads (cursor ports base d) cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (metadata_step move ports base) ih
  | @read c d entry reads cost atRecord rest ih =>
    have he : (cursor ports base c).focus.rootRecord = entry := by
      rcases c with ⟨focus,ancestors⟩
      cases focus with
      | empty => contradiction
      | node l record r => exact Option.some.inj atRecord
    simpa only [he] using SourcePointer.Trace.read ih

end ChaCha.Paper20261030.GapSource
