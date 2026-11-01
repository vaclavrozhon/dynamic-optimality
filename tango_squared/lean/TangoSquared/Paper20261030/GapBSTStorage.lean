import TangoSquared.Paper20261030.GapBSTRepresentation
import TangoSquared.Paper20261030.MetadataPointer
import TangoSquared.Paper20261030.SourcePayloadCapacity

/-! The appendix's actual metadata layout in the existing decorated BST.
Each physical vertex has one internal-record slot and two leaf slots.
A logical leaf cursor is represented by its parent and a slot flag.
The extra maximum-key root also handles the singleton tree. -/

namespace TangoSquared.Paper20261030.GapBST.Storage

open ColoredStorage
open Auxiliary (NodeRecord)

variable {α ρ : Type*}

structure Slots (ρ : Type*) where
  internal : Option ρ
  left : Option ρ
  right : Option ρ

def Slots.values (slots : Slots ρ) : List ρ :=
  slots.internal.toList ++ slots.left.toList ++ slots.right.toList

def record (key : α) (slots : Slots ρ) : NodeRecord α (fun _ => Slots ρ) := (0,⟨key,slots⟩)

def leafRecord : Source α ρ → Option ρ
  | .leaf _ value => some value
  | .fork _ _ _ => none

def gaps : Source α ρ → MTR.Tree (NodeRecord α (fun _ => Slots ρ))
  | .leaf _ _ => .empty
  | .fork value left right => .node (gaps left)
      (record (lastKey left) ⟨some value,leafRecord left,leafRecord right⟩) (gaps right)

def encode (source : Source α ρ) : MTR.Tree (NodeRecord α (fun _ => Slots ρ)) :=
  .node (gaps source) (record (lastKey source) ⟨none,leafRecord source,none⟩) .empty

theorem forget_gaps (source : Source α ρ) : Auxiliary.Metadata.forgetTree (gaps source) = GapBST.gaps source := by
  induction source <;> simp [gaps,GapBST.gaps,Auxiliary.Metadata.forgetTree,record, *]

theorem forget_encode (source : Source α ρ) : Auxiliary.Metadata.forgetTree (encode source) = GapBST.encode source := by
  simp only [encode,GapBST.encode,Auxiliary.Metadata.forgetTree,forget_gaps,record]

def frames (last : α) (slot : Option ρ) : List (SourcePointer.Frame α ρ) →
    List (MTR.Pointer.Frame (NodeRecord α (fun _ => Slots ρ)))
  | [] => [.left (record last ⟨none,slot,none⟩) .empty]
  | .left value right :: rest =>
      .left (record last ⟨some value,slot,leafRecord right⟩) (gaps right) :: frames (lastKey right) none rest
  | .right left value :: rest =>
      .right (gaps left) (record (lastKey left) ⟨some value,leafRecord left,slot⟩) :: frames last none rest

def cursor (logical : SourcePointer.Cursor α ρ) : Auxiliary.Metadata.Cursor α (fun _ => Slots ρ) :=
  park (gaps logical.focus) (frames (lastKey logical.focus) (leafRecord logical.focus) logical.ancestors)

theorem frames_tree (focus : Source α ρ) (rest : List (SourcePointer.Frame α ρ)) :
    MTR.Pointer.plug (gaps focus) (frames (lastKey focus) (leafRecord focus) rest) = encode (SourcePointer.plug focus rest) := by
  induction rest generalizing focus with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | left value right => exact ih (.fork value focus right)
    | right left value => exact ih (.fork value left focus)

theorem cursor_tree (logical : SourcePointer.Cursor α ρ) : (cursor logical).tree = encode logical.tree :=
  (park_tree _ _).trans (frames_tree _ _)

def readSlot (logical : SourcePointer.Cursor α ρ) : Slots ρ → Option ρ :=
  match logical.focus with
  | .fork _ _ _ => Slots.internal
  | .leaf _ _ => match logical.ancestors with
    | .right _ _ :: _ => Slots.right
    | _ => Slots.left

theorem cursor_record (logical : SourcePointer.Cursor α ρ) :
    ∃ entry, (cursor logical).focus.rootKey = some entry ∧
      readSlot logical entry.2.2 = some logical.focus.rootRecord := by
  rcases logical with ⟨focus,rest⟩
  cases focus with
  | fork value left right => exact ⟨_,rfl,rfl⟩
  | leaf key value =>
    cases rest with
    | nil => exact ⟨_,rfl,rfl⟩
    | cons first rest => cases first <;> exact ⟨_,rfl,rfl⟩

theorem readSlot_mem {logical : SourcePointer.Cursor α ρ} {slots : Slots ρ} {value : ρ}
    (present : readSlot logical slots = some value) : value ∈ slots.values := by
  rcases logical with ⟨focus,rest⟩
  cases focus with
  | fork => simp only [readSlot] at present; simp [Slots.values,present]
  | leaf =>
    cases rest with
    | nil => simp only [readSlot] at present; simp [Slots.values,present]
    | cons first rest => cases first <;> simp only [readSlot] at present <;> simp [Slots.values,present]

/-- Three slots are the entire physical payload. Each nonempty slot
contains one of the original source records, rather than a source subtree. -/
theorem slots_size (slots : Slots ρ) : slots.values.length ≤ 3 := by
  rcases slots with ⟨internal,left,right⟩
  cases internal <;> cases left <;> cases right <;> simp [Slots.values]

def Bounded (capacity : Nat) : MTR.Tree (NodeRecord α (fun _ => Slots (List ρ))) → Prop
  | .empty => True
  | .node left entry right =>
      (entry.2.2.values.flatten).length ≤ 3*capacity ∧ Bounded capacity left ∧ Bounded capacity right

theorem leafRecord_bound {source : Source α (List ρ)} {capacity : Nat} (bounded : source.Bounded capacity) :
    ((leafRecord source).toList.flatten).length ≤ capacity := by
  cases source with
  | leaf => simpa [leafRecord,Source.rootRecord] using bounded.root
  | fork => exact Nat.zero_le _

theorem gaps_bounded {source : Source α (List ρ)} {capacity : Nat} (bounded : source.Bounded capacity) :
    Bounded capacity (gaps source) := by
  induction source with
  | leaf => trivial
  | fork value left right ihl ihr =>
    refine ⟨?_,ihl bounded.2.1,ihr bounded.2.2⟩
    have root := bounded.root
    have l := leafRecord_bound bounded.2.1
    have r := leafRecord_bound bounded.2.2
    change value.length ≤ capacity at root
    change (Slots.values ⟨some value,leafRecord left,leafRecord right⟩).flatten.length ≤ _
    simp only [Slots.values,Option.toList_some,List.flatten_append,List.flatten_cons,
      List.flatten_nil,List.append_nil,List.length_append]
    omega

theorem encode_bounded {source : Source α (List ρ)} {capacity : Nat} (bounded : source.Bounded capacity) :
    Bounded capacity (encode source) := by
  refine ⟨?_,gaps_bounded bounded,True.intro⟩
  have leaf := leafRecord_bound bounded
  simpa only [encode,record,Slots.values,Option.toList,List.nil_append,List.append_nil] using
    leaf.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 3))

end TangoSquared.Paper20261030.GapBST.Storage
