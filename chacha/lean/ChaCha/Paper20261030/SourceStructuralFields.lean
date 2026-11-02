import ChaCha.Paper20261030.SourceRecordInventory
import ChaCha.Paper20261030.SourceReversal

/-!
# Constant structural fields for source navigation and rotations

Each source record stores its parent's immutable identifier, its subtree's
color mask, and the identifiers and color masks of its at most two children.
A mask uses constantly many bits for the fixed color set. These fields
are annotations, separate from the application payload and its cache.

Changing the external parent changes only one reached record. An internal
rotation updates the two pivot records and the middle subtree's parent
field using at most thirteen charged source-pointer operations. Updating
the external parent's child field belongs to the cursor-context lift.
-/

namespace ChaCha.Paper20261030.Structural

open ColoredStorage SourcePointer

variable {α ρ ι C : Type*} [DecidableEq C]

structure Child (ι C : Type*) where
  id : ι
  colors : Finset C

structure Fields (ι C : Type*) where
  parent : Option ι
  colors : Finset C
  children : Option (Child ι C × Child ι C)

def descriptor (identifier : ρ → ι) (color : α → C) (source : Source α ρ) : Child ι C :=
  ⟨identifier source.rootRecord,source.support color⟩

def fields (identifier : ρ → ι) (color : α → C) (parent : Option ι) (source : Source α ρ) : Fields ι C :=
  ⟨parent,source.support color,match source with
    | .leaf _ _ => none
    | .fork _ l r => some (descriptor identifier color l,descriptor identifier color r)⟩

def annotate (identifier : ρ → ι) (color : α → C) (parent : Option ι) : Source α ρ → Source α (ρ × Fields ι C)
  | .leaf key record => .leaf key (record,fields identifier color parent (.leaf key record))
  | .fork record l r => .fork (record,fields identifier color parent (.fork record l r))
      (annotate identifier color (some (identifier record)) l)
      (annotate identifier color (some (identifier record)) r)

theorem annotate_root (identifier : ρ → ι) (color : α → C) (parent : Option ι) (source : Source α ρ) :
    (annotate identifier color parent source).rootRecord = (source.rootRecord,fields identifier color parent source) := by
  cases source <;> rfl

theorem annotate_shape (identifier : ρ → ι) (color : α → C) (parent : Option ι) (source : Source α ρ) :
    (annotate identifier color parent source).shape = source.shape := by
  induction source generalizing parent <;> simp_all [annotate,Source.shape]

theorem annotate_inventory (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (source : Source α ρ) {η : Type*} (observe : ρ → η) :
    (annotate identifier color parent source).inventory (fun record => observe record.1) = source.inventory observe := by
  induction source generalizing parent <;> simp_all [annotate]

theorem annotate_parent (identifier : ρ → ι) (color : α → C) (old fresh : Option ι) (source : Source α ρ) :
    annotate identifier color fresh source =
      (annotate identifier color old source).setRoot (source.rootRecord,fields identifier color fresh source) := by
  cases source <;> rfl

theorem change_parent (identifier : ρ → ι) (color : α → C) (old fresh : Option ι) (source : Source α ρ) :
    Rearranges (annotate identifier color old source) (annotate identifier color fresh source) 2 := by
  rw [annotate_parent identifier color old fresh source]
  exact replace_root _ _

theorem annotate_write (identifier : ρ → ι) (color : α → C) (parent : Option ι) (source : Source α ρ)
    (fresh : ρ) (sameId : identifier fresh = identifier source.rootRecord) :
    annotate identifier color parent (source.setRoot fresh) =
      (annotate identifier color parent source).setRoot (fresh,fields identifier color parent source) := by
  cases source <;> simp_all only [Source.setRoot,Source.rootRecord,annotate,fields,Source.support]

theorem write_payload (identifier : ρ → ι) (color : α → C) (parent : Option ι) (source : Source α ρ)
    (fresh : ρ) (sameId : identifier fresh = identifier source.rootRecord) :
    Rearranges (annotate identifier color parent source) (annotate identifier color parent (source.setRoot fresh)) 2 := by
  rw [annotate_write identifier color parent source fresh sameId]
  exact replace_root _ _

theorem rotate_right (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) :
    Rearranges (annotate identifier color parent (.fork q (.fork p u v) w))
      (annotate identifier color parent (.fork p u (.fork q v w))) 13 := by
  let U := annotate identifier color (some (identifier p)) u
  let V := annotate identifier color (some (identifier p)) v
  let W := annotate identifier color (some (identifier q)) w
  let oldP := (p,fields identifier color (some (identifier q)) (.fork p u v))
  let oldQ := (q,fields identifier color parent (.fork q (.fork p u v) w))
  let newP := (p,fields identifier color parent (.fork p u (.fork q v w)))
  let newQ := (q,fields identifier color (some (identifier p)) (.fork q v w))
  have rotation : Rearranges (.fork oldQ (.fork oldP U V) W) (.fork oldP U (.fork oldQ V W)) 1 := by
    intro rest
    exact ⟨[],1,.step (.rotateRight _ _ _ _ _ _) (.nil _),le_rfl⟩
  have middle := (change_parent identifier color (some (identifier p)) (some (identifier q)) v).left
    (r := W) (record := oldQ)
  have child := middle.trans (replace_root
    (.fork oldQ (annotate identifier color (some (identifier q)) v) W) newQ)
  have childAtRoot := child.right (l := U) (record := oldP)
  have finish := childAtRoot.trans (replace_root
    (.fork oldP U (.fork newQ (annotate identifier color (some (identifier q)) v) W)) newP)
  exact (rotation.trans finish).mono (by decide)

theorem rotate_left (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) :
    Rearranges (annotate identifier color parent (.fork p u (.fork q v w)))
      (annotate identifier color parent (.fork q (.fork p u v) w)) 13 :=
  (rotate_right identifier color parent u v w p q).symm

end ChaCha.Paper20261030.Structural
