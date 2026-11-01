import TangoSquared.Paper20261030.SourcePayloadCapacity

/-! Mapping record payloads preserves routing and every charged instruction. -/

namespace TangoSquared.Paper20261030.ColoredStorage

variable {α ρ τ : Type*}

def Source.mapRecords (f : ρ → τ) : Source α ρ → Source α τ
  | .leaf key record => .leaf key (f record)
  | .fork record l r => .fork (f record) (l.mapRecords f) (r.mapRecords f)

theorem Source.mapRecords_root (f : ρ → τ) (source : Source α ρ) :
    (source.mapRecords f).rootRecord = f source.rootRecord := by cases source <;> rfl

theorem Source.mapRecords_shape (f : ρ → τ) (source : Source α ρ) :
    (source.mapRecords f).shape = source.shape := by
  induction source <;> simp_all [mapRecords,Source.shape]

theorem Source.mapRecords_setRoot (f : ρ → τ) (source : Source α ρ) (fresh : ρ) :
    (source.setRoot fresh).mapRecords f = (source.mapRecords f).setRoot (f fresh) := by cases source <;> rfl

theorem Source.Bounded.mapRecords (f : ρ → τ) {source : Source α (List ρ)} {capacity : Nat}
    (bounded : source.Bounded capacity) : (source.mapRecords (List.map f)).Bounded capacity := by
  induction source with
  | leaf key records => simpa only [Source.Bounded,Source.mapRecords,Source.toStored,Stored.Bounded,List.length_map] using bounded
  | fork records l r ihl ihr => exact ⟨by simpa using bounded.1,ihl bounded.2.1,ihr bounded.2.2⟩

end TangoSquared.Paper20261030.ColoredStorage

namespace TangoSquared.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ τ : Type*}

def Frame.mapRecords (f : ρ → τ) : Frame α ρ → Frame α τ
  | .left record r => .left (f record) (r.mapRecords f)
  | .right l record => .right (l.mapRecords f) (f record)

def Cursor.mapRecords (f : ρ → τ) (cursor : Cursor α ρ) : Cursor α τ :=
  ⟨cursor.focus.mapRecords f,cursor.ancestors.map (Frame.mapRecords f)⟩

theorem Step.mapRecords (f : ρ → τ) {before after : Cursor α ρ} (instruction : Step before after) :
    Step (before.mapRecords f) (after.mapRecords f) := by
  cases instruction
  · exact .left _ _ _ _
  · exact .right _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _
  · simpa only [Cursor.mapRecords,Source.mapRecords_setRoot] using Step.write _ _ _

theorem Trace.mapRecords (f : ρ → τ) {before after : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (execution : Trace before reads after cost) :
    Trace (before.mapRecords f) (reads.map f) (after.mapRecords f) cost := by
  induction execution with
  | nil => exact .nil _
  | step instruction rest ih => exact .step (instruction.mapRecords f) ih
  | read rest ih => simpa only [List.map_cons,Cursor.mapRecords,Source.mapRecords_root] using Trace.read ih

theorem Rearranges.mapRecords (f : ρ → τ) {before after : Source α ρ} {budget : Nat}
    (execution : Rearranges before after budget) : Rearranges (before.mapRecords f) (after.mapRecords f) budget := by
  intro outside
  obtain ⟨reads,cost,trace,bounded⟩ := execution []
  exact ⟨reads.map f,cost,(trace.mapRecords f).extend outside,bounded⟩

end TangoSquared.Paper20261030.SourcePointer
