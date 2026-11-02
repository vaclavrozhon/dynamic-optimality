import ChaCha.Paper20261030.MultiSourceFingerLabels
import ChaCha.Paper20261030.MultiSourceSingleCursor

set_option autoImplicit false

/-! Unique physical identifiers turn an unchanged parked label into an
actual cursor representation. The locator and paths in these proofs are
ghost witnesses; no identifier lookup is added to the running program. -/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer

variable {α ρ ι : Type*}

theorem recordAt_mem_inventory (tree : Source α ρ) (position : List Bool) (record : ρ)
    (found : recordAt tree position = some record) : record ∈ tree.inventory id := by
  induction tree generalizing position with
  | leaf key value =>
    cases position with
    | nil => cases Option.some.inj found; simp [Source.rootRecord]
    | cons => cases found
  | fork value left right ihl ihr =>
    cases position with
    | nil => cases Option.some.inj found; simp [Source.rootRecord]
    | cons side rest =>
      rw [Source.inventory_fork]
      cases side with
      | false => exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr (ihl rest found))))
      | true => exact Multiset.mem_add.mpr (Or.inr (ihr rest found))

theorem recordAt_unique (tree : Source α ρ) (unique : (tree.inventory id).Nodup)
    (first second : List Bool) (record : ρ)
    (atFirst : recordAt tree first = some record) (atSecond : recordAt tree second = some record) :
    first = second := by
  induction tree generalizing first second with
  | leaf key value =>
    cases first with
    | cons => cases atFirst
    | nil => cases second with
      | cons => cases atSecond
      | nil => rfl
  | fork value left right ihl ihr =>
    have parts : value ∉ left.inventory id + right.inventory id ∧
        (left.inventory id).Nodup ∧ (right.inventory id).Nodup ∧
        Disjoint (left.inventory id) (right.inventory id) := by
      rw [Source.inventory_fork,add_assoc] at unique
      simpa only [id_eq,Multiset.singleton_add,
        Multiset.nodup_cons,Multiset.nodup_add] using unique
    have different : ∀ position, recordAt left position = some value → False :=
      fun position found => parts.1 (Multiset.mem_add.mpr (Or.inl (recordAt_mem_inventory left position value found)))
    have differentRight : ∀ position, recordAt right position = some value → False :=
      fun position found => parts.1 (Multiset.mem_add.mpr (Or.inr (recordAt_mem_inventory right position value found)))
    cases first with
    | nil =>
      change some value = some record at atFirst
      cases Option.some.inj atFirst
      cases second with
      | nil => rfl
      | cons side rest =>
        cases side
        · exact False.elim (different rest atSecond)
        · exact False.elim (differentRight rest atSecond)
    | cons side rest =>
      cases second with
      | nil =>
        change some value = some record at atSecond
        cases Option.some.inj atSecond
        cases side
        · exact False.elim (different rest atFirst)
        · exact False.elim (differentRight rest atFirst)
      | cons other tail =>
        cases side <;> cases other
        · exact congrArg (List.cons false) (ihl parts.2.1 rest tail atFirst atSecond)
        · exact False.elim (Multiset.disjoint_left.mp parts.2.2.2
            (recordAt_mem_inventory left rest record atFirst) (recordAt_mem_inventory right tail record atSecond))
        · exact False.elim (Multiset.disjoint_left.mp parts.2.2.2
            (recordAt_mem_inventory left tail record atSecond) (recordAt_mem_inventory right rest record atFirst))
        · exact congrArg (List.cons true) (ihr parts.2.2.1 rest tail atFirst atSecond)

theorem recordAt_label_unique (label : ρ → ι) (tree : Source α ρ) (unique : (tree.inventory label).Nodup)
    (first second : List Bool) (identifier : ι)
    (atFirst : (recordAt tree first).map label = some identifier)
    (atSecond : (recordAt tree second).map label = some identifier) : first = second := by
  refine recordAt_unique (tree.mapRecords label) ?_ first second identifier ?_ ?_
  · simpa only [mapRecords_inventory,Function.comp_def,id_eq] using unique
  · rw [MultiSourceProgram.recordAt_map]
    exact atFirst
  · rw [MultiSourceProgram.recordAt_map]
    exact atSecond

theorem cursors_eq_of_label (label : ρ → ι) (before after : Cursor α ρ)
    (tree : before.tree = after.tree) (unique : (before.tree.inventory label).Nodup)
    (same : label before.focus.rootRecord = label after.focus.rootRecord) : before = after := by
  apply eq_of_tree_address before after tree
  apply recordAt_label_unique label before.tree unique (address before) (address after)
    (label before.focus.rootRecord)
  · rw [← locate_record,locate_cursor]
    rfl
  · rw [tree,← locate_record,locate_cursor,Option.map_some,Option.map_some,same]

end ChaCha.Paper20261030.SourcePositions

namespace ChaCha.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions

variable {α ρ ι F : Type*} [DecidableEq F]

theorem fingerLabel_of_represents (label : ρ → ι) (config : Configuration F α ρ) (finger : F)
    (current : Cursor α ρ) (represented : MultiSourceSingleCursor.Represents finger current config) :
    fingerLabel label config finger = some (label current.focus.rootRecord) := by
  simp only [fingerLabel,represented.2,Option.bind_some,represented.1,← locate_record,locate_cursor,Option.map_some]

theorem represents_of_fingerLabel (label : ρ → ι) (config : Configuration F α ρ) (finger : F)
    (current : Cursor α ρ) (tree : current.tree = config.tree) (unique : (config.tree.inventory label).Nodup)
    (identity : fingerLabel label config finger = some (label current.focus.rootRecord)) :
    MultiSourceSingleCursor.Represents finger current config := by
  refine ⟨tree.symm,?_⟩
  unfold fingerLabel at identity
  cases atFinger : config.fingers finger with
  | none => simp only [atFinger,Option.bind_none,reduceCtorEq] at identity
  | some position =>
    simp only [atFinger,Option.bind_some] at identity
    have located : (recordAt config.tree (address current)).map label = some (label current.focus.rootRecord) := by
      rw [← tree,← locate_record,locate_cursor]
      rfl
    exact congrArg some (recordAt_label_unique label config.tree unique position (address current) _ identity located)

end ChaCha.Paper20261030.MultiSourceProgram
