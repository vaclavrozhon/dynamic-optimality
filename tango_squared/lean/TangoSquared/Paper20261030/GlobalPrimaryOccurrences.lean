import TangoSquared.Paper20261030.GlobalPrimaryLayout
import TangoSquared.Paper20261030.EnclosingPayloadOccurrence

set_option autoImplicit false

/-! Every endpoint assembly occurs in the actual nested packet tree.
These are ghost subtree witnesses obtained recursively from the canonical
forest representation. They do not install fingers or perform uncharged
identifier searches. A separate metadata frame transports the stored
root cache to such an occurrence after a local operation. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent
open BoundaryObservations PathDecomposition PreferredProjection PrimaryWings Secondary SecondaryDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

def ErasedOccurrence (data : ComponentData α η) (whole : Source α (Packet η)) : Prop :=
  ∃ saved : Packet η, ∃ outside : List (Frame α (Packet η)),
    whole = plug (data.config.tree.setRoot (saved ++ data.config.tree.rootRecord)) outside

theorem Canonical.port_mem {height start depth : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} {exit : Exit α} (perfect : whole.Perfect height)
    (distinct : whole.leaves.Nodup) (memory : MemoryKey → Bool) (data : α → ComponentData α η)
    (valid : LogicalInvariant reference whole perfect memory data)
    (rooted : ComponentRoot whole start subtree) {headerKey : Nat} {rank : α → Int}
    (canonical : Canonical headerKey (data subtree.terminal) (PackedPrimary.color start subtree)
      (rank subtree.terminal) start) (present : portAt 0 (exits subtree) depth = some exit) :
    start+depth ∈ (data subtree.terminal).decorated.shape.leaves := by
  have input := valid.represented.input reference perfect distinct memory (components data) rooted
  rw [rooted.endpoint_start distinct] at input
  simp only [components] at input
  have shape := congrArg (fun tree : Source Nat Cached => tree.shape.leaves) canonical.erases
  simp only [Source.mapRecords_shape] at shape
  rw [shape]
  have bound : depth < (exits subtree).length :=
    (List.getElem?_eq_some_iff.mp (by simpa [portAt] using present)).1
  have inRange : start+depth ∈ List.range' start ((exits subtree).length+1) := by
    apply List.mem_range'.mpr
    exact ⟨depth,by omega,by omega⟩
  rcases input with full | ⟨_,suffix⟩
  · rw [full]; exact inRange
  · rw [suffix]; exact List.mem_cons_of_mem _ inRange

theorem Nested.erased_occurs {height start : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} (perfect : whole.Perfect height) (distinct : whole.leaves.Nodup)
    (memory : MemoryKey → Bool) (data : α → ComponentData α η)
    (valid : LogicalInvariant reference whole perfect memory data) {headerKey : Nat} {rank : α → Int}
    (nested : Nested headerKey rank whole data) (rooted : ComponentRoot whole start subtree) :
    ErasedOccurrence (data subtree.terminal) (data whole.terminal).config.tree := by
  induction rooted with
  | root =>
    refine ⟨[],[],?_⟩
    simp only [List.nil_append,plug]
    cases (data whole.terminal).config.tree <;> rfl
  | @child start depth parent exit rooted present ih =>
    obtain ⟨saved,outside,outer⟩ := ih
    have canonical := nested.canonical rooted
    have member := canonical.port_mem reference perfect distinct memory data valid rooted present
    have atDepth : portAt start (exits parent) (start+depth) = some exit := by
      rw [portAt_shift]; exact present
    have color : PackedPrimary.color start parent (start+depth) = some exit.leftOfEndpoint := by
      simp only [PackedPrimary.color,atDepth,Option.map_some]
    obtain ⟨records,_,inside,proper,view⟩ := LocalComponentCompiler.real_payload_occurs
      (PackedPrimary.color start parent) (data parent.terminal).decorated (data parent.terminal).forest
      canonical.forestRep headerKey (data parent.terminal).payload (data parent.terminal).config
      canonical.assembled (start+depth) member (by rw [color]; exact Option.some_ne_none _)
    rw [color,nested.child rooted present] at view
    let child := (data exit.subtree.terminal).config.tree.setRoot
      (records.map some ++ none::(data exit.subtree.terminal).config.tree.rootRecord)
    obtain ⟨changed,_,change⟩ := proper_subtree_setRoot child inside proper
      (saved ++ (data parent.terminal).config.tree.rootRecord)
    have changedFocus := (congrArg (fun tree : Source α (Packet η) =>
      tree.setRoot (saved ++ (data parent.terminal).config.tree.rootRecord)) view).trans change
    refine ⟨records.map some ++ [none],changed ++ outside,?_⟩
    rw [outer,changedFocus,plug_append]
    simp only [child,List.append_assoc,List.singleton_append]

theorem StoredAt.erased_occurs (data : ComponentData α η) (current : Cursor α (Cell η))
    (stored : StoredAt data current) :
    ErasedOccurrence data ((current.tree.mapRecords Prod.fst).mapRecords Prod.snd) := by
  obtain ⟨saved,view⟩ := stored.2
  refine ⟨saved,(current.ancestors.map (Frame.mapRecords Prod.fst)).map (Frame.mapRecords Prod.snd),?_⟩
  simp only [Cursor.tree,← plug_mapRecords,view]

theorem Nested.proper_erased_occurs {height start : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} (perfect : whole.Perfect height) (distinct : whole.leaves.Nodup)
    (memory : MemoryKey → Bool) (data : α → ComponentData α η)
    (valid : LogicalInvariant reference whole perfect memory data) {headerKey : Nat} {rank : α → Int}
    (nested : Nested headerKey rank whole data) (rooted : ComponentRoot whole start subtree)
    (other : subtree.terminal ≠ whole.terminal) :
    ∃ saved : Packet η, ∃ outside : List (Frame α (Packet η)), outside ≠ [] ∧
      (data whole.terminal).config.tree =
        plug ((data subtree.terminal).config.tree.setRoot
          (saved ++ (data subtree.terminal).config.tree.rootRecord)) outside := by
  obtain ⟨saved,outside,occurrence⟩ := nested.erased_occurs reference perfect distinct memory data valid rooted
  refine ⟨saved,outside,?_,occurrence⟩
  intro empty
  rw [empty,plug] at occurrence
  have equal := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves.length) occurrence
  simp only [source_setRoot_shape] at equal
  rw [nested.original_keys reference perfect distinct memory data valid .root,
    nested.original_keys reference perfect distinct memory data valid rooted] at equal
  have smaller := rooted.proper_leaves_lt other
  omega

theorem Maintained.erased_occurs {F : Type*} [DecidableEq F] {height start : Nat}
    {markerId headerKey : Nat} {rank : α → Int} {reference : DepthTree 0 height}
    {primary subtree : PrefRouter α} {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {data : α → ComponentData α η} {shared : Configuration F α (Cell η)}
    (valid : Maintained markerId headerKey rank reference primary perfect memory data shared)
    (rooted : ComponentRoot primary start subtree) :
    ErasedOccurrence (data subtree.terminal) ((shared.tree.mapRecords Prod.fst).mapRecords Prod.snd) := by
  rw [valid.root]
  exact valid.nested.erased_occurs reference perfect valid.distinct memory data valid.logical rooted

theorem StoredAt.leaves (data : ComponentData α η) (current : Cursor α (Cell η))
    (stored : StoredAt data current) : current.focus.shape.leaves = data.config.tree.shape.leaves := by
  obtain ⟨saved,view⟩ := stored.2
  have leaves := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves) view
  simpa only [Source.mapRecords_shape,source_setRoot_shape] using leaves

/-- The cache asserted for the active component is at the physical root,
not merely at some unidentified occurrence elsewhere in the tree. -/
theorem Maintained.active_header {F : Type*} [DecidableEq F] {height : Nat}
    {markerId headerKey : Nat} {rank : α → Int} {reference : DepthTree 0 height}
    {primary : PrefRouter α} {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {data : α → ComponentData α η} {shared : Configuration F α (Cell η)}
    (valid : Maintained markerId headerKey rank reference primary perfect memory data shared) :
    shared.tree.rootRecord.2 = some (data primary.terminal).header := by
  obtain ⟨current,whole,stored⟩ := valid.stored (.root : ComponentRoot primary 0 primary)
  have focusLeaves := stored.leaves
  have treeLeaves := valid.nested.original_keys reference perfect valid.distinct memory data valid.logical
    (.root : ComponentRoot primary 0 primary)
  have sameLength : current.focus.shape.leaves.length = current.tree.shape.leaves.length := by
    rw [focusLeaves,treeLeaves,whole,valid.original_keys]
  have empty : current.ancestors = [] := by
    by_contra proper
    have smaller := SubtreeMetadata.proper_leaves_lt current.focus current.ancestors proper
    change current.focus.shape.leaves.length < current.tree.shape.leaves.length at smaller
    omega
  have focus : current.focus = shared.tree := by
    simpa only [Cursor.tree,empty,plug] using whole
  rw [← focus]
  exact stored.1

/-- Runtime readiness adds one actual register at the root. The table and
all other endpoint occurrences remain proof data. -/
structure Ready {F : Type*} [DecidableEq F] {height : Nat} (markerId headerKey : Nat)
    (rank : α → Int) (reference : DepthTree 0 height) (primary : PrefRouter α)
    (perfect : primary.Perfect height) (memory : MemoryKey → Bool) (data : α → ComponentData α η)
    (shared : Configuration F α (Cell η)) (entry : F) : Prop where
  maintained : Maintained markerId headerKey rank reference primary perfect memory data shared
  atRoot : shared.fingers entry = some []

theorem Ready.entry {F : Type*} [DecidableEq F] {height : Nat} {markerId headerKey : Nat}
    {rank : α → Int} {reference : DepthTree 0 height} {primary : PrefRouter α}
    {perfect : primary.Perfect height} {memory : MemoryKey → Bool} {data : α → ComponentData α η}
    {shared : Configuration F α (Cell η)} {entry : F}
    (ready : Ready markerId headerKey rank reference primary perfect memory data shared entry) :
    MultiSourceSingleCursor.Represents entry ⟨shared.tree,[]⟩ shared ∧
      StoredAt (data primary.terminal) ⟨shared.tree,[]⟩ := by
  refine ⟨⟨rfl,ready.atRoot⟩,ready.maintained.active_header,[],?_⟩
  rw [ready.maintained.root]
  simp only [List.nil_append]
  cases (data primary.terminal).config.tree <;> rfl

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
