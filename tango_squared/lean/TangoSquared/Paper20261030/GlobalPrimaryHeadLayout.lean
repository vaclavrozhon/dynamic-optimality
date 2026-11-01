import TangoSquared.Paper20261030.GlobalPrimaryOccurrences

set_option autoImplicit false

/-! The concrete output payload equations of a head program suffice to
rebuild the nested primary layout. The active boundary receives the new
dormant assembly; all other real ports retain their old prefix or incoming
tail payload, and the two virtual bottom payloads retain their original
keys. Unchanged endpoint descriptions are framed by primary geometry. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent
open BoundaryObservations PathDecomposition PreferredProjection PrimaryWings Secondary SecondaryDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

theorem Nested.head_payload_outputs {height d : Nat} (reference : DepthTree 0 height)
    {headerKey : Nat} {rank : α → Int} {x : α} {before after old incoming : PrefRouter α}
    (perfect : before.Perfect height) (distinct : before.leaves.Nodup)
    (step : PrefRouter.HeadStep x d before after) (memory : MemoryKey → Bool)
    (data : α → ComponentData α η) (nested : Nested headerKey rank before data)
    (common : List (Exit α)) (side : Bool) (depthEq : common.length = d)
    (oldEndpoint : old.terminal = before.terminal) (incomingEndpoint : incoming.terminal = after.terminal)
    (beforeWord : exits before = common ++ ⟨side,incoming⟩ :: exits old)
    (afterWord : exits after = common ++ ⟨!side,old⟩ :: exits incoming)
    (dormant active : ComponentData α η)
    (logical : LogicalInvariant reference after (step.perfect perfect) (advanceDepth before x d memory)
      (Function.update (Function.update data before.terminal dormant) after.terminal active))
    (activeCanonical : Canonical headerKey active (PackedPrimary.color 0 after) (rank after.terminal) 0)
    (dormantCanonical : Canonical headerKey dormant (PackedPrimary.color (d+1) old) (rank before.terminal) (d+1))
    (boundary : active.payload (PackedPrimary.color 0 after d) d = dormant.config.tree)
    (dormantFrame : ∀ wing key, key ≠ d → dormant.payload (some wing) key =
      (data before.terminal).payload (some wing) key)
    (activeFrame : ∀ wing key, key ∈ active.decorated.shape.leaves →
      PackedPrimary.color 0 after key = some wing → key ≠ d →
      active.payload (some wing) key =
        if key < d then (data before.terminal).payload (some wing) key
        else (data after.terminal).payload (some wing) key)
    (activeBottom : active.payload none headerKey = (data after.terminal).payload none headerKey)
    (dormantBottom : dormant.payload none headerKey = (data before.terminal).payload none headerKey) :
    Nested headerKey rank after
      (Function.update (Function.update data before.terminal dormant) after.terminal active) := by
  let fresh := Function.update (Function.update data before.terminal dormant) after.terminal active
  have endpoints := step.endpoints_ne distinct
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  have freshActive : fresh after.terminal = active := Function.update_self ..
  have freshDormant : fresh before.terminal = dormant := by
    simp only [fresh,Function.update_of_ne endpoints,Function.update_self]
  have incomingRoot : ComponentRoot before (d+1) incoming := by
    have found : portAt 0 (exits before) d = some ⟨side,incoming⟩ := by
      rw [beforeWord,← depthEq,portAt_boundary]
    simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot before 0 before) found
  have oldRoot : ComponentRoot after (d+1) old := by
    have found : portAt 0 (exits after) d = some ⟨!side,old⟩ := by
      rw [afterWord,← depthEq,portAt_boundary]
    simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot after 0 after) found
  have activeView : Canonical headerKey (fresh after.terminal) (PackedPrimary.color 0 after) (rank after.terminal) 0 := by
    rw [freshActive]; exact activeCanonical
  apply nested.head_update step distinct oldRoot oldEndpoint dormant active
  · change ComponentLayout headerKey rank fresh 0 after
    constructor
    · exact activeView
    · intro key exit present
      rw [freshActive,Nat.zero_add]
      have color : PackedPrimary.color 0 after key = some exit.leftOfEndpoint := by
        simp only [PackedPrimary.color,present,Option.map_some]
      by_cases atBoundary : key = d
      · subst key
        have found := present
        rw [afterWord,← depthEq,portAt_boundary] at found
        cases Option.some.inj found
        rw [oldEndpoint,freshDormant]
        rw [color] at boundary
        exact boundary
      · have childRoot : ComponentRoot after (key+1) exit.subtree := by
          simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot after 0 after) present
        have notNew : exit.subtree.terminal ≠ after.terminal := by
          intro same
          have impossible := (childRoot.eq_root_of_terminal afterDistinct same).1
          omega
        have notOld : exit.subtree.terminal ≠ before.terminal := by
          intro same
          have impossible := (childRoot.endpoint_unique oldRoot afterDistinct (same.trans oldEndpoint.symm)).1
          omega
        have childSame : fresh exit.subtree.terminal = data exit.subtree.terminal :=
          head_data_untouched data before.terminal after.terminal exit.subtree.terminal dormant active notOld notNew
        rw [childSame]
        have member : key ∈ active.decorated.shape.leaves := by
          have actual := activeView.port_mem reference (step.perfect perfect) afterDistinct
            (advanceDepth before x d memory) fresh logical (.root : ComponentRoot after 0 after) present
          simpa only [freshActive,Nat.zero_add] using actual
        rw [activeFrame exit.leftOfEndpoint key member color atBoundary]
        by_cases isPrefix : key < d
        · rw [if_pos isPrefix]
          have beforeFound : portAt 0 (exits before) key = some exit := by
            rw [afterWord,portAt_prefix common _ key (by omega)] at present
            rw [beforeWord,portAt_prefix common _ key (by omega)]
            exact present
          simpa only [Nat.zero_add] using nested.child (.root : ComponentRoot before 0 before) beforeFound
        · rw [if_neg isPrefix]
          have localFound : portAt 0 (exits incoming) (key-(d+1)) = some exit := by
            rw [afterWord,portAt_tail common _ _ _ (by omega),depthEq] at present
            simpa only [portAt,show d+1 ≤ key by omega,if_true,Nat.zero_le,Nat.sub_zero] using present
          have attached := nested.child incomingRoot localFound
          simpa only [incomingEndpoint,Nat.add_sub_of_le (show d+1 ≤ key by omega)] using attached
    · rw [freshActive,activeBottom,← incomingEndpoint]
      exact nested.bottom incomingRoot
  · change ComponentLayout headerKey rank fresh (d+1) old
    constructor
    · rw [oldEndpoint,freshDormant]
      exact dormantCanonical
    · intro localDepth exit present
      rw [oldEndpoint,freshDormant]
      have childRoot := oldRoot.child present
      have notNew : exit.subtree.terminal ≠ after.terminal := by
        intro same
        have impossible := (childRoot.eq_root_of_terminal afterDistinct same).1
        omega
      have notOld : exit.subtree.terminal ≠ before.terminal := by
        intro same
        have impossible := (childRoot.endpoint_unique oldRoot afterDistinct (same.trans oldEndpoint.symm)).1
        omega
      have childSame : fresh exit.subtree.terminal = data exit.subtree.terminal :=
        head_data_untouched data before.terminal after.terminal exit.subtree.terminal dormant active notOld notNew
      rw [childSame,dormantFrame exit.leftOfEndpoint (d+1+localDepth) (by omega)]
      have beforeFound : portAt 0 (exits before) (d+1+localDepth) = some exit := by
        rw [beforeWord,portAt_tail common _ _ _ (by omega),depthEq,portAt_shift]
        exact present
      simpa only [Nat.zero_add] using nested.child (.root : ComponentRoot before 0 before) beforeFound
    · rw [oldEndpoint,freshDormant,dormantBottom]
      exact nested.bottom (.root : ComponentRoot before 0 before)

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
