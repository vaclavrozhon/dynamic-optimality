import TangoSquared.Paper20261030.PrimaryHeaderRefresh
import TangoSquared.Paper20261030.SourceLocatedAddress
import TangoSquared.Paper20261030.ThreeColorConfiguration
import TangoSquared.Paper20261030.MultiSourceMask

/-! The cache-repair route is computed from the two loaded wing bits.
Its position hypotheses follow from the actual three-piece component
configuration, even when inactive physical registers are merely masked.
No stored value at the final root is assumed: the controller reinstalls
the previously loaded header with the new logical root identifier.
-/

namespace TangoSquared.Paper20261030.PrimaryHeaderRefresh

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram PrimaryHeaderController
open ForestConnector.ThreeColors

variable {α ρ η : Type*}

def path (header : Header η) : List Bool :=
  (if header.rightWing then [false] else []) ++ (if header.leftWing then [true] else [])

theorem path_length (header : Header η) : (path header).length ≤ 2 := by
  cases hl : header.leftWing <;> cases hr : header.rightWing <;> simp [path,hl,hr]

theorem component_refresh (header : Header η) (freshId : η)
    (forest : ProjectionForest.State (Option Bool) α ρ) (headerTree : Source α (List ρ))
    (leftWing : header.leftWing = (forest (some true)).isSome)
    (rightWing : header.rightWing = (forest (some false)).isSome)
    (active : Option Bool → Bool) (config : Configuration (Option Bool) α (Record (List ρ) η))
    (represented : (config.mask active).mapRecords Prod.fst = configuration forest ⟨headerTree,[]⟩)
    (valid : WellFormed config) :
    ∃ target reads cost,
      Run (program none header freshId (path header)) (some (RootRecordTour.ascend (path header).length)) config
        (some .done) target reads cost ∧
      target.mapRecords Prod.fst = config.mapRecords Prod.fst ∧
      target.tree.rootRecord.2 = some {header with rootId := freshId} ∧
      WellFormed target ∧ cost ≤ 6 := by
  have pathEq : path header = headerPath forest := by simp only [path,headerPath,leftWing,rightWing]
  have finger := header_finger forest ⟨headerTree,[]⟩
  rw [← represented] at finger
  have masked : (config.mask active).fingers none = some (path header) := by
    simpa only [Configuration.mapRecords,address,List.reverse_nil,List.map_nil,List.append_nil,← pathEq] using finger
  have present := (mask_present active config none (path header) masked).2
  obtain ⟨outside,plainReached⟩ := header_atRoot forest headerTree
  rw [← represented,← pathEq] at plainReached
  obtain ⟨current,reached,_⟩ := lift_locate Prod.fst config.tree (path header) ⟨headerTree,outside⟩ plainReached
  exact refresh none header freshId (path header) (path_length header) config current present reached
    (locate_address config.tree (path header) current reached).symm valid

end TangoSquared.Paper20261030.PrimaryHeaderRefresh
