import ChaCha.Paper20261030.LocalComponentCompiler
import ChaCha.Paper20261030.PrimaryHeaderProgram
import ChaCha.Paper20261030.StructuralReadiness
import ChaCha.Paper20261030.HeadRootBoundaryMetadata

/-! Computing a primary header from a reached logical root record.
The cached identifier and both wing-presence bits come from that record's
identifier and color mask. During a head switch the active header inherits
the incoming bottom and the old start; the dormant header inherits the old
bottom and incoming start. Physical installation and later balanced-root
refresh are separate charged operations.
-/

namespace ChaCha.Paper20261030.PrimaryHeaderController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler

variable {α β ρ ι η : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def fromRoot (bottom : Int) (start : Nat) (record : LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) : Header η :=
  ⟨bottom,start,record.1.1,decide (some true ∈ record.2.colors),decide (some false ∈ record.2.colors)⟩

theorem real_presence (source : Source α (η × ρ)) (color : α → Option Bool)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none source,[]⟩ (erase forest))
    (orientation : Option Bool → Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (side : Bool) :
    (representation none orientation headerKey payload forest (some side)).isSome =
      decide (some side ∈ source.support color) := by
  have atColor := represented (some side)
  cases present : forest (some side) with
  | none =>
    have absent : some side ∉ source.support color := by
      simpa only [erase,present,Option.map_none,ProjectionForest.RepresentsAt,Cursor.tree,plug,annotate_support] using atColor
    simp only [representation,PayloadForestController.transform,VirtualHeaderController.encode,
      reduceCtorEq,if_false,ForestMirrorController.transform,encode,present,Option.map_none,
      Option.isSome_none,absent,decide_false]
  | some current =>
    simp only [erase,present,Option.map_some,ProjectionForest.RepresentsAt] at atColor
    have packed : ColoredStorage.packed color (some side) (annotate Prod.fst color none source) =
        some (current.mapRecords Prod.snd).tree := atColor.1
    have member : some side ∈ source.support color := by
      by_contra absent
      have notPacked := (packed_none_iff color (some side) (annotate Prod.fst color none source)).mpr
        (by simpa only [annotate_support] using absent)
      rw [notPacked] at packed
      contradiction
    simp only [representation,PayloadForestController.transform,VirtualHeaderController.encode,
      reduceCtorEq,if_false,ForestMirrorController.transform,encode,present,Option.map_some,
      Option.isSome_some,member,decide_true]

theorem fromRoot_correct (bottom : Int) (start : Nat) (source : Source α (η × ρ)) (color : α → Option Bool)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none source,[]⟩ (erase forest))
    (orientation : Option Bool → Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool))))) :
    let header := fromRoot bottom start (annotate Prod.fst color none source).rootRecord
    header.bottom = bottom ∧ header.start = start ∧ header.rootId = source.rootRecord.1 ∧
      header.leftWing = (representation none orientation headerKey payload forest (some true)).isSome ∧
      header.rightWing = (representation none orientation headerKey payload forest (some false)).isSome := by
  simp only [fromRoot,annotate_root,fields]
  exact ⟨trivial,trivial,trivial,(real_presence source color forest represented orientation headerKey payload true).symm,
    (real_presence source color forest represented orientation headerKey payload false).symm⟩

def switched (old incoming : Header η) (records : HeadBoundary.Records (η × ρ) η (Option Bool)) : Header η × Header η :=
  (fromRoot incoming.bottom old.start records.low,fromRoot old.bottom incoming.start records.oldHigh)

def switchedRoot (old incoming : Header η) (records : HeadBoundary.RootRecords (η × ρ) η) : Header η × Header η :=
  (fromRoot incoming.bottom old.start records.incomingHigh,fromRoot old.bottom incoming.start records.oldHigh)

theorem switched_roles (old incoming : Header η) (records : HeadBoundary.Records (η × ρ) η (Option Bool)) :
    (switched old incoming records).1.bottom = incoming.bottom ∧
      (switched old incoming records).1.start = old.start ∧
      (switched old incoming records).2.bottom = old.bottom ∧
      (switched old incoming records).2.start = incoming.start := ⟨rfl,rfl,rfl,rfl⟩

end ChaCha.Paper20261030.PrimaryHeaderController
