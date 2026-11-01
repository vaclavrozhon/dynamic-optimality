import Splay.Accounting.InternalPairingFraction
import Splay.Accounting.RootHeavyPathPairingGeometry

namespace Splay.Accounting

open Splay.Lazy

/-- Equality flags of consecutive two-cell double groups. -/
def sameSideDoubleFlags : List Side → List Bool
  | first :: second :: sides =>
      decide (first = second) :: sameSideDoubleFlags sides
  | _ => []

/-- The same Boolean flags read from a splay kind transcript. -/
def doubleStepFlags : List SplayStepKind → List Bool
  | .zigZig :: kinds => true :: doubleStepFlags kinds
  | .zigZag :: kinds => false :: doubleStepFlags kinds
  | .zig :: _ => []
  | [] => []

/-- The exact side schedule identifies precisely the genuine zig-zigs. -/
theorem HitSideSchedule.doubleStepFlags_eq_sameSideDoubleFlags
    {kinds : List SplayStepKind} {sides : List Side}
    (schedule : HitSideSchedule kinds sides) :
    doubleStepFlags kinds = sameSideDoubleFlags sides := by
  induction schedule with
  | done => rfl
  | zig => rfl
  | zigZig tail ih =>
      simp [doubleStepFlags, sameSideDoubleFlags, ih]
  | zigZag opposite tail ih =>
      simp [doubleStepFlags, sameSideDoubleFlags, ih, opposite]

/-- Even positions of the duplicated list recover the original cell side. -/
theorem getElem?_duplicateHitSides_even (sides : List Side) (index : ℕ) :
    (duplicateHitSides sides)[2 * index]? = sides[index]? := by
  induction sides generalizing index with
  | nil =>
      simp [duplicateHitSides]
  | cons side sides ih =>
      cases index with
      | zero => simp [duplicateHitSides]
      | succ index =>
          simpa [duplicateHitSides, Nat.mul_succ] using ih index

/--
If both cells of a fixed double group have the same side, its equality flag
is `true`.
-/
theorem sameSideDoubleFlags_getElem?_eq_true
    (sides : List Side) (group : ℕ) (side : Side)
    (first : sides[2 * group]? = some side)
    (second : sides[2 * group + 1]? = some side) :
    (sameSideDoubleFlags sides)[group]? = some true := by
  induction sides using List.twoStepInduction generalizing group side with
  | nil =>
      simp at first
  | singleton only =>
      cases group with
      | zero => simp at second
      | succ group => simp at first
  | cons_cons firstSide secondSide sides ih =>
      cases group with
      | zero =>
          simp at first second
          subst firstSide
          subst secondSide
          simp [sameSideDoubleFlags]
      | succ group =>
          apply ih (group := group) (side := side)
          · simpa [Nat.mul_succ] using first
          · have shifted :
                2 * group + 3 = (2 * group + 1) + 2 := by omega
            simpa [Nat.mul_succ, shifted] using second

/-- Every position of a half-open list interval carries one fixed side. -/
def UniformSideInterval (sides : List Side) (side : Side)
    (start length : ℕ) : Prop :=
  ∀ index, start ≤ index → index < start + length →
    sides[index]? = some side

/--
An explicit segment decomposition supplies the exact half-open uniform
interval needed by the manuscript's four-child grouping.
-/
theorem uniformSideInterval_of_decomposition
    {α : Type*} {inside whole front back : List α}
    (projectSide : α → Side) {side : Side}
    (decomposition : whole = front ++ inside ++ back)
    (sameSide : ∀ element ∈ inside, projectSide element = side) :
    UniformSideInterval
      (whole.map projectSide) side front.length inside.length := by
  intro index startLe indexLt
  have insideIndexLt : index - front.length < inside.length := by
    omega
  have mappedDecomposition :
      whole.map projectSide =
        front.map projectSide ++
          (inside.map projectSide ++ back.map projectSide) := by
    rw [decomposition]
    simp only [List.map_append, List.append_assoc]
  rw [mappedDecomposition]
  rw [List.getElem?_append_right (by simpa using startLe)]
  simp only [List.length_map]
  rw [List.getElem?_append_left (by simpa using insideIndexLt)]
  rw [List.getElem?_map, List.getElem?_eq_getElem insideIndexLt]
  simp only [Option.map_some]
  exact congrArg some
    (sameSide inside[index - front.length]
      (List.getElem_mem insideIndexLt))

/-- A contiguous same-side segment has a suitable global start position. -/
theorem _root_.Splay.Lazy.IsSegment.exists_uniformSideInterval
    {α : Type*} {inside whole : List α} (projectSide : α → Side)
    {side : Side} (segment : IsSegment inside whole)
    (sameSide : ∀ element ∈ inside, projectSide element = side) :
    ∃ start,
      UniformSideInterval (whole.map projectSide) side start inside.length := by
  obtain ⟨front, back, decomposition⟩ := segment
  exact ⟨front.length,
    uniformSideInterval_of_decomposition
      projectSide decomposition sameSide⟩

/--
Every complete four-child group in a uniform interval is a same-side double
group.  Combined with `HitSideSchedule`, it is therefore a genuine zig-zig.
-/
theorem doubleStepFlags_eq_true_of_mem_completeDoubleGroups
    {kinds : List SplayStepKind} {sides : List Side}
    (schedule : HitSideSchedule kinds sides)
    {side : Side} {start length group : ℕ}
    (uniform :
      UniformSideInterval (duplicateHitSides sides) side start length)
    (member : group ∈ completeDoubleGroups start length) :
    (doubleStepFlags kinds)[group]? = some true := by
  have groupStart :=
    start_le_four_mul_of_mem_completeDoubleGroups member
  have groupEnd :=
    four_mul_add_four_le_end_of_mem_completeDoubleGroups member
  have firstDuplicated :
      (duplicateHitSides sides)[4 * group]? = some side :=
    uniform (4 * group) groupStart (by omega)
  have secondDuplicated :
      (duplicateHitSides sides)[4 * group + 2]? = some side :=
    uniform (4 * group + 2) (by omega) (by omega)
  have firstCell : sides[2 * group]? = some side := by
    rw [← getElem?_duplicateHitSides_even sides (2 * group)]
    simpa only [show 2 * (2 * group) = 4 * group by omega] using
      firstDuplicated
  have secondCell : sides[2 * group + 1]? = some side := by
    rw [← getElem?_duplicateHitSides_even sides (2 * group + 1)]
    simpa only [show 2 * (2 * group + 1) = 4 * group + 2 by omega] using
      secondDuplicated
  rw [schedule.doubleStepFlags_eq_sameSideDoubleFlags]
  exact
    sameSideDoubleFlags_getElem?_eq_true
      sides group side firstCell secondCell

/--
Kernel-checked geometric witness for the manuscript's
`internal-pairings-fraction` lemma.  Each listed group is a genuine zig-zig
wholly inside the interval and hence contributes one internal pairing in
each phase.
-/
structure InternalPairingFractionWitness
    (kinds : List SplayStepKind) (intervalLength : ℕ) where
  groups : List ℕ
  groups_nodup : groups.Nodup
  internal_zigZig :
    ∀ group ∈ groups, (doubleStepFlags kinds)[group]? = some true
  length_bound : intervalLength ≤ 4 * groups.length + 6
  phase_lower_bound : (intervalLength - 6) / 4 ≤ groups.length

/-- A uniform contiguous interval automatically has the fraction witness. -/
def HitSideSchedule.internalPairingFractionWitness
    {kinds : List SplayStepKind} {sides : List Side}
    (schedule : HitSideSchedule kinds sides)
    {side : Side} {start length : ℕ}
    (uniform :
      UniformSideInterval (duplicateHitSides sides) side start length) :
    InternalPairingFractionWitness kinds length where
  groups := completeDoubleGroups start length
  groups_nodup := completeDoubleGroups_nodup start length
  internal_zigZig := fun group member =>
    doubleStepFlags_eq_true_of_mem_completeDoubleGroups
      schedule uniform member
  length_bound := by
    rw [length_completeDoubleGroups]
    exact interval_length_le_four_mul_completeDoubleGroupCount_add_six _ _
  phase_lower_bound := by
    rw [length_completeDoubleGroups]
    exact sub_six_div_four_le_completeDoubleGroupCount _ _

/-- Two phases give the manuscript's combined multiplication-form bound. -/
theorem InternalPairingFractionWitness.total_pairing_bound
    {kinds : List SplayStepKind} {intervalLength : ℕ}
    (witness : InternalPairingFractionWitness kinds intervalLength) :
    intervalLength ≤ 2 * (2 * witness.groups.length) + 6 := by
  have bound := witness.length_bound
  omega

end Splay.Accounting
