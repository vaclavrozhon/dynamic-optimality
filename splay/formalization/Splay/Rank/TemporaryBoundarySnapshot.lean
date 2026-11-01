import Splay.Rank.FromTree
import Splay.Rank.Heavy
import Splay.Rank.TemporaryPriority

namespace Splay.Rank

/--
The two-element marker used by the temporary-priority argument around one
accessed value.
-/
def twoBoundaryMarker {n : ℕ}
    (left right : External n) (element : External n) : Bool :=
  decide (element = left ∨ element = right)

/--
The rank function obtained by assigning artificial priority `0.5` to two
distinguished external positions and doubling every genuine rank.
-/
def twoBoundaryTemporaryRank {n : ℕ}
    (snapshot : Snapshot n) (left right : External n)
    (element : External n) : ℕ :=
  temporaryPriority snapshot.rank
    (twoBoundaryMarker left right) element

@[simp]
theorem twoBoundaryTemporaryRank_eq_one_left {n : ℕ}
    (snapshot : Snapshot n) (left right : External n) :
    twoBoundaryTemporaryRank snapshot left right left = 1 := by
  simp [twoBoundaryTemporaryRank, twoBoundaryMarker,
    temporaryPriority, artificialPriority]

@[simp]
theorem twoBoundaryTemporaryRank_eq_one_right {n : ℕ}
    (snapshot : Snapshot n) (left right : External n) :
    twoBoundaryTemporaryRank snapshot left right right = 1 := by
  simp [twoBoundaryTemporaryRank, twoBoundaryMarker,
    temporaryPriority, artificialPriority]

theorem twoBoundaryTemporaryRank_eq_truePriority {n : ℕ}
    (snapshot : Snapshot n) (left right element : External n)
    (ordinary : element ≠ left ∧ element ≠ right) :
    twoBoundaryTemporaryRank snapshot left right element =
      truePriority (snapshot.rank element) := by
  simp [twoBoundaryTemporaryRank, twoBoundaryMarker,
    temporaryPriority, ordinary.1, ordinary.2]

/-- The one-element marker used after restoring the first boundary rank. -/
def oneBoundaryMarker {n : ℕ}
    (special : External n) (element : External n) : Bool :=
  decide (element = special)

/--
Temporary priority for one remaining artificial boundary; every other
genuine rank is doubled.
-/
def oneBoundaryTemporaryRank {n : ℕ}
    (snapshot : Snapshot n) (special : External n)
    (element : External n) : ℕ :=
  temporaryPriority snapshot.rank
    (oneBoundaryMarker special) element

@[simp]
theorem oneBoundaryTemporaryRank_eq_one {n : ℕ}
    (snapshot : Snapshot n) (special : External n) :
    oneBoundaryTemporaryRank snapshot special special = 1 := by
  simp [oneBoundaryTemporaryRank, oneBoundaryMarker,
    temporaryPriority, artificialPriority]

theorem oneBoundaryTemporaryRank_eq_truePriority {n : ℕ}
    (snapshot : Snapshot n) (special element : External n)
    (ordinary : element ≠ special) :
    oneBoundaryTemporaryRank snapshot special element =
      truePriority (snapshot.rank element) := by
  simp [oneBoundaryTemporaryRank, oneBoundaryMarker,
    temporaryPriority, ordinary]

/--
Doubling every genuine rank is a valid snapshot transformation.  It changes
numeric codes but preserves all comparisons and therefore all heavy-path
choices.
-/
def Snapshot.withTruePriority {n : ℕ}
    (snapshot : Snapshot n) : Snapshot n where
  rank element := truePriority (snapshot.rank element)
  maxRank := truePriority snapshot.maxRank
  rank_le_max := by
    intro element
    simp only [truePriority]
    exact Nat.mul_le_mul_left 2 (snapshot.rank_le_max element)
  uniqueIntervalMin := by
    intro lower upper nonempty
    obtain ⟨candidate, minimum, unique⟩ :=
      snapshot.uniqueIntervalMin lower upper nonempty
    refine ⟨candidate, ⟨minimum.1, minimum.2.1, ?_⟩, ?_⟩
    · intro element elementLower elementUpper
      simp only [truePriority]
      exact Nat.mul_le_mul_left 2
        (minimum.2.2 element elementLower elementUpper)
    · intro other otherMinimum
      apply unique other
      refine ⟨otherMinimum.1, otherMinimum.2.1, ?_⟩
      intro element elementLower elementUpper
      have doubled :=
        otherMinimum.2.2 element elementLower elementUpper
      simp only [truePriority] at doubled
      omega
  hasZero := by
    obtain ⟨element, zero⟩ := snapshot.hasZero
    exact ⟨element, by simp [truePriority, zero]⟩

@[simp]
theorem withTruePriority_rank {n : ℕ}
    (snapshot : Snapshot n) :
    snapshot.withTruePriority.rank =
      fun element => truePriority (snapshot.rank element) :=
  rfl

/-- Doubling ranks preserves the full interval-minimum predicate. -/
theorem isIntervalMin_withTruePriority_iff
    {n : ℕ} (snapshot : Snapshot n)
    (lower upper candidate : External n) :
    IsIntervalMin snapshot.withTruePriority.rank
        lower upper candidate ↔
      IsIntervalMin snapshot.rank lower upper candidate := by
  constructor
  · intro minimum
    refine ⟨minimum.1, minimum.2.1, ?_⟩
    intro element elementLower elementUpper
    have doubled :=
      minimum.2.2 element elementLower elementUpper
    simp only [withTruePriority_rank, truePriority] at doubled
    omega
  · intro minimum
    refine ⟨minimum.1, minimum.2.1, ?_⟩
    intro element elementLower elementUpper
    simp only [withTruePriority_rank, truePriority]
    exact Nat.mul_le_mul_left 2
      (minimum.2.2 element elementLower elementUpper)

/-- Every interval chooses the same canonical owner after rank doubling. -/
theorem intervalMin_withTruePriority_eq
    {n : ℕ} (snapshot : Snapshot n)
    (lower upper : External n) (nonempty : lower ≤ upper) :
    snapshot.withTruePriority.intervalMin lower upper nonempty =
      snapshot.intervalMin lower upper nonempty := by
  symm
  apply snapshot.withTruePriority.intervalMin_unique
  exact
    (isIntervalMin_withTruePriority_iff
      snapshot lower upper
        (snapshot.intervalMin lower upper nonempty)).2
      (snapshot.intervalMin_isMin lower upper nonempty)

/-- Every ternary heavy-branch choice is invariant under rank doubling. -/
theorem heavyBranch_withTruePriority_eq
    {n : ℕ} (snapshot : Snapshot n)
    (lower upper : External n) (nonempty : lower ≤ upper)
    (root : ℕ) :
    snapshot.withTruePriority.heavyBranch
        lower upper nonempty root =
      snapshot.heavyBranch lower upper nonempty root := by
  have originalHeavy :=
    snapshot.heavyBranch_isHeavy lower upper nonempty root
  obtain ⟨candidate, minimum, contains⟩ := originalHeavy
  have scaledHeavy :
      snapshot.withTruePriority.IsHeavyBranch
        lower upper root
        (snapshot.heavyBranch lower upper nonempty root) :=
    ⟨candidate,
      (isIntervalMin_withTruePriority_iff
        snapshot lower upper candidate).2 minimum,
      contains⟩
  exact
    (snapshot.withTruePriority.heavyBranch_unique
      lower upper nonempty root scaledHeavy).symm

private theorem eq_of_rank_eq_zero
    {n : ℕ} (snapshot : Snapshot n) {root element : External n}
    (rootRank : snapshot.rank root = 0)
    (elementRank : snapshot.rank element = 0) :
    element = root := by
  let lower : External n := ⟨0, by omega⟩
  let upper : External n := ⟨2 * n, by omega⟩
  have nonempty : lower ≤ upper := by
    simp [lower, upper]
  have rootMin :
      IsIntervalMin snapshot.rank lower upper root := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ root.val
      omega
    · change root.val ≤ 2 * n
      omega
    · intro node _ _
      rw [rootRank]
      omega
  have elementMin :
      IsIntervalMin snapshot.rank lower upper element := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ element.val
      omega
    · change element.val ≤ 2 * n
      omega
    · intro node _ _
      rw [elementRank]
      omega
  have rootUnique :=
    snapshot.intervalMin_unique lower upper nonempty rootMin
  have elementUnique :=
    snapshot.intervalMin_unique lower upper nonempty elementMin
  exact elementUnique.trans rootUnique.symm

private theorem rank_pos_of_ne_root
    {n : ℕ} (snapshot : Snapshot n) {root element : External n}
    (rootRank : snapshot.rank root = 0)
    (different : element ≠ root) :
    0 < snapshot.rank element := by
  by_contra notPositive
  have zero : snapshot.rank element = 0 := by omega
  exact different (eq_of_rank_eq_zero snapshot rootRank zero)

/--
Lowering one non-root external position to artificial priority `0.5`
preserves uniqueness of interval minima.
-/
theorem hasUniqueIntervalMin_oneBoundaryTemporaryRank
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0) :
    HasUniqueIntervalMin
      (oneBoundaryTemporaryRank snapshot special) := by
  intro lower upper nonempty
  by_cases specialInside : lower ≤ special ∧ special ≤ upper
  · by_cases rootInside : lower ≤ root ∧ root ≤ upper
    · refine ⟨root, ?_, ?_⟩
      · refine ⟨rootInside.1, rootInside.2, ?_⟩
        intro element _ _
        rw [oneBoundaryTemporaryRank_eq_truePriority
          snapshot special root different.symm, rootRank]
        simp [truePriority]
      · intro candidate candidateMin
        have candidateLeRoot :=
          candidateMin.2.2 root rootInside.1 rootInside.2
        rw [oneBoundaryTemporaryRank_eq_truePriority
          snapshot special root different.symm, rootRank] at candidateLeRoot
        simp only [truePriority, Nat.mul_zero] at candidateLeRoot
        by_cases candidateSpecial : candidate = special
        · subst candidate
          simp at candidateLeRoot
        · rw [oneBoundaryTemporaryRank_eq_truePriority
            snapshot special candidate candidateSpecial] at candidateLeRoot
          have candidateRankZero : snapshot.rank candidate = 0 := by
            simp only [truePriority] at candidateLeRoot
            omega
          exact eq_of_rank_eq_zero snapshot rootRank candidateRankZero
    · refine ⟨special, ?_, ?_⟩
      · refine ⟨specialInside.1, specialInside.2, ?_⟩
        intro element elementLower elementUpper
        by_cases elementSpecial : element = special
        · subst element
          exact Nat.le_refl _
        · have elementNotRoot : element ≠ root := by
            intro equal
            apply rootInside
            simpa [equal] using And.intro elementLower elementUpper
          rw [oneBoundaryTemporaryRank_eq_one,
            oneBoundaryTemporaryRank_eq_truePriority
              snapshot special element elementSpecial]
          have positive :=
            rank_pos_of_ne_root snapshot rootRank elementNotRoot
          simp only [truePriority]
          omega
      · intro candidate candidateMin
        have candidateLeSpecial :=
          candidateMin.2.2 special
            specialInside.1 specialInside.2
        rw [oneBoundaryTemporaryRank_eq_one] at candidateLeSpecial
        by_cases candidateSpecial : candidate = special
        · exact candidateSpecial
        · have candidateNotRoot : candidate ≠ root := by
            intro equal
            apply rootInside
            subst candidate
            exact ⟨candidateMin.1, candidateMin.2.1⟩
          rw [oneBoundaryTemporaryRank_eq_truePriority
            snapshot special candidate candidateSpecial] at candidateLeSpecial
          have positive :=
            rank_pos_of_ne_root snapshot rootRank candidateNotRoot
          simp only [truePriority] at candidateLeSpecial
          omega
  · obtain ⟨candidate, candidateMin, candidateUnique⟩ :=
      snapshot.uniqueIntervalMin lower upper nonempty
    have candidateOrdinary : candidate ≠ special := by
      intro equal
      apply specialInside
      subst candidate
      exact ⟨candidateMin.1, candidateMin.2.1⟩
    refine ⟨candidate, ?_, ?_⟩
    · refine ⟨candidateMin.1, candidateMin.2.1, ?_⟩
      intro element elementLower elementUpper
      have elementOrdinary : element ≠ special := by
        intro equal
        apply specialInside
        simpa [equal] using And.intro elementLower elementUpper
      rw [oneBoundaryTemporaryRank_eq_truePriority
          snapshot special candidate candidateOrdinary,
        oneBoundaryTemporaryRank_eq_truePriority
          snapshot special element elementOrdinary]
      simp only [truePriority]
      exact Nat.mul_le_mul_left 2
        (candidateMin.2.2 element elementLower elementUpper)
    · intro other otherMin
      have otherOrdinary : other ≠ special := by
        intro equal
        apply specialInside
        subst other
        exact ⟨otherMin.1, otherMin.2.1⟩
      apply candidateUnique other
      refine ⟨otherMin.1, otherMin.2.1, ?_⟩
      intro element elementLower elementUpper
      have elementOrdinary : element ≠ special := by
        intro equal
        apply specialInside
        simpa [equal] using And.intro elementLower elementUpper
      have temporaryLe :=
        otherMin.2.2 element elementLower elementUpper
      rw [oneBoundaryTemporaryRank_eq_truePriority
          snapshot special other otherOrdinary,
        oneBoundaryTemporaryRank_eq_truePriority
          snapshot special element elementOrdinary] at temporaryLe
      simp only [truePriority] at temporaryLe
      omega

/--
A concrete snapshot with one remaining artificial boundary priority.
-/
def Snapshot.withOneBoundaryTemporaryPriority
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0) :
    Snapshot n where
  rank := oneBoundaryTemporaryRank snapshot special
  maxRank := 2 * snapshot.maxRank + 1
  rank_le_max := by
    intro element
    by_cases marked : element = special
    · subst element
      rw [oneBoundaryTemporaryRank_eq_one]
      omega
    · rw [oneBoundaryTemporaryRank_eq_truePriority
        snapshot special element marked]
      simp only [truePriority]
      have bound := snapshot.rank_le_max element
      omega
  uniqueIntervalMin :=
    hasUniqueIntervalMin_oneBoundaryTemporaryRank
      snapshot root special different rootRank
  hasZero := by
    refine ⟨root, ?_⟩
    rw [oneBoundaryTemporaryRank_eq_truePriority
      snapshot special root different.symm, rootRank]
    simp [truePriority]

@[simp]
theorem withOneBoundaryTemporaryPriority_rank
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0) :
    (snapshot.withOneBoundaryTemporaryPriority
      root special different rootRank).rank =
        oneBoundaryTemporaryRank snapshot special :=
  rfl

/--
Artificially lowering one external node on each side of the unique rank-zero
root preserves uniqueness of interval minima.

The order hypothesis is essential.  An interval containing both artificial
nodes then also contains the rank-zero root, so the two equal artificial
priorities can never tie for minimum.
-/
theorem hasUniqueIntervalMin_twoBoundaryTemporaryRank
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0) :
    HasUniqueIntervalMin
      (twoBoundaryTemporaryRank snapshot left right) := by
  intro lower upper nonempty
  by_cases rootInside : lower ≤ root ∧ root ≤ upper
  · refine ⟨root, ?_, ?_⟩
    · refine ⟨rootInside.1, rootInside.2, ?_⟩
      intro element _ _
      have rootOrdinary : root ≠ left ∧ root ≠ right := by
        constructor
        · intro equal
          have values := congrArg Fin.val equal
          have less : left.val < root.val := ordered.1
          omega
        · intro equal
          have values := congrArg Fin.val equal
          have less : root.val < right.val := ordered.2
          omega
      rw [twoBoundaryTemporaryRank_eq_truePriority
        snapshot left right root rootOrdinary, rootRank]
      simp [truePriority]
    · intro candidate candidateMin
      have candidateLeRoot :=
        candidateMin.2.2 root rootInside.1 rootInside.2
      have rootOrdinary : root ≠ left ∧ root ≠ right := by
        constructor
        · intro equal
          have values := congrArg Fin.val equal
          have less : left.val < root.val := ordered.1
          omega
        · intro equal
          have values := congrArg Fin.val equal
          have less : root.val < right.val := ordered.2
          omega
      rw [twoBoundaryTemporaryRank_eq_truePriority
        snapshot left right root rootOrdinary, rootRank] at candidateLeRoot
      simp only [truePriority, Nat.mul_zero] at candidateLeRoot
      by_cases candidateLeft : candidate = left
      · subst candidate
        simp at candidateLeRoot
      · by_cases candidateRight : candidate = right
        · subst candidate
          simp at candidateLeRoot
        · have candidateOrdinary : candidate ≠ left ∧ candidate ≠ right :=
            ⟨candidateLeft, candidateRight⟩
          rw [twoBoundaryTemporaryRank_eq_truePriority
            snapshot left right candidate candidateOrdinary] at candidateLeRoot
          have candidateRankZero : snapshot.rank candidate = 0 := by
            simp only [truePriority] at candidateLeRoot
            omega
          exact eq_of_rank_eq_zero snapshot rootRank candidateRankZero
  · by_cases leftInside : lower ≤ left ∧ left ≤ upper
    · have rightOutside : ¬(lower ≤ right ∧ right ≤ upper) := by
        intro rightInside
        apply rootInside
        exact
          ⟨leftInside.1.trans (Nat.le_of_lt ordered.1),
            (Nat.le_of_lt ordered.2).trans rightInside.2⟩
      refine ⟨left, ?_, ?_⟩
      · refine ⟨leftInside.1, leftInside.2, ?_⟩
        intro element elementLower elementUpper
        by_cases elementLeft : element = left
        · subst element
          exact Nat.le_refl _
        · have elementNotRight : element ≠ right := by
            intro equal
            apply rightOutside
            simpa [equal] using And.intro elementLower elementUpper
          have elementNotRoot : element ≠ root := by
            intro equal
            apply rootInside
            simpa [equal] using And.intro elementLower elementUpper
          rw [twoBoundaryTemporaryRank_eq_one_left,
            twoBoundaryTemporaryRank_eq_truePriority
              snapshot left right element
                ⟨elementLeft, elementNotRight⟩]
          have positive :=
            rank_pos_of_ne_root snapshot rootRank elementNotRoot
          simp only [truePriority]
          omega
      · intro candidate candidateMin
        have candidateLeLeft :=
          candidateMin.2.2 left leftInside.1 leftInside.2
        rw [twoBoundaryTemporaryRank_eq_one_left] at candidateLeLeft
        by_cases candidateLeft : candidate = left
        · exact candidateLeft
        · have candidateNotRight : candidate ≠ right := by
            intro equal
            apply rightOutside
            subst candidate
            exact ⟨candidateMin.1, candidateMin.2.1⟩
          have candidateNotRoot : candidate ≠ root := by
            intro equal
            apply rootInside
            subst candidate
            exact ⟨candidateMin.1, candidateMin.2.1⟩
          rw [twoBoundaryTemporaryRank_eq_truePriority
            snapshot left right candidate
              ⟨candidateLeft, candidateNotRight⟩] at candidateLeLeft
          have positive :=
            rank_pos_of_ne_root snapshot rootRank candidateNotRoot
          simp only [truePriority] at candidateLeLeft
          omega
    · by_cases rightInside : lower ≤ right ∧ right ≤ upper
      · refine ⟨right, ?_, ?_⟩
        · refine ⟨rightInside.1, rightInside.2, ?_⟩
          intro element elementLower elementUpper
          by_cases elementRight : element = right
          · subst element
            exact Nat.le_refl _
          · have elementNotLeft : element ≠ left := by
              intro equal
              apply leftInside
              simpa [equal] using And.intro elementLower elementUpper
            have elementNotRoot : element ≠ root := by
              intro equal
              apply rootInside
              simpa [equal] using And.intro elementLower elementUpper
            rw [twoBoundaryTemporaryRank_eq_one_right,
              twoBoundaryTemporaryRank_eq_truePriority
                snapshot left right element
                  ⟨elementNotLeft, elementRight⟩]
            have positive :=
              rank_pos_of_ne_root snapshot rootRank elementNotRoot
            simp only [truePriority]
            omega
        · intro candidate candidateMin
          have candidateLeRight :=
            candidateMin.2.2 right rightInside.1 rightInside.2
          rw [twoBoundaryTemporaryRank_eq_one_right] at candidateLeRight
          by_cases candidateRight : candidate = right
          · exact candidateRight
          · have candidateNotLeft : candidate ≠ left := by
              intro equal
              apply leftInside
              subst candidate
              exact ⟨candidateMin.1, candidateMin.2.1⟩
            have candidateNotRoot : candidate ≠ root := by
              intro equal
              apply rootInside
              subst candidate
              exact ⟨candidateMin.1, candidateMin.2.1⟩
            rw [twoBoundaryTemporaryRank_eq_truePriority
              snapshot left right candidate
                ⟨candidateNotLeft, candidateRight⟩] at candidateLeRight
            have positive :=
              rank_pos_of_ne_root snapshot rootRank candidateNotRoot
            simp only [truePriority] at candidateLeRight
            omega
      · obtain ⟨candidate, candidateMin, candidateUnique⟩ :=
          snapshot.uniqueIntervalMin lower upper nonempty
        have candidateOrdinary : candidate ≠ left ∧ candidate ≠ right := by
          constructor
          · intro equal
            apply leftInside
            subst candidate
            exact ⟨candidateMin.1, candidateMin.2.1⟩
          · intro equal
            apply rightInside
            subst candidate
            exact ⟨candidateMin.1, candidateMin.2.1⟩
        refine ⟨candidate, ?_, ?_⟩
        · refine ⟨candidateMin.1, candidateMin.2.1, ?_⟩
          intro element elementLower elementUpper
          have elementOrdinary : element ≠ left ∧ element ≠ right := by
            constructor
            · intro equal
              apply leftInside
              simpa [equal] using And.intro elementLower elementUpper
            · intro equal
              apply rightInside
              simpa [equal] using And.intro elementLower elementUpper
          rw [twoBoundaryTemporaryRank_eq_truePriority
              snapshot left right candidate candidateOrdinary,
            twoBoundaryTemporaryRank_eq_truePriority
              snapshot left right element elementOrdinary]
          simp only [truePriority]
          exact Nat.mul_le_mul_left 2
            (candidateMin.2.2 element elementLower elementUpper)
        · intro other otherMin
          have otherOrdinary : other ≠ left ∧ other ≠ right := by
            constructor
            · intro equal
              apply leftInside
              subst other
              exact ⟨otherMin.1, otherMin.2.1⟩
            · intro equal
              apply rightInside
              subst other
              exact ⟨otherMin.1, otherMin.2.1⟩
          apply candidateUnique other
          refine ⟨otherMin.1, otherMin.2.1, ?_⟩
          intro element elementLower elementUpper
          have elementOrdinary : element ≠ left ∧ element ≠ right := by
            constructor
            · intro equal
              apply leftInside
              simpa [equal] using And.intro elementLower elementUpper
            · intro equal
              apply rightInside
              simpa [equal] using And.intro elementLower elementUpper
          have temporaryLe :=
            otherMin.2.2 element elementLower elementUpper
          rw [twoBoundaryTemporaryRank_eq_truePriority
              snapshot left right other otherOrdinary,
            twoBoundaryTemporaryRank_eq_truePriority
              snapshot left right element elementOrdinary] at temporaryLe
          simp only [truePriority] at temporaryLe
          omega

/--
A concrete rank snapshot for the manuscript's two artificial boundary
priorities.
-/
def Snapshot.withTwoBoundaryTemporaryPriority
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0) :
    Snapshot n where
  rank := twoBoundaryTemporaryRank snapshot left right
  maxRank := 2 * snapshot.maxRank + 1
  rank_le_max := by
    intro element
    by_cases marked : element = left ∨ element = right
    · rcases marked with rfl | rfl
      · rw [twoBoundaryTemporaryRank_eq_one_left]
        omega
      · rw [twoBoundaryTemporaryRank_eq_one_right]
        omega
    · rw [twoBoundaryTemporaryRank_eq_truePriority
        snapshot left right element ⟨not_or.mp marked |>.1,
          not_or.mp marked |>.2⟩]
      simp only [truePriority]
      have bound := snapshot.rank_le_max element
      omega
  uniqueIntervalMin :=
    hasUniqueIntervalMin_twoBoundaryTemporaryRank
      snapshot left root right ordered rootRank
  hasZero := by
    refine ⟨root, ?_⟩
    have ordinary : root ≠ left ∧ root ≠ right := by
      constructor
      · intro equal
        have values := congrArg Fin.val equal
        have less : left.val < root.val := ordered.1
        omega
      · intro equal
        have values := congrArg Fin.val equal
        have less : root.val < right.val := ordered.2
        omega
    rw [twoBoundaryTemporaryRank_eq_truePriority
      snapshot left right root ordinary, rootRank]
    simp [truePriority]

@[simp]
theorem withTwoBoundaryTemporaryPriority_rank
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0) :
    (snapshot.withTwoBoundaryTemporaryPriority
      left root right ordered rootRank).rank =
        twoBoundaryTemporaryRank snapshot left right :=
  rfl

end Splay.Rank
