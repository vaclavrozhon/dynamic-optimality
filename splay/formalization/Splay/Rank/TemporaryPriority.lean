import Splay.Rank.Basic

namespace Splay.Rank

/--
The integer code used for a genuine numerical rank when ranks are compared
with temporary artificial priorities.

Doubling leaves the odd code `1` available for the paper's artificial rank
`0.5`.  This code is an ordering device only: contracted gaps continue to use
the undoubled genuine ranks.
-/
def truePriority (rank : ℕ) : ℕ :=
  2 * rank

/-- The integer code representing the paper's temporary artificial rank `0.5`. -/
def artificialPriority : ℕ :=
  1

/--
Temporarily mark selected elements as having artificial priority `1`; every
unmarked element keeps the doubled code of its genuine rank.

The Boolean marker makes the exceptional set explicit and decidable.  In the
splay application it marks precisely the two boundary elements `x⁻` and `x⁺`.
-/
def temporaryPriority {α : Type*} (trueRank : α → ℕ)
    (isArtificial : α → Bool) (element : α) : ℕ :=
  if isArtificial element = true then
    artificialPriority
  else
    truePriority (trueRank element)

@[simp]
theorem truePriority_zero :
    truePriority 0 = 0 := by
  simp [truePriority]

@[simp]
theorem temporaryPriority_of_artificial {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {element : α}
    (hArtificial : isArtificial element = true) :
    temporaryPriority trueRank isArtificial element =
      artificialPriority := by
  simp [temporaryPriority, hArtificial]

@[simp]
theorem temporaryPriority_of_ordinary {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {element : α}
    (hOrdinary : isArtificial element = false) :
    temporaryPriority trueRank isArtificial element =
      truePriority (trueRank element) := by
  simp [temporaryPriority, hOrdinary]

/-- The artificial code lies strictly between rank zero and every positive rank. -/
theorem artificialPriority_between {rank : ℕ} (hPositive : 0 < rank) :
    0 < artificialPriority ∧
      artificialPriority < truePriority rank := by
  simp only [artificialPriority, truePriority]
  omega

/-- An unmarked element of genuine rank zero has temporary priority zero. -/
theorem temporaryPriority_eq_zero_of_root {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {root : α}
    (hRootRank : trueRank root = 0)
    (hRootOrdinary : isArtificial root = false) :
    temporaryPriority trueRank isArtificial root = 0 := by
  simp [temporaryPriority, hRootOrdinary, truePriority, hRootRank]

/-- A marked element has priority one, independently of its genuine rank. -/
theorem temporaryPriority_eq_one_of_artificial {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {element : α}
    (hArtificial : isArtificial element = true) :
    temporaryPriority trueRank isArtificial element = 1 := by
  simp [temporaryPriority, hArtificial, artificialPriority]

/--
The exact priority chain used around a splayed root: the unmarked rank-zero
root is below a marked boundary element, which is below every unmarked
positive-rank element.
-/
theorem temporaryPriority_root_artificial_ordinary {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool)
    {root special ordinary : α}
    (hRootRank : trueRank root = 0)
    (hRootOrdinary : isArtificial root = false)
    (hSpecial : isArtificial special = true)
    (hOrdinary : isArtificial ordinary = false)
    (hOrdinaryPositive : 0 < trueRank ordinary) :
    temporaryPriority trueRank isArtificial root <
        temporaryPriority trueRank isArtificial special ∧
      temporaryPriority trueRank isArtificial special <
        temporaryPriority trueRank isArtificial ordinary := by
  simp only [
    temporaryPriority_of_artificial trueRank isArtificial hSpecial,
    temporaryPriority_of_ordinary trueRank isArtificial hRootOrdinary,
    temporaryPriority_of_ordinary trueRank isArtificial hOrdinary,
    hRootRank,
    truePriority_zero
  ]
  exact artificialPriority_between hOrdinaryPositive

/--
Temporary priorities preserve non-strict comparison between two unmarked
elements.
-/
theorem temporaryPriority_le_iff_of_ordinary {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {left right : α}
    (hLeft : isArtificial left = false)
    (hRight : isArtificial right = false) :
    temporaryPriority trueRank isArtificial left ≤
        temporaryPriority trueRank isArtificial right ↔
      trueRank left ≤ trueRank right := by
  simp only [
    temporaryPriority_of_ordinary trueRank isArtificial hLeft,
    temporaryPriority_of_ordinary trueRank isArtificial hRight,
    truePriority
  ]
  omega

/-- Temporary priorities preserve strict comparison between unmarked elements. -/
theorem temporaryPriority_lt_iff_of_ordinary {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {left right : α}
    (hLeft : isArtificial left = false)
    (hRight : isArtificial right = false) :
    temporaryPriority trueRank isArtificial left <
        temporaryPriority trueRank isArtificial right ↔
      trueRank left < trueRank right := by
  simp only [
    temporaryPriority_of_ordinary trueRank isArtificial hLeft,
    temporaryPriority_of_ordinary trueRank isArtificial hRight,
    truePriority
  ]
  omega

/-- Temporary priorities preserve equality between unmarked elements. -/
theorem temporaryPriority_eq_iff_of_ordinary {α : Type*}
    (trueRank : α → ℕ) (isArtificial : α → Bool) {left right : α}
    (hLeft : isArtificial left = false)
    (hRight : isArtificial right = false) :
    temporaryPriority trueRank isArtificial left =
        temporaryPriority trueRank isArtificial right ↔
      trueRank left = trueRank right := by
  simp only [
    temporaryPriority_of_ordinary trueRank isArtificial hLeft,
    temporaryPriority_of_ordinary trueRank isArtificial hRight,
    truePriority
  ]
  omega

end Splay.Rank
