import Splay.Interface.ActivityCoefficients
import BinarySeededCompressionRecursion

namespace Splay.Interface

/-- An explicit provider from the verified, strictly cap-decreasing dyadic
compiler. This is the dyadic recurrence, not the stronger entropy recurrence. -/
def seededCoefficients (shape : Shape) : ActivityCoefficients :=
  Research.BinarySeededCompressionRecursion.originalCoefficients shape

theorem seededCoefficients_valid (shape : Shape)
    (exempt : shape.exemptPasses = 2)
    (numerator : shape.matchingNumerator = 1)
    (denominator : shape.matchingDenominator = 8) :
    CoefficientBound shape (seededCoefficients shape) :=
  Research.BinarySeededCompressionRecursion.original_coefficients_valid
    shape exempt numerator denominator

end Splay.Interface
