import Splay.Interface.ActivityCoefficients

namespace Splay.Analysis

/-- The rate contributed by insertion and variation coefficients. The added
one covers initialization, zig-zags, and zero coefficient pairs uniformly. -/
def coefficientRate (coefficients : Interface.ActivityCoefficients) (G : ℕ) : ℕ :=
  (coefficients G).1 + G * (coefficients G).2 + 1

/-- The splay factor exported by arbitrary valid interface coefficients.
Boundary credits introduce the single logarithm of `coefficientRate`. -/
def coefficientFactor (coefficients : Interface.ActivityCoefficients) (G : ℕ) : ℕ :=
  coefficientRate coefficients G * (Nat.clog 2 (coefficientRate coefficients G) + 1)

theorem coefficientRate_pos (coefficients : Interface.ActivityCoefficients) (G : ℕ) :
    0 < coefficientRate coefficients G := Nat.zero_lt_succ _

theorem coefficientFactor_pos (coefficients : Interface.ActivityCoefficients) (G : ℕ) :
    0 < coefficientFactor coefficients G :=
  Nat.mul_pos (coefficientRate_pos coefficients G) (Nat.zero_lt_succ _)

end Splay.Analysis
