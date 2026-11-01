import Splay.Interface.Potential
import Splay.Interface.BlockCount

namespace Splay.Interface

@[simp] theorem totalInserts_append {n : ℕ} (first second : List (Operation n)) :
    totalInserts (first ++ second) = totalInserts first + totalInserts second := by
  simp [totalInserts]

@[simp] theorem totalIncreases_append {n : ℕ} (first second : List (Operation n)) :
    totalIncreases (first ++ second) = totalIncreases first + totalIncreases second := by
  simp [totalIncreases]

@[simp] theorem totalDecreases_append {n : ℕ} (first second : List (Operation n)) :
    totalDecreases (first ++ second) = totalDecreases first + totalDecreases second := by
  simp [totalDecreases]

@[simp] theorem totalActivity_append {n : ℕ} (first second : List (Operation n)) :
    totalActivity (first ++ second) = totalActivity first + totalActivity second := by
  simp [totalActivity]

@[simp] theorem totalBlockGrowth_append {n : ℕ} (first second : List (Operation n)) :
    totalBlockGrowth (first ++ second) = totalBlockGrowth first + totalBlockGrowth second := by
  simp [totalBlockGrowth]

end Splay.Interface
