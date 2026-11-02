import ChaCha.Paper20261030.SplayAuxiliarySource
import MultiSplay.ClassicalSwitchWord

/-!
# Exposing an actual inorder outlet using ordinary splaying

An interior outlet is the gap between two consecutive separator identities.
Splaying the lower separator, then the upper separator inside its right
child, puts this exact payload within two edges of the root. The two
executions and their navigation are charged to one unchanged potential.
No balance or assumed auxiliary-cost hypothesis is used.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR
open ColoredStorage
open MultiSplay Auxiliary ClassicalSwitch

variable {α ρ : Type*}

theorem splay_source_rearranges_at {before after : RawTree ρ} {key : ρ} {rotations : Nat}
    (execution : Splay key before after rotations) (unique : before.inorder.Nodup)
    (ports : Nat → Source α ρ) (base : Nat) :
    SourcePointer.Rearranges (GapSource.encode before ports base)
      (GapSource.encode after ports base) (3*rotations+1) := by
  have result := splay_source_rearranges execution unique (fun i => ports (base+i))
  simpa only [← GapSource.encode_offset,Nat.add_zero] using result

private theorem empty_of_empty_word {tree : RawTree ρ} (word : tree.inorder = []) :
    tree = .empty := by cases tree <;> simp_all [Tree.inorder]

/-- Interior exposure uses exactly the two specified bottom-up splays.
The output payload in gap `left.length+1` remains the original payload. -/
theorem expose_interior {before : RawTree ρ} {left right : List ρ} {lo hi : ρ}
    (word : before.inorder = left++[lo,hi]++right)
    (unique : before.inorder.Nodup) {capacity : Nat} (bounded : before.size ≤ capacity)
    (ports : Nat → Source α ρ) :
    ∃ a middle b : RawTree ρ, ∃ first second : Nat,
      Splay lo before (.node a lo middle) first ∧
      Splay hi middle (.node .empty hi b) second ∧
      a.inorder = left ∧ b.inorder = right ∧
      SourcePointer.Rearranges (GapSource.encode before ports 0)
        (.fork lo (GapSource.encode a ports 0)
          (.fork hi (ports (left.length+1)) (GapSource.encode b ports (left.length+2))))
        (3*(first+second)+4) ∧
      (3*(first+second)+4)+6*potential (.node a lo (.node .empty hi b)) ≤
        6*potential before+36*Nat.log 2 capacity+10 := by
  classical
  obtain ⟨a,middle,first,firstSplay,leftWord,middleWord⟩ :=
    split_unique (left := left) (right := hi::right)
      (by simpa [List.append_assoc] using word) unique
  have parts := nodup_node (firstSplay.inorder_eq ▸ unique)
  obtain ⟨vacant,b,second,secondSplay,emptyWord,rightWord⟩ :=
    split_unique (left := []) (right := right)
      (by simpa using middleWord) parts.2.1
  have empty := empty_of_empty_word emptyWord
  subst vacant
  have middleBound : middle.size ≤ capacity := by
    have size := firstSplay.size_eq
    simp only [Tree.size] at size
    omega
  have firstBound := splay_amortized_capacity firstSplay unique bounded
  have secondBound := splay_amortized_capacity secondSplay parts.2.1 middleBound
  have middleSize := secondSplay.size_eq
  have sameRank : rank (.node a lo middle) = rank (.node a lo (.node .empty hi b)) := by
    simp only [rank,Tree.size] at middleSize ⊢
    rw [middleSize]
  have sizeLeft : a.size = left.length := by
    rw [← Tree.length_inorder,leftWord]
  have firstTrace := splay_source_rearranges firstSplay unique ports
  simp only [GapSource.encode,Nat.zero_add] at firstTrace
  have secondTrace := (splay_source_rearranges_at secondSplay parts.2.1 ports (a.size+1)).right
    (l := GapSource.encode a ports 0) (record := lo)
  have physical : SourcePointer.Rearranges (GapSource.encode before ports 0)
      (.fork lo (GapSource.encode a ports 0)
        (.fork hi (ports (left.length+1)) (GapSource.encode b ports (left.length+2))))
      (3*(first+second)+4) := by
    have trace := firstTrace.trans secondTrace
    have charged := trace.mono (n := 3*(first+second)+4) (by omega)
    simpa [GapSource.encode,Tree.size,sizeLeft,Nat.add_assoc] using charged
  refine ⟨a,middle,b,first,second,firstSplay,secondSplay,leftWord,rightWord,physical,?_⟩
  simp only [potential] at firstBound secondBound ⊢
  rw [sameRank] at firstBound
  omega

theorem expose_first {before : RawTree ρ} {right : List ρ} {key : ρ}
    (word : before.inorder = key::right)
    (unique : before.inorder.Nodup) {capacity : Nat} (bounded : before.size ≤ capacity)
    (ports : Nat → Source α ρ) :
    ∃ after : RawTree ρ, ∃ rotations : Nat,
      Splay key before (.node .empty key after) rotations ∧ after.inorder = right ∧
      SourcePointer.Rearranges (GapSource.encode before ports 0)
        (.fork key (ports 0) (GapSource.encode after ports 1)) (3*rotations+1) ∧
      (3*rotations+1)+6*potential (.node .empty key after) ≤
        6*potential before+18*Nat.log 2 capacity+4 := by
  classical
  obtain ⟨vacant,after,rotations,execution,emptyWord,rightWord⟩ :=
    split_unique (left := []) (right := right) (by simpa using word) unique
  have empty := empty_of_empty_word emptyWord
  subst vacant
  have bound := splay_amortized_capacity execution unique bounded
  refine ⟨after,rotations,execution,rightWord,?_,by omega⟩
  simpa only [GapSource.encode,Tree.size,Nat.add_zero] using
    splay_source_rearranges execution unique ports

theorem expose_last {before : RawTree ρ} {left : List ρ} {key : ρ}
    (word : before.inorder = left++[key])
    (unique : before.inorder.Nodup) {capacity : Nat} (bounded : before.size ≤ capacity)
    (ports : Nat → Source α ρ) :
    ∃ after : RawTree ρ, ∃ rotations : Nat,
      Splay key before (.node after key .empty) rotations ∧ after.inorder = left ∧
      SourcePointer.Rearranges (GapSource.encode before ports 0)
        (.fork key (GapSource.encode after ports 0) (ports (left.length+1))) (3*rotations+1) ∧
      (3*rotations+1)+6*potential (.node after key .empty) ≤
        6*potential before+18*Nat.log 2 capacity+4 := by
  classical
  obtain ⟨after,vacant,rotations,execution,leftWord,emptyWord⟩ :=
    split_unique (left := left) (right := []) (by simpa using word) unique
  have empty := empty_of_empty_word emptyWord
  subst vacant
  have sizeLeft : after.size = left.length := by rw [← Tree.length_inorder,leftWord]
  have bound := splay_amortized_capacity execution unique bounded
  refine ⟨after,rotations,execution,leftWord,?_,by omega⟩
  simpa only [GapSource.encode,Tree.size,Nat.zero_add,sizeLeft] using
    splay_source_rearranges execution unique ports

end ChaCha.Paper20261030.SplayAuxiliary
