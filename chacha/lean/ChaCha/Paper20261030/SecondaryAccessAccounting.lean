import ChaCha.Paper20261030.DepthPreferences
import ChaCha.Paper20261030.MemoryCountAssembly

/-!
# Charging decoded secondary flips to the actual persistent writes

At each internal reference interval, the active endpoint identifies one
existing memory cell. The decoded access changes precisely its local bit.
Summing over all actual cells therefore pays every physical secondary flip.
-/

namespace ChaCha.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

theorem searchPath_take_owner {primary : PrefRouter α} {key : α} {height depth : Nat}
    (perfect : primary.Perfect height) (member : key ∈ primary.leaves) (bound : depth ≤ height) :
    (primary.searchPath key).take depth ∈ primary.ownerPaths depth := by
  induction depth generalizing primary height with
  | zero => simp [ownerPaths]
  | succ depth ih =>
    cases height with
    | zero => omega
    | succ height =>
      cases primary with
      | leaf value => exact False.elim perfect
      | fork bit left right =>
        by_cases inLeft : key ∈ left.leaves
        · simp only [searchPath,if_pos inLeft,List.take_succ_cons,ownerPaths]
          exact List.mem_append_left _ (List.mem_map.mpr ⟨_,ih perfect.1 inLeft (by omega),rfl⟩)
        · have inRight : key ∈ right.leaves := (List.mem_append.mp member).resolve_left inLeft
          simp only [searchPath,if_neg inLeft,if_pos inRight,List.take_succ_cons,ownerPaths]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih perfect.2 inRight (by omega),rfl⟩)

end ChaCha.PreferredProjection.PrefRouter

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

theorem write_sum_node (primary : PrefRouter α) {a cut b : Nat} (ha : a ≤ cut) (hb : cut < b)
    (left : DepthTree a cut) (right : DepthTree (cut+1) b) (writeCost : MemoryKey → Nat) :
    (∑ key ∈ memoryKeys primary (.node cut ha hb left right), writeCost key) =
      (∑ owner ∈ (primary.ownerPaths a).toFinset, writeCost (⟨a,cut,b⟩,owner)) +
        (∑ key ∈ memoryKeys primary left, writeCost key) +
        ∑ key ∈ memoryKeys primary right, writeCost key := by
  have dl := memoryKeys_disjoint_left primary hb left
  have dr := memoryKeys_disjoint_right primary ha right
  have dc := memoryKeys_disjoint_children primary left right
  have outer := Finset.disjoint_union_left.mpr ⟨dr,dc⟩
  simp only [rootMemoryKeys] at dl outer
  simp only [memoryKeys]
  rw [Finset.sum_union outer,Finset.sum_union dl,Finset.sum_image]
  intro u hu v hv same
  exact (Prod.mk.inj same).2

theorem decoded_flips_le_writes {height a b d : Nat} (reference : DepthTree a b)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (upper : b ≤ height)
    (endpoint : α) (member : endpoint ∈ primary.leaves) (memory : MemoryKey → Bool) :
    (decodeDepth reference (ownerBits primary endpoint memory)).accessFlips d ≤
      ∑ key ∈ memoryKeys primary reference,
        changesFrom (memory key) (depthWrite primary endpoint d key).toList := by
  induction reference with
  | leaf value => simp [decodeDepth,PrefRouter.accessFlips,memoryKeys]
  | @node a b cut ha hb left right ihl ihr =>
    rw [write_sum_node]
    have leftBound := ihl (by omega)
    have rightBound := ihr upper
    have ownerMember := PrefRouter.searchPath_take_owner perfect member (show a ≤ height by omega)
    have rootBound := Finset.single_le_sum (f := fun owner =>
      changesFrom (memory (⟨a,cut,b⟩,owner)) (depthWrite primary endpoint d (⟨a,cut,b⟩,owner)).toList)
      (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr ownerMember)
    have rootPrefix := List.take_prefix a (primary.searchPath endpoint)
    have leftMem := decodeDepth_mem left (ownerBits primary endpoint memory) d
    have rightMem := decodeDepth_mem right (ownerBits primary endpoint memory) d
    simp only [decodeDepth,PrefRouter.accessFlips]
    by_cases insideLeft : a ≤ d ∧ d ≤ cut
    · rw [if_pos (leftMem.mpr insideLeft)]
      have rootCost : changesFrom (memory (⟨a,cut,b⟩,(primary.searchPath endpoint).take a))
          (depthWrite primary endpoint d (⟨a,cut,b⟩,(primary.searchPath endpoint).take a)).toList =
          edgeChange (ownerBits primary endpoint memory ⟨a,cut,b⟩) false := by
        simp [depthWrite,rootPrefix,show a ≤ d ∧ d ≤ b by omega,show ¬cut < d by omega,
          changesFrom,ownerBits]
      rw [rootCost] at rootBound
      omega
    · rw [if_neg (fun h => insideLeft (leftMem.mp h))]
      by_cases insideRight : cut+1 ≤ d ∧ d ≤ b
      · rw [if_pos (rightMem.mpr insideRight)]
        have rootCost : changesFrom (memory (⟨a,cut,b⟩,(primary.searchPath endpoint).take a))
            (depthWrite primary endpoint d (⟨a,cut,b⟩,(primary.searchPath endpoint).take a)).toList =
            edgeChange (ownerBits primary endpoint memory ⟨a,cut,b⟩) true := by
          simp [depthWrite,rootPrefix,show a ≤ d ∧ d ≤ b by omega,show cut < d by omega,
            changesFrom,ownerBits]
        rw [rootCost] at rootBound
        omega
      · rw [if_neg (fun h => insideRight (rightMem.mp h))]
        exact Nat.zero_le _

theorem head_flips_le_writes {height a b d : Nat} (reference : DepthTree a b)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (perfect : before.Perfect height) (distinct : before.leaves.Nodup) (upper : b ≤ height)
    (memory : MemoryKey → Bool) :
    (decodeDepth reference (ownerBits before before.terminal memory)).accessFlips d ≤
      ∑ key ∈ memoryKeys before reference, changesFrom (memory key) (depthWrite before x d key).toList := by
  have bound := decoded_flips_le_writes reference before perfect upper before.terminal before.terminal_mem memory (d := d)
  have sums : (∑ key ∈ memoryKeys before reference,
      changesFrom (memory key) (depthWrite before before.terminal d key).toList) =
      ∑ key ∈ memoryKeys before reference, changesFrom (memory key) (depthWrite before x d key).toList := by
    apply Finset.sum_congr rfl
    intro key member
    rw [head_depthWrite_memory_owner step distinct reference key member]
    rfl
  exact sums ▸ bound

end ChaCha.Paper20261030.Secondary
