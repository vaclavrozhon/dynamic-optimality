import MultiSplay.EndpointCoreSupport
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Linear initialization support despite the larger leaf universe

At depth d there are at most 2^(floor(d/2)+1) core vertices. A binary
interval hierarchy has at most one split at each cut, so the number of
owner rows with a core owner is at most 4*(2^H-1), uniformly in its shape.
-/

namespace MultiSplay.EndpointEncoding

open TangoSquared (DepthTree DepthSplit)
open TangoSquared.Primary (Key level mem_level)

theorem level_card (depth : Nat) : (level depth).card = 2^depth := by
  induction depth with
  | zero => simp [level]
  | succ depth ih =>
      have disjoint : Disjoint ((level depth).image (false :: ·)) ((level depth).image (true :: ·)) := by
        apply Finset.disjoint_left.mpr
        intro key left right
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp left
        obtain ⟨b,_,same⟩ := Finset.mem_image.mp right
        cases same
      rw [level,Finset.card_union_of_disjoint disjoint,
        Finset.card_image_of_injective _ (fun _ _ same => (List.cons.inj same).2),
        Finset.card_image_of_injective _ (fun _ _ same => (List.cons.inj same).2),ih,pow_succ]
      omega

theorem core_level_bound (height depth : Nat) :
    ((level depth).filter (fun owner => owner ∈ coreNodes height)).card ≤ 2^(depth/2+1) := by
  by_cases even : depth % 2 = 0
  · have subset : (level depth).filter (fun owner => owner ∈ coreNodes height) ⊆
        (level (depth/2)).image core := by
      intro owner member
      obtain ⟨atDepth,inCore⟩ := Finset.mem_filter.mp member
      have length := (mem_level _ _).mp atDepth
      obtain ⟨address,_,eqn⟩ := mem_coreNodes.mp inCore
      rcases eqn with rfl | ⟨side,rfl⟩
      · have half : address.length = depth/2 := by rw [core_length] at length; omega
        exact Finset.mem_image.mpr ⟨address,(mem_level _ _).mpr half,rfl⟩
      · simp only [List.length_append,core_length,List.length_cons,List.length_nil] at length
        omega
    have bound := (Finset.card_le_card subset).trans (Finset.card_image_le)
    rw [pow_succ]
    rw [level_card] at bound
    omega
  · have subset : (level depth).filter (fun owner => owner ∈ coreNodes height) ⊆
        (level (depth/2)).image (fun address => core address ++ [false]) ∪
          (level (depth/2)).image (fun address => core address ++ [true]) := by
      intro owner member
      obtain ⟨atDepth,inCore⟩ := Finset.mem_filter.mp member
      have length := (mem_level _ _).mp atDepth
      obtain ⟨address,_,eqn⟩ := mem_coreNodes.mp inCore
      rcases eqn with rfl | ⟨side,rfl⟩
      · rw [core_length] at length
        omega
      · have half : address.length = depth/2 := by
          simp only [List.length_append,core_length,List.length_cons,List.length_nil] at length
          omega
        cases side
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨address,(mem_level _ _).mpr half,rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨address,(mem_level _ _).mpr half,rfl⟩)
    have bound := Finset.card_le_card subset
    have union := Finset.card_union_le
      ((level (depth/2)).image (fun address => core address ++ [false]))
      ((level (depth/2)).image (fun address => core address ++ [true]))
    have left := Finset.card_image_le (s := level (depth/2)) (f := fun address => core address ++ [false])
    have right := Finset.card_image_le (s := level (depth/2)) (f := fun address => core address ++ [true])
    rw [level_card] at left right
    rw [pow_succ]
    omega

/-- Distinct nodes of an interval hierarchy have distinct cut positions. -/
theorem cuts_injective {a b : Nat} (tree : DepthTree a b) {first second : DepthSplit}
    (firstMember : first ∈ tree.nodes) (secondMember : second ∈ tree.nodes)
    (same : first.cut = second.cut) : first = second := by
  have firstBounds := tree.node_bounds firstMember
  have secondBounds := tree.node_bounds secondMember
  have firstLocate := tree.locate_of_separates firstMember
    (show first.Separates first.cut (first.cut+1) from ⟨firstBounds.2.1,le_rfl,by omega,by omega⟩)
  have secondLocate := tree.locate_of_separates secondMember
    (show second.Separates first.cut (first.cut+1) from ⟨by omega,by omega,by omega,by omega⟩)
  exact Option.some.inj (firstLocate.symm.trans secondLocate)

theorem doubled_level_sum (height : Nat) :
    (∑ depth ∈ Finset.range (2*height), 2^(depth/2+1)) = 4*(2^height-1) := by
  induction height with
  | zero => simp
  | succ height ih =>
      rw [Nat.mul_add,Nat.mul_one,Finset.sum_range_succ,Finset.sum_range_succ,ih]
      have even : (2*height)/2 = height := by omega
      have odd : (2*height+1)/2 = height := by omega
      rw [even,odd,pow_succ]
      have positive : 0 < 2^height := Nat.pow_pos (by omega)
      omega

def coreRows {a b : Nat} (height : Nat) (tree : DepthTree a b) : Finset Secondary.Row :=
  (Secondary.rows tree).filter (fun row => row.2 ∈ coreNodes height)

theorem coreRows_card {height a b : Nat} (tree : DepthTree a b) (bounded : b ≤ 2*height) :
    (coreRows height tree).card ≤ 4*(2^height-1) := by
  have sigma : coreRows height tree = tree.nodes.sigma
      (fun split => (level split.lo).filter (fun owner => owner ∈ coreNodes height)) := by
    ext row
    simp [coreRows,Secondary.rows,and_assoc]
  rw [sigma,Finset.card_sigma]
  have levels := Finset.sum_le_sum (s := tree.nodes) (fun split _ => core_level_bound height split.lo)
  have cuts : (∑ split ∈ tree.nodes,2^(split.lo/2+1)) ≤ ∑ split ∈ tree.nodes,2^(split.cut/2+1) := by
    apply Finset.sum_le_sum
    intro split member
    have bounds := tree.node_bounds member
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have positions : tree.nodes.image DepthSplit.cut ⊆ Finset.range (2*height) := by
    intro cut member
    obtain ⟨split,source,rfl⟩ := Finset.mem_image.mp member
    have bounds := tree.node_bounds source
    simp only [Finset.mem_range]
    omega
  have full := Finset.sum_le_sum_of_subset (f := fun depth => 2^(depth/2+1)) positions
  rw [Finset.sum_image (fun _ ha _ hb same => cuts_injective tree ha hb same),doubled_level_sum] at full
  exact levels.trans (cuts.trans full)

end MultiSplay.EndpointEncoding
