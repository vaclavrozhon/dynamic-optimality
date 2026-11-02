import DynamicOptimality.MultiFinger.RegionBoundary
import DynamicOptimality.MultiFinger.TendonEndpoints

/-! All four deque endpoints are bounded consecutive-marker regions.
The retained interior may contain arbitrarily many markers. Only its
first or last opaque gap participates in the actual deque kernel. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR SearchRotation
open Pointer (MarkedTree)
open GeometricOnlineSimulation.OpenDeque
open TendonContents TendonSource

variable {α : Type*}

theorem low_first_region (before after : Option (Right α))
    (gap : RawTree α) (key : α) (inside : MarkedTree α) {count : Nat}
    (actual : Rotations (lowFill before (firstHole inside))
      (.node gap key (lowFill after (firstHole inside))) count) :
    RegionStep (lowMarked before inside) (.node (.hole gap) key (lowMarked after inside)) count := by
  apply prefix_region (lowMarked before) (fun inner => .node (.hole gap) key (lowMarked after inner))
    (lowKeys before) ([key]++lowKeys after) (lowHoles before) ([gap]++lowHoles after)
  · exact lowMarked_word before
  · intro inner; simp [MarkedTree.skeleton,Tree.inorder,lowMarked_word,List.append_assoc]
  · exact lowMarked_holes before
  · intro inner; simp [MarkedTree.holes,lowMarked_holes,List.append_assoc]
  · have size := lowMarked_size before (.hole (firstHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · have size := lowMarked_size after (.hole (firstHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size ⊢
    omega
  · simpa only [MarkedTree.erase,lowMarked_erase] using actual

theorem low_last_region (before after : Option (Right α))
    (gap : RawTree α) (key : α) (inside : MarkedTree α) {count : Nat}
    (actual : Rotations (lowFill before (firstHole inside))
      (.node (lowFill after gap) key (firstHole inside)) count) :
    RegionStep (lowMarked before inside) (.node (lowMarked after (.hole gap)) key inside) count := by
  apply prefix_region (lowMarked before) (fun inner => .node (lowMarked after (.hole gap)) key inner)
    (lowKeys before) (lowKeys after++[key]) (lowHoles before) (lowHoles after++[gap])
  · exact lowMarked_word before
  · intro inner; simp [MarkedTree.skeleton,Tree.inorder,lowMarked_word,List.append_assoc]
  · exact lowMarked_holes before
  · intro inner; simp [MarkedTree.holes,lowMarked_holes,List.append_assoc]
  · have size := lowMarked_size before (.hole (firstHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · have size := lowMarked_size after (.hole gap)
    simp only [MarkedTree.skeleton,Tree.size] at size ⊢
    omega
  · simpa only [MarkedTree.erase,lowMarked_erase] using actual

theorem high_first_region (before after : Option (Left α))
    (gap : RawTree α) (key : α) (inside : MarkedTree α) {count : Nat}
    (actual : Rotations (highFill before (lastHole inside))
      (.node (lastHole inside) key (highFill after gap)) count) :
    RegionStep (highMarked before inside) (.node inside key (highMarked after (.hole gap))) count := by
  apply suffix_region (highMarked before) (fun inner => .node inner key (highMarked after (.hole gap)))
    (highKeys before) ([key]++highKeys after) (highHoles before) ([gap]++highHoles after)
  · exact highMarked_word before
  · intro inner; simp [MarkedTree.skeleton,Tree.inorder,highMarked_word,List.append_assoc]
  · exact highMarked_holes before
  · intro inner; simp [MarkedTree.holes,highMarked_holes,List.append_assoc]
  · have size := highMarked_size before (.hole (lastHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · have size := highMarked_size after (.hole gap)
    simp only [MarkedTree.skeleton,Tree.size] at size ⊢
    omega
  · simpa only [MarkedTree.erase,highMarked_erase] using actual

theorem high_last_region (before after : Option (Left α))
    (gap : RawTree α) (key : α) (inside : MarkedTree α) {count : Nat}
    (actual : Rotations (highFill before (lastHole inside))
      (.node (highFill after (lastHole inside)) key gap) count) :
    RegionStep (highMarked before inside) (.node (highMarked after inside) key (.hole gap)) count := by
  apply suffix_region (highMarked before) (fun inner => .node (highMarked after inner) key (.hole gap))
    (highKeys before) (highKeys after++[key]) (highHoles before) (highHoles after++[gap])
  · exact highMarked_word before
  · intro inner; simp [MarkedTree.skeleton,Tree.inorder,highMarked_word,List.append_assoc]
  · exact highMarked_holes before
  · intro inner; simp [MarkedTree.holes,highMarked_holes,List.append_assoc]
  · have size := highMarked_size before (.hole (lastHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · have size := highMarked_size after (.hole (lastHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size ⊢
    omega
  · simpa only [MarkedTree.erase,highMarked_erase] using actual

theorem low_last_insert_region (before after : Option (Right α))
    (gap : RawTree α) (key : α) (inside : MarkedTree α) {count : Nat}
    (actual : Rotations (lowFill before (.node gap key (firstHole inside)))
      (lowFill after (firstHole inside)) count) :
    RegionStep (lowMarked before (.node (.hole gap) key inside)) (lowMarked after inside) count := by
  apply prefix_region (fun inner => lowMarked before (.node (.hole gap) key inner)) (lowMarked after)
    (lowKeys before++[key]) (lowKeys after) (lowHoles before++[gap]) (lowHoles after)
  · intro inner; simp [MarkedTree.skeleton,Tree.inorder,lowMarked_word,List.append_assoc]
  · exact lowMarked_word after
  · intro inner; simp [MarkedTree.holes,lowMarked_holes,List.append_assoc]
  · exact lowMarked_holes after
  · have size := lowMarked_size before (.node (.hole gap) key (.hole (firstHole inside)))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · have size := lowMarked_size after (.hole (firstHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · simpa only [MarkedTree.erase,lowMarked_erase] using actual

theorem high_first_insert_region (before after : Option (Left α))
    (gap : RawTree α) (key : α) (inside : MarkedTree α) {count : Nat}
    (actual : Rotations (highFill before (.node (lastHole inside) key gap))
      (highFill after (lastHole inside)) count) :
    RegionStep (highMarked before (.node inside key (.hole gap))) (highMarked after inside) count := by
  apply suffix_region (fun inner => highMarked before (.node inner key (.hole gap))) (highMarked after)
    ([key]++highKeys before) (highKeys after) ([gap]++highHoles before) (highHoles after)
  · intro inner; simp [MarkedTree.skeleton,Tree.inorder,highMarked_word,List.append_assoc]
  · exact highMarked_word after
  · intro inner; simp [MarkedTree.holes,highMarked_holes,List.append_assoc]
  · exact highMarked_holes after
  · have size := highMarked_size before (.node (.hole (lastHole inside)) key (.hole gap))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · have size := highMarked_size after (.hole (lastHole inside))
    simp only [MarkedTree.skeleton,Tree.size] at size
    omega
  · simpa only [MarkedTree.erase,highMarked_erase] using actual

end DynamicOptimality.MultiFinger
