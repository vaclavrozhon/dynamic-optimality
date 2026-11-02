import MultiSplay.Obstructions.ClassicalCounters
import MultiSplay.ClassicalSwitchSelected

/-! Perfect primary references and their actual maximum-node guards. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

 theorem right_follows (depth : Nat) : RootPreferred allRight (List.replicate depth true) := by
  induction depth with
  | zero => exact rootPreferred_nil _
  | succ depth ih =>
    rw [List.replicate_succ,rootPreferred_cons]
    exact ⟨rfl,ih⟩

 theorem preferred_perfect_size (height key : Nat) :
    (preferred allRight (perfect height key)).size = height := by
  induction height with
  | zero => rfl
  | succ height ih =>
    change 1+(preferred allRight (perfect height key)).size = height+1
    rw [ih]
    omega

private theorem upper_allRight (spine : Spine Nat) (right : ∀ entry ∈ spine, entry.1 = true) :
    spine.upper = .absent := by
  induction spine with
  | nil => rfl
  | cons entry spine ih =>
    obtain ⟨side,key⟩ := entry
    have same := right (side,key) (by simp)
    change side = true at same
    subst side
    exact ih (fun entry member => right entry (by simp [member]))

 theorem perfect_maximum_spine (depth key : Nat) :
    ∃ above : Spine Nat,
      referenceSpine (perfect (depth+2) key) (List.replicate (depth+1) true) = (true,key-1)::above ∧
      (∀ entry ∈ above, entry.1 = true) := by
  induction depth with
  | zero =>
    refine ⟨[],?_,by simp⟩
    have same : key+1-2 = key-1 := by omega
    simp [perfect,referenceSpine,same]
  | succ depth ih =>
    obtain ⟨above,same,right⟩ := ih
    refine ⟨above++[(true,key+1-2^(depth+2))],?_,?_⟩
    · change referenceSpine (perfect (depth+2) key) (List.replicate (depth+1) true) ++
        [(true,key+1-2^(depth+2))] = _
      rw [same]
      rfl
    · intro entry member
      rcases List.mem_append.mp member with member | member
      · exact right entry member
      · exact congrArg Prod.fst (List.mem_singleton.mp member)

/-- The root auxiliary's word and its nearest guard come from the perfect
primary reference, independently of the physical auxiliary shape. -/
 theorem maximum_reference_data (depth key : Nat) :
    ∃ frontKeys : List Nat, ∃ spine : Spine Nat,
      Path allRight (perfect (depth+2) key) (List.replicate (depth+1) true) spine
        (.node .empty key .empty) ∧
      spine.lower = .guard frontKeys (key-1) ∧ spine.upper = .absent ∧
      (preferred allRight (perfect (depth+2) key)).inorder = frontKeys++[key-1,key] ∧
      frontKeys.length = depth := by
  obtain ⟨above,spineEq,all⟩ := perfect_maximum_spine depth key
  have endpoint : referenceAt (perfect (depth+2) key) (List.replicate (depth+1) true) =
      .node .empty key .empty := perfect_maximum (depth+1) key
  have path := path_at allRight (perfect (depth+2) key) (List.replicate (depth+1) true)
    (right_follows _) (by rw [endpoint]; simp)
  rw [endpoint,spineEq] at path
  have upper : Spine.upper ((true,key-1)::above) = .absent :=
    upper_allRight ((true,key-1)::above) (by intro entry member; rcases List.mem_cons.mp member with rfl | member; rfl; exact all entry member)
  have word : (preferred allRight (perfect (depth+2) key)).inorder = above.lowerKeys++[key-1,key] := by
    rw [path.preferred_eq,Spine.inorder_plug]
    simp only [Spine.lowerKeys,preferred,restrict_eq,allRight,if_true,inorder,List.nil_append,
      List.append_nil,← Spine.upper_domain,upper,Boundary.upperKeys,List.append_assoc,List.singleton_append]
  have size := preferred_perfect_size (depth+2) key
  have length := congrArg List.length word
  simp only [length_inorder,List.length_append,List.length_cons,List.length_nil] at length
  exact ⟨above.lowerKeys,(true,key-1)::above,path,rfl,upper,word,by omega⟩

end MultiSplay.Obstructions.Classical
