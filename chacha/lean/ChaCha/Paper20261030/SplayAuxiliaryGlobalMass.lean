import ChaCha.Paper20261030.SplayAuxiliaryGlobalPotential
import ChaCha.Paper20261030.SplayAuxiliaryPayload

/-!
# Linear total size of the persistent secondary forest

The primary paths partition the internal reference vertices. A dormant
path adds at most one sentinel. Consequently the whole collection of
secondary auxiliaries has fewer than twice as many separators as original
keys; bounding each path separately by the universe height is unnecessary.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage PreferredProjection Secondary SecondaryDecomposition

variable {α ρ κ : Type*}

theorem referenceCuts_map (key : ρ → κ) (reference : Source α ρ) :
    referenceCuts id (reference.mapRecords key) = referenceCuts key reference := by
  induction reference <;> simp_all [Source.mapRecords,referenceCuts]

theorem represented_mass {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {component : RawComponent α κ}
    (represented : Decomposition.Represents key right reference component) :
    (referenceCuts id component.closed).size = (referenceCuts key reference).size := by
  have lengths := congrArg List.length (represented_leafPayloads represented)
  simp only [leafPayloads_length,referenceCuts_map] at lengths
  omega

theorem referenceCuts_source_size {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    (referenceCuts cutKey (source reference p)).size = b-a := by
  induction reference with
  | leaf => simp [source,referenceCuts,MTR.Tree.size]
  | node cut ha hb left right ihl ihr =>
      simp only [source,referenceCuts,MTR.Tree.size,ihl,ihr]
      omega

theorem referenceCuts_suffix_size {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (sentinel : Nat) (valid : a ≤ sentinel ∧ sentinel ≤ b) :
    (referenceCuts cutKey (suffixSource reference p sentinel valid)).size = b-sentinel := by
  induction reference with
  | leaf => simp only [suffixSource,terminalLeaf,referenceCuts,MTR.Tree.size]; omega
  | @node a b cut ha hb left right ihl ihr =>
      simp only [suffixSource]
      split
      · simp only [referenceCuts,MTR.Tree.size,ihl,referenceCuts_source_size]
        omega
      · exact ihr _

variable [DecidableEq α]

private theorem fork_path_mass (bit : Bool) (left right : PrefRouter α)
    (distinct : (left.leaves++right.leaves).Nodup) (height : Nat) (key : α) :
    height+1-(PrefRouter.fork bit left right).componentStart key =
      (if key ∈ left.leaves then height-left.componentStart key else height-right.componentStart key) +
        (if key = (PrefRouter.fork bit left right).terminal then 1 else 0) := by
  by_cases endpoint : key = (PrefRouter.fork bit left right).terminal
  · subst key
    cases bit
    · simp [PrefRouter.componentStart,PrefRouter.terminal,left.terminal_mem,
        PrefRouter.componentStart_terminal]
    · have outside : right.terminal ∉ left.leaves :=
        fun member => (List.nodup_append.mp distinct).2.2 _ member _ right.terminal_mem rfl
      simp [PrefRouter.componentStart,PrefRouter.terminal,outside,PrefRouter.componentStart_terminal]
  · simp only [PrefRouter.componentStart,if_neg endpoint]
    split_ifs <;> omega

theorem primary_path_mass {height : Nat} {primary : PrefRouter α}
    (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup) :
    primary.leaves.toFinset.sum (fun key => height-primary.componentStart key) = primary.internalVertices := by
  induction height generalizing primary with
  | zero =>
      cases primary with
      | leaf => simp [PrefRouter.leaves,PrefRouter.componentStart,PrefRouter.internalVertices]
      | fork => exact False.elim perfect
  | succ height ih =>
      cases primary with
      | leaf => exact False.elim perfect
      | fork bit left right =>
          obtain ⟨dl,dr,separate⟩ := List.nodup_append.mp distinct
          have disjoint : Disjoint left.leaves.toFinset right.leaves.toFinset := by
            apply Finset.disjoint_left.mpr
            intro key inLeft inRight
            exact separate _ (List.mem_toFinset.mp inLeft) _ (List.mem_toFinset.mp inRight) rfl
          have sums : (left.leaves++right.leaves).toFinset.sum
              (fun key => if key ∈ left.leaves then height-left.componentStart key
                else height-right.componentStart key) =
              left.leaves.toFinset.sum (fun key => height-left.componentStart key) +
              right.leaves.toFinset.sum (fun key => height-right.componentStart key) := by
            rw [List.toFinset_append,Finset.sum_union disjoint]
            congr 1
            · apply Finset.sum_congr rfl
              intro key member
              simp only [if_pos (List.mem_toFinset.mp member)]
            · apply Finset.sum_congr rfl
              intro key member
              have outside : key ∉ left.leaves :=
                fun inside => separate _ inside _ (List.mem_toFinset.mp member) rfl
              simp only [if_neg outside]
          have one : (left.leaves++right.leaves).toFinset.sum
              (fun key => if key = (PrefRouter.fork bit left right).terminal then 1 else 0) = 1 := by
            rw [Finset.sum_ite_eq']
            exact if_pos (List.mem_toFinset.mpr
              (PrefRouter.terminal_mem (PrefRouter.fork bit left right)))
          calc
            _ = (left.leaves++right.leaves).toFinset.sum
                (fun key => (if key ∈ left.leaves then height-left.componentStart key
                  else height-right.componentStart key) +
                  (if key = (PrefRouter.fork bit left right).terminal then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro key _
              exact fork_path_mass bit left right distinct height key
            _ = _ := by
              rw [Finset.sum_add_distrib,sums,one,ih perfect.1 dl,ih perfect.2 dr]
              rfl

theorem primary_path_mass_with_sentinels {height : Nat} {primary : PrefRouter α}
    (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup) :
    primary.leaves.toFinset.sum (fun key => height-primary.componentStart key+1)+1 =
      2*primary.leaves.length := by
  have ones : primary.leaves.toFinset.sum (fun _ => (1 : Nat)) = primary.leaves.length := by
    simp [List.toFinset_card_of_nodup distinct]
  rw [Finset.sum_add_distrib,primary_path_mass perfect distinct,ones]
  have vertices := primary.internal_vertices_leaves
  omega

theorem componentSource_size_bound {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (memory : MemoryKey → Bool) (key : α) :
    (referenceCuts cutKey (componentSource reference primary perfect memory key)).size ≤
      height-primary.componentStart key+1 := by
  unfold componentSource
  split
  · subst key
    simp only [referenceCuts_source_size,Nat.sub_zero,PrefRouter.componentStart_terminal]
    omega
  · rw [referenceCuts_suffix_size]
    have bounded := PrefRouter.componentStart_le_height perfect key
    omega

theorem componentSource_height_bound {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (memory : MemoryKey → Bool) (key : α) :
    (componentSource reference primary perfect memory key).shape.height ≤
      (LocalReferences.depthReference reference).height := by
  unfold componentSource
  split
  · rw [source_shape]
  · exact suffixSource_height _ _ _ _

namespace Global

theorem Component.Valid.mass {reference : Source Nat Cached} {component : Component}
    (valid : component.Valid reference) :
    forestSize component.trees = (referenceCuts cutKey reference).size :=
  (core_mass valid.2).trans (represented_mass valid.1)

theorem Table.Valid.potential_bound {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Table α)
    (valid : Table.Valid reference primary perfect memory components) :
    components.potential primary.leaves.toFinset ≤
      2*primary.leaves.length * Nat.log 2 (LocalReferences.depthReference reference).height := by
  have componentBound : ∀ key ∈ primary.leaves.toFinset, (components key).potential ≤
      (height-primary.componentStart key+1)*Nat.log 2 (LocalReferences.depthReference reference).height := by
    intro key member
    have represented := valid key (List.mem_toFinset.mp member)
    have bounded := represented.potential_bound
    rw [represented_mass represented.1] at bounded
    exact bounded.trans (Nat.mul_le_mul
      (componentSource_size_bound reference primary perfect memory key)
      (Nat.log_mono_right (componentSource_height_bound reference primary perfect memory key)))
  have bound := Finset.sum_le_sum componentBound
  rw [← Finset.sum_mul] at bound
  have mass := primary_path_mass_with_sentinels perfect distinct
  exact bound.trans (Nat.mul_le_mul_right _ (by omega))

end Global
end ChaCha.Paper20261030.SplayAuxiliary
