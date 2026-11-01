import TangoSquared.Paper20261030.GlobalPrimaryRoots

set_option autoImplicit false

/-! The finite primary leaf word indexes exactly the actual preferred-path
components. Every leaf is an endpoint of one component; distinct leaves
make its rooted subtree and starting depth unique. -/

namespace TangoSquared.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem leaf_in_exit {whole : PrefRouter α} {key : α}
    (member : key ∈ whole.leaves) (other : key ≠ whole.terminal) :
    ∃ exit ∈ exits whole, key ∈ exit.subtree.leaves := by
  induction whole with
  | leaf value =>
    simp only [PrefRouter.leaves,List.mem_singleton] at member
    exact False.elim (other member)
  | fork bit left right ihl ihr =>
    rcases List.mem_append.mp member with inLeft | inRight
    · cases bit
      · obtain ⟨exit,present,inside⟩ := ihl inLeft other
        exact ⟨exit,List.mem_cons_of_mem _ present,inside⟩
      · exact ⟨⟨true,left⟩,List.mem_cons_self,inLeft⟩
    · cases bit
      · exact ⟨⟨false,right⟩,List.mem_cons_self,inRight⟩
      · obtain ⟨exit,present,inside⟩ := ihr inRight other
        exact ⟨exit,List.mem_cons_of_mem _ present,inside⟩

theorem ComponentRoot.endpoint_exists {whole : PrefRouter α} {key : α}
    (member : key ∈ whole.leaves) :
    ∃ start subtree, ComponentRoot whole start subtree ∧ subtree.terminal = key := by
  by_cases endpoint : key = whole.terminal
  · exact ⟨0,whole,.root,endpoint.symm⟩
  · obtain ⟨exit,present,inside⟩ := leaf_in_exit member endpoint
    obtain ⟨depth,lookup⟩ := List.mem_iff_getElem?.mp present
    obtain ⟨inner,subtree,rooted,same⟩ := ComponentRoot.endpoint_exists inside
    have immediate : ComponentRoot whole (depth+1) exit.subtree := by
      have atDepth : portAt 0 (exits whole) depth = some exit := by simpa [portAt] using lookup
      simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot whole 0 whole) atDepth
    exact ⟨depth+1+inner,subtree,immediate.trans rooted,same⟩
termination_by whole.leaves.length
decreasing_by exact exit_smaller (by assumption)

theorem ComponentRoot.endpoint_exists_at_start {whole : PrefRouter α} {key : α}
    (distinct : whole.leaves.Nodup) (member : key ∈ whole.leaves) :
    ∃ subtree, ComponentRoot whole (whole.componentStart key) subtree ∧ subtree.terminal = key := by
  obtain ⟨start,subtree,rooted,endpoint⟩ := ComponentRoot.endpoint_exists member
  have atStart := rooted.endpoint_start distinct
  rw [endpoint] at atStart
  rw [atStart]
  exact ⟨subtree,rooted,endpoint⟩

end TangoSquared.Paper20261030.PrimaryWings
