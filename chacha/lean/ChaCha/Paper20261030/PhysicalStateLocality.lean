import ChaCha.Paper20261030.MaintainedPhysicalState

/-! The complete expansion depends only on the component records and
start depths belonging to endpoints inside its original-key subtree. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

theorem storedTree_congr (beforeStarts afterStarts : α → Nat)
    (beforeComponents afterComponents : Components α) (subtree : PrefRouter α)
    (startsSame : ∀ key ∈ subtree.leaves, beforeStarts key = afterStarts key)
    (componentsSame : ∀ key ∈ subtree.leaves, beforeComponents key = afterComponents key) :
    storedTree beforeStarts beforeComponents subtree = storedTree afterStarts afterComponents subtree := by
  have planSame : storedPlan beforeStarts beforeComponents subtree = storedPlan afterStarts afterComponents subtree := by
    simp only [storedPlan,startsSame _ subtree.terminal_mem,componentsSame _ subtree.terminal_mem]
  have headerSame : storedHeader beforeStarts beforeComponents subtree = storedHeader afterStarts afterComponents subtree := by
    simp only [storedHeader,startsSame _ subtree.terminal_mem,componentsSame _ subtree.terminal_mem]
  have payloadSame :
      (fun e => if member : e ∈ exits subtree then storedTree beforeStarts beforeComponents e.subtree
        else Source.leaf subtree.terminal []) =
      (fun e => if member : e ∈ exits subtree then storedTree afterStarts afterComponents e.subtree
        else Source.leaf subtree.terminal []) := by
    funext e
    split_ifs with member
    · exact storedTree_congr beforeStarts afterStarts beforeComponents afterComponents e.subtree
        (fun key h => startsSame key (exit_leaves_subset member key h))
        (fun key h => componentsSame key (exit_leaves_subset member key h))
    · rfl
  change PrimaryPhysical.expand _ _ subtree = PrimaryPhysical.expand _ _ subtree
  rw [PrimaryPhysical.expand,PrimaryPhysical.expand]
  change PrimaryPhysical.component (graftWing _ _) (graftWing _ _) _ _ =
    PrimaryPhysical.component (graftWing _ _) (graftWing _ _) _ _
  dsimp only [storedTree] at payloadSame
  rw [payloadSame,planSame,headerSame]
termination_by subtree.leaves.length
decreasing_by exact exit_smaller (by assumption)

end ChaCha.Paper20261030.SecondaryDecomposition

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem exit_excludes_terminal {primary : PrefRouter α} {exit : Exit α}
    (distinct : primary.leaves.Nodup) (member : exit ∈ exits primary) :
    primary.terminal ∉ exit.subtree.leaves := by
  intro inside
  obtain ⟨depth,present⟩ := List.mem_iff_getElem?.mp member
  have start := port_componentStart distinct
    (show portAt 0 (exits primary) depth = some exit by simpa [portAt] using present) inside
  rw [PrefRouter.componentStart_terminal] at start
  omega

theorem exit_leaves_disjoint {primary : PrefRouter α} (distinct : primary.leaves.Nodup)
    {a b : Exit α} (first : a ∈ exits primary) (second : b ∈ exits primary) (different : a ≠ b) :
    ∀ key ∈ a.subtree.leaves, key ∉ b.subtree.leaves := by
  induction primary with
  | leaf value => simp [exits] at first
  | fork bit left right ihl ihr =>
    obtain ⟨dl,dr,disjoint⟩ := List.nodup_append.mp distinct
    cases bit <;> simp only [exits,List.mem_cons] at first second
    · rcases first with rfl | first <;> rcases second with rfl | second
      · exact False.elim (different rfl)
      · intro key hr hl
        exact disjoint _ (exit_leaves_subset second key hl) _ hr rfl
      · intro key hl hr
        exact disjoint _ (exit_leaves_subset first key hl) _ hr rfl
      · exact ihl dl first second
    · rcases first with rfl | first <;> rcases second with rfl | second
      · exact False.elim (different rfl)
      · intro key hl hr
        exact disjoint _ hl _ (exit_leaves_subset second key hr) rfl
      · intro key hr hl
        exact disjoint _ hl _ (exit_leaves_subset first key hr) rfl
      · exact ihr dr first second

end ChaCha.Paper20261030.PrimaryWings
