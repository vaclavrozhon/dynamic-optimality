import ChaCha.Paper20261030.PackedPortAgreement

/-! Distinct original keys make the actual primary exit list distinct.
Consequently overriding a boundary payload cannot alter any other depth
port of the same primary component. -/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α β : Type*} [DecidableEq α]

theorem exit_leaves_subset {primary : PrefRouter α} {exit : Exit α}
    (member : exit ∈ exits primary) : ∀ key ∈ exit.subtree.leaves, key ∈ primary.leaves := by
  induction primary with
  | leaf key => simp [exits] at member
  | fork bit left right ihl ihr =>
    cases bit <;> simp only [exits,List.mem_cons] at member
    · rcases member with rfl | member
      · exact fun key hk => List.mem_append_right _ hk
      · exact fun key hk => List.mem_append_left _ (ihl member key hk)
    · rcases member with rfl | member
      · exact fun key hk => List.mem_append_left _ hk
      · exact fun key hk => List.mem_append_right _ (ihr member key hk)

theorem exits_nodup {primary : PrefRouter α} (distinct : primary.leaves.Nodup) : (exits primary).Nodup := by
  induction primary with
  | leaf key => simp [exits]
  | fork bit left right ihl ihr =>
    obtain ⟨dl,dr,disjoint⟩ := List.nodup_append.mp distinct
    cases bit
    · apply List.nodup_cons.mpr
      refine ⟨?_,ihl dl⟩
      intro member
      have inside := exit_leaves_subset member right.terminal right.terminal_mem
      exact disjoint _ inside _ right.terminal_mem rfl
    · apply List.nodup_cons.mpr
      refine ⟨?_,ihr dr⟩
      intro member
      have inside := exit_leaves_subset member left.terminal left.terminal_mem
      exact disjoint _ left.terminal_mem _ inside rfl

theorem portAt_boundary (common tail : List β) (boundary : β) :
    portAt 0 (common ++ boundary :: tail) common.length = some boundary := by
  simp [portAt]

theorem portAt_ne_boundary (common tail : List β) (boundary : β)
    (distinct : (common ++ boundary :: tail).Nodup) (depth : Nat) (different : depth ≠ common.length)
    (exit : β) (present : portAt 0 (common ++ boundary :: tail) depth = some exit) : exit ≠ boundary := by
  intro same
  subst exit
  have boundaryPresent := portAt_boundary common tail boundary
  simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero] at present boundaryPresent
  have depthBound : depth < (common ++ boundary :: tail).length := List.getElem?_eq_some_iff.mp present |>.1
  have boundaryBound : common.length < (common ++ boundary :: tail).length := by simp
  have depthValue := List.getElem?_eq_some_iff.mp present |>.2
  have boundaryValue := List.getElem?_eq_some_iff.mp boundaryPresent |>.2
  exact different ((List.Nodup.getElem_inj_iff distinct).mp (depthValue.trans boundaryValue.symm))

end ChaCha.Paper20261030.PrimaryWings
