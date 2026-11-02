import ChaCha.Paper20261030.SplayAuxiliarySpliceWords
import ChaCha.Paper20261030.SplayAuxiliaryReference

/-! The dormant suffix retains an ordered subword of the same actual
separator keys. Suppressing a unary reference vertex creates no new key. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open ColoredStorage SecondaryDecomposition

theorem referenceCuts_suffix_sublist {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) (valid : a ≤ sentinel ∧ sentinel ≤ b) :
    (referenceCuts cutKey (suffixSource reference preference sentinel valid)).inorder.Sublist
      (referenceCuts cutKey (source reference preference)).inorder := by
  induction reference with
  | leaf => exact .refl _
  | @node a b cut ha hb left right ihl ihr =>
      by_cases before : sentinel ≤ cut
      · simp only [suffixSource,dif_pos before,source,referenceCuts,MTR.Tree.inorder]
        exact ((ihl ⟨valid.1,before⟩).append (.refl _)).append (.refl _)
      · simp only [suffixSource,dif_neg before,source,referenceCuts,MTR.Tree.inorder]
        exact (ihr ⟨by omega,valid.2⟩).trans (List.sublist_append_right _ _)

theorem referenceCuts_source_ordered {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (referenceCuts cutKey (source reference preference)).Ordered := by
  change (referenceCuts secondaryKey (source reference preference)).Ordered
  rw [referenceCuts_secondary]
  exact (separatorReference reference).toRaw_ordered

theorem referenceCuts_suffix_ordered {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) (valid : a ≤ sentinel ∧ sentinel ≤ b) :
    (referenceCuts cutKey (suffixSource reference preference sentinel valid)).Ordered :=
  (referenceCuts_source_ordered reference preference).sublist
    (referenceCuts_suffix_sublist reference preference sentinel valid)

theorem referenceCuts_suffix_nodup {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) (valid : a ≤ sentinel ∧ sentinel ≤ b) :
    (referenceCuts cutKey (suffixSource reference preference sentinel valid)).inorder.Nodup :=
  (referenceCuts_suffix_ordered reference preference sentinel valid).imp (fun less => Nat.ne_of_lt less)

end ChaCha.Paper20261030.SplayAuxiliary
