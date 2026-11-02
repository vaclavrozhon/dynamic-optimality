import ChaCha.Paper20261030.SplayAuxiliaryPreparedTerminal
import ChaCha.Paper20261030.SplayAuxiliaryExposure

/-! Expose the dormant sentinel with the ordinary splay algorithm. The
sentinel port is the same actual original leaf, including its key. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection
open MultiSplay.Auxiliary

 theorem prepared_suffix_port {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (suffixSource reference p d valid) c) :
    c.ports 0 = .leaf d d := by
  have port := represented_terminal_port represented
  obtain ⟨index,leaf⟩ := suffixSource_terminalIndex reference p d valid prepared
  rw [index,leaf] at port
  exact port

 theorem prepared_suffix_minimum {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (suffixSource reference p d valid) c) :
    ∀ key ∈ c.core.inorder, d ≤ key := by
  intro key member
  rw [represented_suffix_keys reference p d valid prepared represented] at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

 theorem prepared_suffix_member {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (suffixSource reference p d valid) c) :
    d ∈ c.core.inorder := by
  obtain ⟨entry,present,key⟩ := SeparatorPath.terminal_upper_separator reference p d prepared upper
  rw [represented_suffix_keys reference p d valid prepared represented]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨entry,present,key⟩,by simp⟩

/-- The output remains the same dormant component, and its first port is
literally the original terminal. Only the root auxiliary is splayed. -/
theorem prepared_suffix_expose {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b)
    (c : RawComponent Nat Nat)
    (represented : Represents cutKey followsRight (suffixSource reference p d valid) c) :
    ∃ tail : RawTree Nat, ∃ work : Nat,
      Splay d c.core (.node .empty d tail) work ∧
      Represents cutKey followsRight (suffixSource reference p d valid) ⟨.node .empty d tail,c.ports⟩ ∧
      SourcePointer.Rearranges c.closed (.fork d (.leaf d d) (GapSource.encode tail c.ports 1))
        (3*work+1) ∧
      work+2*potential (.node .empty d tail) ≤
        2*potential c.core+6*Nat.log 2 (LocalReferences.depthReference reference).height+1 := by
  have ordered := represented_core_ordered represented (referenceCuts_suffix_ordered reference p d valid)
  have unique := ordered.imp (fun less => Nat.ne_of_lt less)
  have minimum := prepared_suffix_minimum reference p d valid prepared represented
  obtain ⟨after,work,execution,physical⟩ := exists_pointer_splay
    (prepared_suffix_member reference p d valid prepared upper represented)
  cases after with
  | empty => have impossible := execution.root_after; cases impossible
  | node left pivot tail =>
      have key : pivot = d := Option.some.inj execution.root_after
      subst pivot
      have empty : left = .empty := by
        cases left with
        | empty => rfl
        | node ll key lr =>
            have afterOrdered := execution.ordered_after ordered
            have leftLt := (List.pairwise_append.mp (List.pairwise_append.mp afterOrdered).1).2.2
            have less : key < d := leftLt key (by simp [MTR.Tree.inorder]) d (by simp)
            have present : key ∈ c.core.inorder := by
              rw [execution.inorder_eq]
              simp [MTR.Tree.inorder]
            have greater := minimum key present
            omega
      subst left
      have same : Equivalent ⟨.node .empty d tail,c.ports⟩ c :=
        ⟨execution.inorder_eq.symm,fun _ _ => rfl⟩
      have trace := splay_source_rearranges execution unique c.ports
      have port := prepared_suffix_port reference p d valid prepared represented
      simp only [GapSource.encode,MTR.Tree.size,Nat.zero_add,port] at trace
      exact ⟨tail,work,execution,represented.equivalent same,trace,
        splay_amortized_capacity execution unique
          (represented.size_height.trans (suffixSource_height reference p d valid))⟩

end ChaCha.Paper20261030.SplayAuxiliary
