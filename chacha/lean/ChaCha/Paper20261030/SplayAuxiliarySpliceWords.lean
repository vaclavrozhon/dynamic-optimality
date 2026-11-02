import ChaCha.Paper20261030.SplayAuxiliarySplice
import ChaCha.Paper20261030.PreparedPrefixJoin

/-!
# Exact separator words for arbitrary-shape suffix and splice outputs

These lemmas let the physical implementation establish the invariant by
checking the resulting inorder keys and gap payloads. They reuse the same
reference restriction and persistent-memory splice as the balanced proof.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open PreferredProjection ColoredStorage SecondaryDecomposition RawComponent Decomposition

theorem skeleton_keys {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    (PathPorts.skeleton followsRight (source reference p)).inorder.map cutKey =
      (SeparatorPath.word reference p).map (fun e => e.1) := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
      cases bit : p ⟨a,cut,b⟩ <;>
        simp [source,PathPorts.skeleton,followsRight,bit,MTR.Tree.inorder,
          SeparatorPath.word,cutKey,ihl,ihr]

theorem represented_keys {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (source reference p) c) :
    c.core.inorder = (SeparatorPath.word reference p).map (fun e => e.1) := by
  rw [represented.word,skeleton_keys]

theorem suffix_skeleton_keys {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) :
    (PathPorts.skeleton followsRight (suffixSource reference p d valid)).inorder.map cutKey =
      ((SeparatorPath.word reference p).filter (fun e => decide (d ≤ e.1))).map (fun e => e.1) := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
      cases bit : p ⟨a,cut,b⟩
      · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using prepared
        have bounds := (Secondary.decodeDepth_mem l p d).mp
          (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
        have child := ihl bounds endpoint
        simpa [suffixSource,bounds.2,PathPorts.skeleton,followsRight,bit,MTR.Tree.inorder,
          SeparatorPath.word,cutKey] using congrArg (fun word => word ++ [cut]) child
      · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using prepared
        have bounds := (Secondary.decodeDepth_mem r p d).mp
          (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
        have notLeft : ¬ d ≤ cut := by omega
        simpa [suffixSource,notLeft,SeparatorPath.word,bit] using ihr bounds endpoint

theorem represented_suffix_keys {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d)
    {c : RawComponent Nat Nat}
    (represented : Represents cutKey followsRight (suffixSource reference p d valid) c) :
    c.core.inorder = ((SeparatorPath.word reference p).map (fun e => e.1)).filter
      (fun key => decide (d ≤ key)) := by
  rw [represented.word,suffix_skeleton_keys reference p d valid prepared,List.filter_map]
  rfl

/-- Any actual suffix with these keys and ports realizes the same restricted
reference. The hypotheses can be supplied by ordinary splay splitting. -/
theorem suffix_represents_of_words {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d)
    (active suffix : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (word : suffix.core.inorder = active.core.inorder.filter (fun key => decide (d ≤ key)))
    (ports : suffix.portWord = active.portWord.drop
      (PathDecomposition.terminalIndex followsRight (source reference p))) :
    Represents cutKey followsRight (suffixSource reference p d valid) suffix := by
  obtain ⟨semantic,represented,semanticPorts⟩ :=
    suffixRepresentative_exists reference p d valid prepared active activeRep
  apply represented.equivalent
  apply equivalent_of_words
  · rw [word,represented_keys reference p activeRep,
      represented_suffix_keys reference p d valid prepared represented]
  · exact ports.trans semanticPorts.symm

/-- Prefix/suffix exchange preserves the full prepared root word, while
replacing exactly the specified suffix of its physical port list. -/
theorem splice_represents_of_words {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming out : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight (suffixSource reference q d valid) incoming)
    (word : out.core.inorder = active.core.inorder)
    (ports : out.portWord = active.portWord.take
      (PathDecomposition.terminalIndex followsRight (source reference p)) ++ incoming.portWord) :
    Represents cutKey followsRight (source reference (Secondary.spliceBits d p q)) out := by
  obtain ⟨semantic,represented,semanticPorts⟩ :=
    splicedRepresentative_exists reference p q d valid preparedP preparedQ active incoming activeRep incomingRep
  rw [← source_splice] at represented
  apply represented.equivalent
  apply equivalent_of_words
  · rw [word,represented_keys reference p activeRep,
      represented_keys reference (Secondary.spliceBits d p q) represented]
    rw [SeparatorPath.word_terminal_congr reference p (Secondary.spliceBits d p q) d preparedP
      (splice_prepared_terminal reference p q d valid preparedP)]
  · exact ports.trans semanticPorts.symm

end ChaCha.Paper20261030.SplayAuxiliary
