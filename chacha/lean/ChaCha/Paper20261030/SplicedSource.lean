import ChaCha.Paper20261030.SuffixPortTransfer
import ChaCha.Paper20261030.HeadMemorySplice

/-!
# The reference tree after transferring a primary prefix

The persistent rule keeps records whose original interval starts at or
before `d`, and takes all later records from the incoming owner. Along
the path to `d`, this leaves the prepared directions unchanged. Every
left off-path subtree remains the old owner's whole subtree, and every
right off-path subtree becomes the incoming owner's whole subtree.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def splicedSource : {a b : Nat} → (reference : DepthTree a b) →
    (DepthSplit → Bool) → (DepthSplit → Bool) → (d : Nat) → a ≤ d ∧ d ≤ b → Source Nat Cached
  | _,_,.leaf a,_,_,_,_ => terminalLeaf a
  | a,b,.node cut ha hb l r,p,q,d,valid =>
      if left : d ≤ cut then
        .fork (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩)
          (splicedSource l p q d ⟨valid.1,left⟩) (source r q)
      else .fork (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩)
          (source l p) (splicedSource r p q d ⟨by omega,valid.2⟩)

theorem source_splice_before {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (before : b ≤ d) : source reference (Secondary.spliceBits d p q) = source reference p := by
  apply source_congr
  intro s hs
  have bounds := reference.node_bounds hs
  simp only [Secondary.spliceBits,if_pos (show s.lo ≤ d by omega)]

theorem source_splice_after {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (after : d < a) : source reference (Secondary.spliceBits d p q) = source reference q := by
  apply source_congr
  intro s hs
  have bounds := reference.node_bounds hs
  simp only [Secondary.spliceBits,if_neg (show ¬ s.lo ≤ d by omega)]

theorem source_splice {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    source reference (Secondary.spliceBits d p q) = splicedSource reference p q d valid := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    have bit : Secondary.spliceBits d p q ⟨a,cut,b⟩ = p ⟨a,cut,b⟩ := by
      simp only [Secondary.spliceBits,if_pos valid.1]
    by_cases left : d ≤ cut
    · simp only [source,bit,splicedSource,dif_pos left,ihl ⟨valid.1,left⟩,
        source_splice_after r p q d (by omega)]
    · simp only [source,bit,splicedSource,dif_neg left,ihr ⟨by omega,valid.2⟩,
        source_splice_before l p q d (by omega)]

theorem spliced_terminal {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) :
    terminalSource followsRight (splicedSource reference p q d valid) = terminalLeaf d := by
  induction reference with
  | leaf a =>
    have equal : a = d := by omega
    subst d
    rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using prepared
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      simpa only [splicedSource,dif_pos bounds.2,terminalSource,followsRight,bit,
        Bool.false_eq_true,if_false] using ihl bounds endpoint
    · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using prepared
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      simpa only [splicedSource,dif_neg (show ¬ d ≤ cut by omega),terminalSource,followsRight,bit,
        if_true] using ihr bounds endpoint

end ChaCha.Paper20261030.SecondaryDecomposition
