import ChaCha.Paper20261030.SuffixDecomposition
import ChaCha.Paper20261030.HeadMemorySplice

/-!
# Prepared root-path records agree across owners

In a fixed reference, the preferred root path and all its stored bits
are determined by its endpoint. Thus two components prepared at the same
depth have equal full path words, although their off-path memories can be
different. Restriction keeps exactly the records at or above the sentinel.
-/

namespace ChaCha.Paper20261030.SeparatorPath

open PreferredProjection

theorem terminal_root_direction {a b cut : Nat} (ha : a ≤ cut) (hb : cut < b)
    (l : DepthTree a cut) (r : DepthTree (cut+1) b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth (.node cut ha hb l r) p).terminal = d) :
    p ⟨a,cut,b⟩ = decide (cut < d) := by
  cases bit : p ⟨a,cut,b⟩
  · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
      simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
    have bounds := (Secondary.decodeDepth_mem l p d).mp
      (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
    simp [show ¬ cut < d by omega]
  · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
      simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
    have bounds := (Secondary.decodeDepth_mem r p d).mp
      (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
    simp [show cut < d by omega]

theorem word_terminal_congr {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat)
    (before : (Secondary.decodeDepth reference p).terminal = d)
    (after : (Secondary.decodeDepth reference q).terminal = d) : word reference p = word reference q := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    have equal := (terminal_root_direction ha hb l r p d before).trans
      (terminal_root_direction ha hb l r q d after).symm
    cases bit : p ⟨a,cut,b⟩
    · have other : q ⟨a,cut,b⟩ = false := equal.symm.trans bit
      have leftP : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using before
      have leftQ : (Secondary.decodeDepth l q).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,other,Bool.false_eq_true,if_false] using after
      simp only [word,bit,other,Bool.false_eq_true,if_false,ihl leftP leftQ]
    · have other : q ⟨a,cut,b⟩ = true := equal.symm.trans bit
      have rightP : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using before
      have rightQ : (Secondary.decodeDepth r q).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,other,if_true] using after
      simp only [word,bit,other,if_true,ihr rightP rightQ]

end ChaCha.Paper20261030.SeparatorPath

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem prepared_suffix_word_agreement {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (before : (Secondary.decodeDepth reference p).terminal = d)
    (after : (Secondary.decodeDepth reference q).terminal = d)
    (active dormant : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (dormantRep : Represents followsRight (suffixSource reference q d valid) dormant) :
    dormant.core.toListModel = active.core.toListModel.filter (fun e => decide (d ≤ e.1)) := by
  rw [represented_suffix_word reference q d valid after dormant dormantRep,
    represented_word reference p active activeRep,List.filter_map]
  rw [SeparatorPath.word_terminal_congr reference p q d before after]
  rfl

/-- The genuine suffix has different owners; only the boundary path's
record values agree. This theorem makes no assertion that attached
subtrees or tail memory agree. -/
theorem prepared_boundary_payload_agreement {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (before : (Secondary.decodeDepth reference p).terminal = d)
    (after : (Secondary.decodeDepth reference q).terminal = d)
    (active dormant : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (dormantRep : Represents followsRight (suffixSource reference q d valid) dormant)
    (upper : d < b) :
    let fa := prepared_upper_found reference p d before upper active activeRep
    let fd := represented_suffix_boundary_found reference q d valid after upper dormant dormantRep
    (splitAt d active.core active.balanced fa).value =
      (splitAt d dormant.core dormant.balanced fd).value := by
  dsimp only
  let fa := prepared_upper_found reference p d before upper active activeRep
  let fd := represented_suffix_boundary_found reference q d valid after upper dormant dormantRep
  let pivot : Sigma (Tagged Payload) := ⟨d,(splitAt d dormant.core dormant.balanced fd).value⟩
  have inDormant : pivot ∈ dormant.core.toListModel := split_pivot_mem dormant d fd
  have inActive : pivot ∈ active.core.toListModel := by
    rw [prepared_suffix_word_agreement reference p q d valid before after active dormant activeRep dormantRep] at inDormant
    exact (List.mem_filter.mp inDormant).1
  obtain ⟨pre,post,word⟩ := List.mem_iff_append.mp inActive
  have decomp := splitAt_word_decomposition active.core active.balanced
    (represented_ordered reference p active activeRep) pre post pivot word fa
  have equal := decomp.2.1
  exact eq_of_heq (Sigma.mk.inj equal).2

end ChaCha.Paper20261030.SecondaryDecomposition
