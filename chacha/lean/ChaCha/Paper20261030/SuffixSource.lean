import ChaCha.Paper20261030.PreparedSeparators
import ChaCha.Paper20261030.PreparedRightWing
import ChaCha.Paper20261030.DormantPreferences

/-!
# Restricted secondary sources retain original reference records

`suffixSource` is the actual restriction to depths at least its sentinel,
with empty children deleted and unary reference vertices suppressed.
Surviving vertices keep their original split intervals and preferences.
Its decoding agrees with the already checked preferred-tree restriction;
no new compactly reindexed depth reference is substituted for it.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def suffixSource : {a b : Nat} → (reference : DepthTree a b) →
    (DepthSplit → Bool) → (sentinel : Nat) → a ≤ sentinel ∧ sentinel ≤ b → Source Nat Cached
  | _,_,.leaf a,_,_,_ => terminalLeaf a
  | a,b,.node cut ha hb l r,p,d,valid =>
      if left : d ≤ cut then
        .fork (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩)
          (suffixSource l p d ⟨valid.1,left⟩) (source r p)
      else suffixSource r p d ⟨by omega,valid.2⟩

theorem suffixSource_raw {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) : Raw (suffixSource reference p d valid) := by
  induction reference with
  | leaf => rfl
  | node cut ha hb l r ihl ihr =>
    simp only [suffixSource]
    split
    · exact ⟨rfl,ihl _,source_raw r p⟩
    · exact ihr _

theorem suffixSource_decode {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (Secondary.decodeDepth reference p).prune (Secondary.suffixKeep d) =
      some (decodeSource (suffixSource reference p d valid)) := by
  induction reference with
  | leaf a =>
    have equal : a = d := by omega
    subst d
    simp [Secondary.decodeDepth,PrefRouter.prune,Secondary.suffixKeep,suffixSource,terminalLeaf,decodeSource]
  | @node a b cut ha hb l r ihl ihr =>
    by_cases left : d ≤ cut
    · have retained : (Secondary.decodeDepth r p).prune (Secondary.suffixKeep d) =
          some (Secondary.decodeDepth r p) := by
        apply PrefRouter.prune_of_all_true
        intro key mem
        have bounds := (Secondary.decodeDepth_mem r p key).mp mem
        simp only [Secondary.suffixKeep,decide_eq_true_eq]
        omega
      simp only [Secondary.decodeDepth,PrefRouter.prune,ihl ⟨valid.1,left⟩,retained,
        PrefRouter.combine,suffixSource,dif_pos left,decodeSource,followsRight,decodeSource_source]
    · have deleted : (Secondary.decodeDepth l p).prune (Secondary.suffixKeep d) = none := by
        apply PrefRouter.prune_of_all_false
        intro key mem
        have bounds := (Secondary.decodeDepth_mem l p key).mp mem
        simp only [Secondary.suffixKeep,decide_eq_false_iff_not]
        omega
      simp only [Secondary.decodeDepth,PrefRouter.prune,deleted,ihr ⟨by omega,valid.2⟩,
        PrefRouter.combine,suffixSource,dif_neg left]

theorem suffixSource_height {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (suffixSource reference p d valid).shape.height ≤ (LocalReferences.depthReference reference).height := by
  induction reference with
  | leaf => exact le_rfl
  | @node a b cut ha hb l r ihl ihr =>
    simp only [suffixSource]
    split
    · have left := ihl (by omega)
      simp only [Source.shape,source_shape,LocalReferences.depthReference,RouterProjection.Router.height]
      omega
    · have right := ihr (by omega)
      simp only [LocalReferences.depthReference,RouterProjection.Router.height]
      omega

theorem suffixSource_word {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) :
    (fromRecordTree (PathPorts.skeleton followsRight (suffixSource reference p d valid))).toListModel =
      ((SeparatorPath.word reference p).filter (fun e => decide (d ≤ e.1))).map markEntry := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      have child := ihl bounds endpoint
      simp only [suffixSource,dif_pos bounds.2,PathPorts.skeleton,followsRight,bit,
        Bool.false_eq_true,if_false,fromRecordTree,Std.DTreeMap.Internal.Impl.toListModel_inner,
        Std.DTreeMap.Internal.Impl.toListModel_leaf,SeparatorPath.word,List.filter_append,
        List.filter_cons,decide_eq_true bounds.2,if_true,List.filter_nil,List.map_append,
        List.map_cons,List.map_nil,child,markEntry]
    · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      have notLeft : ¬ d ≤ cut := by omega
      simp only [suffixSource,dif_neg notLeft,SeparatorPath.word,bit,if_true,List.filter_cons,
        decide_eq_false notLeft,Bool.false_eq_true,if_false]
      exact ihr bounds endpoint

theorem suffixSource_terminalIndex {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) :
    terminalIndex followsRight (suffixSource reference p d valid) = 0 ∧
      terminalSource followsRight (suffixSource reference p d valid) = terminalLeaf d := by
  induction reference with
  | leaf a =>
    have equal : a = d := by omega
    subst d
    exact ⟨rfl,rfl⟩
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      simpa only [suffixSource,dif_pos bounds.2,terminalIndex,terminalSource,followsRight,
        bit,Bool.false_eq_true,if_false] using ihl bounds endpoint
    · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      have notLeft : ¬ d ≤ cut := by omega
      simpa only [suffixSource,dif_neg notLeft] using ihr bounds endpoint

end ChaCha.Paper20261030.SecondaryDecomposition
