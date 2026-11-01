import TangoSquared.Paper20261030.PrimaryComponentOwners
import TangoSquared.Paper20261030.SuffixSource

/-!
# A head access preserves every other component's genuine memory

The owner address of a dormant record differs from the active endpoint's
address. Thus the actual depth write does not touch it. Structural bits
on the sentinel path are forced independently of memory and give equal
prepared suffix sources whenever their genuine bits agree.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem head_dormant_genuine_unchanged {x key : α} {d height : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (perfect : before.Perfect height) (member : key ∈ before.leaves) (other : key ≠ before.terminal)
    (preference : MemoryKey → Bool) (split : DepthSplit)
    (below : before.componentStart key ≤ split.lo) (upper : split.lo ≤ height) :
    ownerBits after key (advanceDepth before x d preference) split = ownerBits before key preference split := by
  have addressLength : ((before.searchPath key).take split.lo).length = split.lo := by
    rw [List.length_take,PrefRouter.searchPath_length perfect member,Nat.min_eq_left upper]
  have separate := PrefRouter.componentStart_owner_ne distinct member other below
  have outside : ¬ ((before.searchPath key).take split.lo).IsPrefix (before.searchPath before.terminal) := by
    simpa only [List.prefix_iff_eq_take,addressLength] using separate
  have write := head_depthWrite_owner step distinct (split,(before.searchPath key).take split.lo) addressLength
  simp only [ownerBits,step.searchPath key,advanceDepth,write]
  rw [if_neg (fun h => outside h.1)]
  rfl

end TangoSquared.Paper20261030.Secondary

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem prepared_suffix_congr {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (sentinel : Nat) (valid : a ≤ sentinel ∧ sentinel ≤ b)
    (same : ∀ split ∈ reference.nodes, sentinel < split.lo → p split = q split) :
    suffixSource reference (Secondary.intervalUpdate sentinel p) sentinel valid =
      suffixSource reference (Secondary.intervalUpdate sentinel q) sentinel valid := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb left right ihl ihr =>
    have rootSame : Secondary.intervalUpdate sentinel p ⟨a,cut,b⟩ =
        Secondary.intervalUpdate sentinel q ⟨a,cut,b⟩ := by simp [Secondary.intervalUpdate,valid]
    have leftSame : ∀ split ∈ left.nodes, sentinel < split.lo → p split = q split := by
      intro split member after
      exact same split (by simp [DepthTree.nodes,member]) after
    have rightSame : ∀ split ∈ right.nodes, sentinel < split.lo → p split = q split := by
      intro split member after
      exact same split (by simp [DepthTree.nodes,member]) after
    by_cases keepLeft : sentinel ≤ cut
    · have rightSources : source right (Secondary.intervalUpdate sentinel p) =
          source right (Secondary.intervalUpdate sentinel q) := by
        apply source_congr
        intro split member
        have bounds := right.node_bounds member
        have after : sentinel < split.lo := by omega
        simp only [Secondary.intervalUpdate,if_neg (show ¬ (split.lo ≤ sentinel ∧ sentinel ≤ split.hi) by omega)]
        exact rightSame split member after
      simp only [suffixSource,dif_pos keepLeft,rootSame,ihl ⟨valid.1,keepLeft⟩ leftSame,rightSources]
    · simp only [suffixSource,dif_neg keepLeft,ihr ⟨by omega,valid.2⟩ rightSame]

end TangoSquared.Paper20261030.SecondaryDecomposition
