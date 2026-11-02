import ChaCha.Paper20261030.DecodedHeadPivot

/-!
# Selecting the exact head repair from two observed records

`selectExit` tests the lower neighbor, then the upper neighbor, using
only their stored interval and preference fields. The selected record is
exactly the split of every abstract first-wrong-edge step. At a preferred
endpoint the same procedure returns `none`.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def unmarkEntry (e : Sigma (Tagged Payload)) : SeparatorPath.Entry := ⟨e.1,e.2.1⟩

def selectExit (d : Nat) (lower upper : Option SeparatorPath.Entry) : Option SeparatorPath.Entry :=
  match lower with
  | some e => if SeparatorPath.Exit d e then some e else upper.filter (fun f => decide (SeparatorPath.Exit d f))
  | none => upper.filter (fun f => decide (SeparatorPath.Exit d f))

def observedExit (d : Nat) (pair : NeighborPair (β := Payload)) : Option SeparatorPath.Entry :=
  selectExit d (pair.1.map unmarkEntry) (pair.2.map unmarkEntry)

theorem unmarked_neighbors {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    (neighbors d c.core).1.map unmarkEntry =
        ((SeparatorPath.word reference p).filter (fun e => decide (e.1 < d))).getLast? ∧
      (neighbors d c.core).2.map unmarkEntry =
        ((SeparatorPath.word reference p).filter (fun e => decide (d ≤ e.1))).head? := by
  obtain ⟨hl,hr⟩ := represented_neighbors reference p d c represented
  rw [hl,hr]
  have hi : unmarkEntry ∘ markEntry = id := by funext e; cases e; rfl
  constructor <;> simp only [Option.map_map,hi,Option.map_id,id_eq]

theorem selectExit_correct (d : Nat) (word : List SeparatorPath.Entry)
    (lower upper : Option SeparatorPath.Entry) (e : SeparatorPath.Entry)
    (lowerMem : ∀ f, lower = some f → f ∈ word) (upperMem : ∀ f, upper = some f → f ∈ word)
    (present : lower = some e ∨ upper = some e) (exits : SeparatorPath.Exit d e)
    (unique : ∀ f ∈ word, SeparatorPath.Exit d f → f = e) : selectExit d lower upper = some e := by
  cases hl : lower with
  | none =>
    have hu : upper = some e := present.resolve_left (by simp [hl])
    simp [selectExit,hl,hu,exits]
  | some f =>
    by_cases hf : SeparatorPath.Exit d f
    · have he := unique f (lowerMem f hl) hf
      simp [selectExit,hl,hf,he,exits]
    · have hu : upper = some e := present.resolve_left (by
        intro he
        have hfe := Option.some.inj (hl.symm.trans he)
        subst f
        exact hf exits)
      simp [selectExit,hl,hf,hu,exits]

theorem observed_head_selection {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {request depth : Nat} {after : PrefRouter Nat}
    (step : PrefRouter.HeadStep request depth (Secondary.decodeDepth reference p) after)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ v : PreferredSplit p reference,
      Secondary.decodeDepth reference (Function.update p v.split (!p v.split)) = after ∧
      observedExit request (neighbors request c.core) = some ⟨v.split.cut,(v.split,p v.split)⟩ := by
  obtain ⟨v,decode,exits⟩ := decoded_head_pivot_spec reference p step
  let e : SeparatorPath.Entry := ⟨v.split.cut,(v.split,p v.split)⟩
  have lowerMem : ∀ f, (neighbors request c.core).1.map unmarkEntry = some f → f ∈ SeparatorPath.word reference p := by
    intro f hf
    rw [(unmarked_neighbors reference p request c represented).1] at hf
    exact (List.mem_filter.mp (List.mem_of_getLast? hf)).1
  have upperMem : ∀ f, (neighbors request c.core).2.map unmarkEntry = some f → f ∈ SeparatorPath.word reference p := by
    intro f hf
    rw [(unmarked_neighbors reference p request c represented).2] at hf
    exact (List.mem_filter.mp (List.mem_of_head? hf)).1
  have present : (neighbors request c.core).1.map unmarkEntry = some e ∨
      (neighbors request c.core).2.map unmarkEntry = some e := by
    cases bit : p v.split
    · have hx : SeparatorPath.Exit request ⟨v.split.cut,(v.split,false)⟩ := by simpa only [bit] using exits
      have candidate := observed_right_exit v.lo_le_cut v.cut_lt_hi v.left v.right reference p v.below bit
        request (SeparatorPath.exit_left_preference _ _ hx) hx.2.1 c represented
      apply Or.inl
      rw [candidate]
      simp only [Option.map_some,unmarkEntry,e,bit]
    · have hx : SeparatorPath.Exit request ⟨v.split.cut,(v.split,true)⟩ := by simpa only [bit] using exits
      have candidate := observed_left_exit v.lo_le_cut v.cut_lt_hi v.left v.right reference p v.below bit
        request hx.1 (SeparatorPath.exit_right_preference _ _ hx) c represented
      apply Or.inr
      rw [candidate]
      simp only [Option.map_some,unmarkEntry,e,bit]
  have mem : e ∈ SeparatorPath.word reference p := present.elim (lowerMem e) (upperMem e)
  refine ⟨v,decode,?_⟩
  exact selectExit_correct request (SeparatorPath.word reference p) _ _ e lowerMem upperMem present exits
    (fun f hf hexit => SeparatorPath.exit_unique reference p request hf mem hexit exits)

theorem observed_terminal_none {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    observedExit (Secondary.decodeDepth reference p).terminal
      (neighbors (Secondary.decodeDepth reference p).terminal c.core) = none := by
  let d := (Secondary.decodeDepth reference p).terminal
  have lowerNone : ((neighbors d c.core).1.map unmarkEntry).filter
      (fun e => decide (SeparatorPath.Exit d e)) = none := by
    apply Option.filter_eq_none_iff.mpr
    intro e he
    rw [(unmarked_neighbors reference p d c represented).1] at he
    have hm := (List.mem_filter.mp (List.mem_of_getLast? he)).1
    simpa only [decide_eq_true_eq] using SeparatorPath.terminal_not_exit reference p hm
  have upperNone : ((neighbors d c.core).2.map unmarkEntry).filter
      (fun e => decide (SeparatorPath.Exit d e)) = none := by
    apply Option.filter_eq_none_iff.mpr
    intro e he
    rw [(unmarked_neighbors reference p d c represented).2] at he
    have hm := (List.mem_filter.mp (List.mem_of_head? he)).1
    simpa only [decide_eq_true_eq] using SeparatorPath.terminal_not_exit reference p hm
  change selectExit d _ _ = none
  cases hl : (neighbors d c.core).1.map unmarkEntry with
  | none => simpa only [selectExit,hl] using upperNone
  | some e =>
    have hn : ¬ SeparatorPath.Exit d e := by
      rw [hl] at lowerNone
      simpa using lowerNone
    simpa only [selectExit,hl,if_neg hn] using upperNone

end ChaCha.Paper20261030.SecondaryDecomposition
