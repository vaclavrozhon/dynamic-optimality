import ChaCha.BinaryLeafPotential
import ChaCha.PeriodicAccounting

/-!
# Concrete fragment aggregation

Every child owner belongs to one and only one ancestor owner. The lemmas below
identify the local micro/macro potentials with the actual depth-hierarchy terms,
including the auxiliary terminal fragments.
-/

namespace ChaCha
open Primary CyclicRuns

/-- Restricting an ancestor-local word to a descendant owner gives the actual
original word restricted to that descendant. -/
theorem ownerWord_nested (u v : Key) (h : u.IsPrefix v) (xs : List Key) :
    ownerWord v (ownerWord u xs) = ownerWord v xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hv : v.IsPrefix x
    · have hu := h.trans hv
      simp [ownerWord, hu, hv] at ih ⊢
      exact ih
    · by_cases hu : u.IsPrefix x <;> simpa [ownerWord, hu, hv] using ih

/-- Restricting a fine-label word by its coarse prefix is exactly the child
owner's fine-label word. -/
theorem fine_cellWord_eq_child_owner (u v : Key) (d f : Nat)
    (hv : v.length = d) (huv : u.IsPrefix v) (hdf : d ≤ f) (xs : List Key) :
    cellWord (List.take d) ((ownerWord u xs).map (List.take f)) v =
      (ownerWord v xs).map (List.take f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have heq : x.take d = v ↔ v.IsPrefix x := by
      rw [List.prefix_iff_eq_take, hv]
      exact eq_comm
    by_cases hvx : v.IsPrefix x
    · have hux := huv.trans hvx
      have htake : x.take d = v := heq.mpr hvx
      simpa [cellWord, ownerWord, hux, hvx, List.take_take, Nat.min_eq_left hdf, htake] using
        congrArg (List.cons (x.take f)) ih
    · have hn : x.take d ≠ v := fun h => hvx (heq.mp h)
      by_cases hux : u.IsPrefix x <;>
        simpa [cellWord, ownerWord, hux, hvx, List.take_take, Nat.min_eq_left hdf, hn] using ih

/-- Every depth-d child has a unique depth-a owner, namely its depth-a prefix. -/
theorem sum_descendant_levels {M : Type*} [AddCommMonoid M]
    (a d : Nat) (had : a ≤ d) (F : Key → M) :
    (∑ u ∈ level a, ∑ v ∈ (level d).filter (fun v => u.IsPrefix v), F v) =
      ∑ v ∈ level d, F v := by
  have hfilter (u : Key) (hu : u ∈ level a) :
      (level d).filter (fun v => u.IsPrefix v) =
        (level d).filter (fun v => v.take a = u) := by
    have hlen := (mem_level u a).1 hu
    ext v
    simp only [Finset.mem_filter]
    rw [List.prefix_iff_eq_take, hlen]
    simp only [eq_comm]
  have hmap : ∀ v ∈ level d, v.take a ∈ level a := by
    intro v hv
    apply (mem_level _ _).2
    rw [List.length_take, (mem_level v d).1 hv, Nat.min_eq_left had]
  calc
    _ = ∑ u ∈ level a, ∑ v ∈ (level d).filter (fun v => v.take a = u), F v := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hfilter u hu]
    _ = _ := Finset.sum_fiberwise_of_maps_to hmap F

/-- Per-fragment parent, macro, and micro potentials, using actual owner words. -/
def Gadget.parentPotential (H : Nat) (xs : List Key) (q : Gadget) : ℤ :=
  (wordTurns ((ownerWord q.owner xs).map (List.take (min (q.split.hi + 1) H))) : ℤ)

def Gadget.macroPotential (H : Nat) (xs : List Key) (q : Gadget) : ℤ :=
  (wordTurns ((ownerWord q.owner xs).map (List.take (min (q.split.cut + 1) H))) : ℤ)

def Gadget.microPotential (H : Nat) (xs : List Key) (q : Gadget) : ℤ :=
  ∑ v ∈ (level (q.split.cut + 1)).filter (fun v => q.owner.IsPrefix v),
    (wordTurns ((ownerWord v xs).map (List.take (min (q.split.hi + 1) H))) : ℤ)

def Gadget.potentialDifference (H : Nat) (xs : List Key) (q : Gadget) : ℤ :=
  q.macroPotential H xs + q.microPotential H xs - q.parentPotential H xs

/-- Micro potentials over all owners at the split's top depth are exactly the
potential of its lower depth child. -/
theorem sum_microPotential (H : Nat) (xs : List Key) (s : DepthSplit)
    (hlo : s.lo ≤ s.cut + 1) :
    (∑ u ∈ level s.lo, (Gadget.mk s u).microPotential H xs) =
      fragmentPotential H xs (s.cut + 1) s.hi := by
  simpa only [Gadget.microPotential, fragmentPotential] using
    sum_descendant_levels s.lo (s.cut + 1) hlo
      (fun v => (wordTurns ((ownerWord v xs).map (List.take (min (s.hi + 1) H))) : ℤ))

/-- The local differences aggregate to one actual depth-tree difference. -/
theorem sum_owner_potentialDifference (H : Nat) (xs : List Key) (s : DepthSplit)
    (hlo : s.lo ≤ s.cut + 1) :
    (∑ u ∈ level s.lo, (Gadget.mk s u).potentialDifference H xs) =
      splitPotentialDifference H xs s := by
  simp only [Gadget.potentialDifference, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_microPotential H xs s hlo]
  rfl

/-- A sum over all auxiliary fragments is exactly a sum over split-owner pairs. -/
theorem sum_allGadgets {M : Type*} [AddCommMonoid M] (H : Nat) (F : Gadget → M) :
    ∑ q ∈ allGadgets H, F q =
      ∑ s ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes,
        ∑ u ∈ level s.lo, F ⟨s, u⟩ := by
  unfold allGadgets
  rw [Finset.sum_image]
  · rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro s hs
    have hb := DepthTree.node_bounds _ hs
    have hlt : s.lo < H := by omega
    rw [← Finset.sum_filter]
    have heq : (owners H).filter (fun u => u.length = s.lo) = level s.lo :=
      (level_eq_owner_fiber hlt).symm
    rw [heq]
  · intro a ha b hb h
    cases a
    cases b
    simpa only [Gadget.mk.injEq, Prod.mk.injEq] using h

/-- Every concrete fragment difference is included exactly once in the telescope. -/
theorem sum_allGadgets_potentialDifference (H : Nat) (xs : List Key) :
    (∑ q ∈ allGadgets H, q.potentialDifference H xs) =
      ∑ s ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes,
        splitPotentialDifference H xs s := by
  rw [sum_allGadgets]
  apply Finset.sum_congr rfl
  intro s hs
  have hb := DepthTree.node_bounds _ hs
  exact sum_owner_potentialDifference H xs s (by omega)

/-- The actual global potential term is at most the cyclic primary count. -/
theorem allGadgets_potential_le_primary (H : Nat) (xs : List Key) (hleaves : OnLeaves H xs) :
    (∑ q ∈ allGadgets H, q.potentialDifference H xs) ≤ (cyclicPrimary H xs : ℤ) := by
  rw [sum_allGadgets_potentialDifference]
  have heq := fragment_potential_telescope_primary H xs hleaves
  have hnonneg : 0 ≤ fragmentPotential H xs 0 H := by
    unfold fragmentPotential
    exact Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  omega


/-- A depth projection automatically saturates at the actual leaf depth. -/
theorem take_saturated {H : Nat} (d : Nat) {x : Key} (hx : x.length = H) :
    x.take d = x.take (min d H) := by
  by_cases hd : d ≤ H
  · rw [Nat.min_eq_left hd]
  · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by omega)]
    rw [← hx, List.take_length]

theorem ownerWord_map_take_saturated (H d : Nat) (u : Key) (xs : List Key)
    (hleaves : OnLeaves H xs) :
    (ownerWord u xs).map (List.take d) =
      (ownerWord u xs).map (List.take (min d H)) := by
  apply List.map_congr_left
  intro x hx
  exact take_saturated d (hleaves x (List.mem_filter.mp hx).1)

theorem Gadget.parentPotential_eq_actual (q : Gadget) (H : Nat) (xs : List Key)
    (hleaves : OnLeaves H xs) :
    q.parentPotential H xs = (wordTurns ((ownerWord q.owner xs).map q.fine) : ℤ) := by
  unfold Gadget.parentPotential Gadget.fine
  rw [ownerWord_map_take_saturated H (q.split.hi + 1) q.owner xs hleaves]

theorem Gadget.macroPotential_eq_actual (q : Gadget) (H : Nat) (xs : List Key)
    (hleaves : OnLeaves H xs) :
    q.macroPotential H xs = (wordTurns ((ownerWord q.owner xs).map q.coarse) : ℤ) := by
  unfold Gadget.macroPotential Gadget.coarse
  rw [ownerWord_map_take_saturated H (q.split.cut + 1) q.owner xs hleaves]

/-- All visited coarse names may be summed over any finite covering universe:
unvisited cells contribute the empty word, hence zero turns. -/
theorem sum_visited_cellWords {α C : Type*} [LinearOrder α] [LinearOrder C] [DecidableEq C]
    (coarse : α → C) (word : List α) (names : Finset C)
    (hcover : ∀ x ∈ word, coarse x ∈ names) :
    (∑ c ∈ (word.map coarse).toFinset, (wordTurns (cellWord coarse word c) : ℤ)) =
      ∑ c ∈ names, (wordTurns (cellWord coarse word c) : ℤ) := by
  apply Finset.sum_subset
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact hcover x hx
  · intro c hc hn
    have he : cellWord coarse word c = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hne : coarse x ≠ c := by
        intro heq
        apply hn
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, heq⟩)
      simpa using hne
    rw [he]
    rfl

/-- Micro potentials use exactly the actual fine-word restriction to coarse names. -/
theorem Gadget.microPotential_eq_cells {H : Nat} {q : Gadget}
    (hq : q ∈ allGadgets H) (xs : List Key) (hleaves : OnLeaves H xs) :
    q.microPotential H xs =
      ∑ v ∈ (level (q.split.cut + 1)).filter (fun v => q.owner.IsPrefix v),
        (wordTurns (cellWord q.coarse ((ownerWord q.owner xs).map q.fine) v) : ℤ) := by
  obtain ⟨hs, hu, hlen⟩ := mem_allGadgets.mp hq
  have hb := DepthTree.node_bounds _ hs
  unfold Gadget.microPotential
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨hvlevel, huv⟩ := Finset.mem_filter.mp hv
  rw [← ownerWord_map_take_saturated H (q.split.hi + 1) v xs hleaves]
  have hword := fine_cellWord_eq_child_owner q.owner v (q.split.cut + 1) (q.split.hi + 1)
    ((mem_level v _).1 hvlevel) huv (by omega) xs
  exact congrArg (fun w => (wordTurns w : ℤ)) hword.symm

/-- The local micro sum over visited names is the actual fragment micro potential. -/
theorem Gadget.microPotential_eq_visited {H : Nat} {q : Gadget}
    (hq : q ∈ allGadgets H) (xs : List Key) (hleaves : OnLeaves H xs) :
    q.microPotential H xs =
      ∑ v ∈ (((ownerWord q.owner xs).map q.fine).map q.coarse).toFinset,
        (wordTurns (cellWord q.coarse ((ownerWord q.owner xs).map q.fine) v) : ℤ) := by
  rw [Gadget.microPotential_eq_cells hq xs hleaves]
  symm
  apply sum_visited_cellWords
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  obtain ⟨hxin, hpx⟩ := List.mem_filter.mp hx
  have hp : q.owner.IsPrefix x := of_decide_eq_true hpx
  obtain ⟨hs, hu, hlen⟩ := mem_allGadgets.mp hq
  have hb := DepthTree.node_bounds _ hs
  have hxH := hleaves x hxin
  have hproj : q.coarse (q.fine x) = x.take (q.split.cut + 1) := by
    simp only [Gadget.coarse, Gadget.fine, List.take_take, Nat.min_eq_left (by omega : q.split.cut + 1 ≤ q.split.hi + 1)]
  rw [hproj]
  apply Finset.mem_filter.mpr
  constructor
  · apply (mem_level _ _).2
    rw [List.length_take, hxH, Nat.min_eq_left (by omega)]
  · apply List.prefix_iff_eq_take.mpr
    rw [List.take_take, Nat.min_eq_left (by omega : q.owner.length ≤ q.split.cut + 1)]
    exact List.prefix_iff_eq_take.mp hp


/-- Cast a concrete finite natural count without changing its indexing. -/
theorem intCast_nat_sum {ι : Type*} (s : Finset ι) (f : ι → Nat) :
    ((∑ x ∈ s, f x : Nat) : ℤ) = ∑ x ∈ s, (f x : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert x s hx ih => simp only [Finset.sum_insert hx, Int.natCast_add, ih]

namespace CyclicRuns

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

omit [LinearOrder α] in
/-- A run-name set is exactly the set of coarse names of its actual letters. -/
theorem cells_eq_visited (coarse : α → C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse) :
    cells coarse blocks = (((blocks.map Block.word).flatten).map coarse).toFinset := by
  ext c
  constructor
  · intro hc
    obtain ⟨b, hb, hbc⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨b.first, ?_, hbc⟩
    exact List.mem_flatten.mpr ⟨b.word, List.mem_map.mpr ⟨b, hb, rfl⟩, by simp [Block.word]⟩
  · intro hc
    obtain ⟨x, hx, hxc⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    obtain ⟨word, hw, hxw⟩ := List.mem_flatten.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨b, hb, (homogeneous b hb x hxw).symm.trans hxc⟩

/-- The local macro-plus-micro-minus-parent term of an actual fine-label word. -/
def localTurnPotential (coarse : α → C) (word : List α) : ℤ :=
  (wordTurns (word.map coarse) : ℤ) +
    (∑ c ∈ (word.map coarse).toFinset, (wordTurns (cellWord coarse word c) : ℤ)) -
    (wordTurns word : ℤ)

/-- Choosing a different origin on the cyclic word changes no local potential. -/
theorem localTurnPotential_swap_append (coarse : α → C) (xs ys : List α) :
    localTurnPotential coarse (xs ++ ys) = localTurnPotential coarse (ys ++ xs) := by
  have hnames : ((xs ++ ys).map coarse).toFinset = ((ys ++ xs).map coarse).toFinset := by
    simp only [List.map_append, List.toFinset_append]
    exact Finset.union_comm _ _
  have hmicro :
      (∑ c ∈ ((xs ++ ys).map coarse).toFinset, (wordTurns (cellWord coarse (xs ++ ys) c) : ℤ)) =
      ∑ c ∈ ((ys ++ xs).map coarse).toFinset, (wordTurns (cellWord coarse (ys ++ xs) c) : ℤ) := by
    rw [hnames]
    apply Finset.sum_congr rfl
    intro c hc
    unfold cellWord
    rw [List.filter_append, List.filter_append, wordTurns_swap_append]
  unfold localTurnPotential
  rw [hmicro, wordTurns_swap_append xs ys]
  simp only [List.map_append]
  rw [wordTurns_swap_append (xs.map coarse) (ys.map coarse)]

/-- The actual local turn identity expressed as its telescoping potential term. -/
theorem local_turn_potential_identity (coarse : α → C) (ordered : Monotone coarse)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse)))
    (returns : ReturnsMatch coarse (b :: bs)) :
    (groupedJoins coarse (b :: bs) : ℤ) +
      (TurnAccounting.nontrivialMacroTurns (encode b.first (b :: bs)) : ℤ) =
      localTurnPotential coarse ((b :: bs).map Block.word).flatten +
        (TurnAccounting.entryTurns (encode b.first (b :: bs)) : ℤ) +
        (TurnAccounting.exitTurns (encode b.first (b :: bs)) : ℤ) := by
  have hfine := fine_boundaries_of_coarse coarse b.first (b :: bs) homogeneous boundary
  have h := actual_local_turn_identity coarse ordered b bs homogeneous boundary hfine returns
  rw [← wordTurns_blocks_coarse coarse (b :: bs) homogeneous, cells_eq_visited coarse (b :: bs) homogeneous] at h
  have hc := congrArg (fun n : Nat => (n : ℤ)) h
  simp only [Int.natCast_add, intCast_nat_sum] at hc
  unfold localTurnPotential
  omega

/-- The one-cell case has identically zero telescoping difference. -/
theorem localTurnPotential_of_constant (coarse : α → C) (word : List α)
    (hconstant : CoarseConstant coarse word) : localTurnPotential coarse word = 0 := by
  cases word with
  | nil => simp [localTurnPotential, wordTurns, cyclicDirections, TurnAccounting.cyclicTurns]
  | cons a as =>
    have hc : ∀ x ∈ a :: as, coarse x = coarse a :=
      fun x hx => hconstant x hx a (by simp)
    have hmacro : wordTurns ((a :: as).map coarse) = 0 := by
      apply wordTurns_constant (coarse a)
      intro c hcmap
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcmap
      exact hc x hx
    have hnames : ((a :: as).map coarse).toFinset = {coarse a} := by
      ext c
      constructor
      · intro h
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
        simp only [Finset.mem_singleton]
        exact hc x hx
      · intro h
        have he : c = coarse a := Finset.mem_singleton.mp h
        subst c
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, by simp, rfl⟩)
    have hcell : cellWord coarse (a :: as) (coarse a) = a :: as := by
      apply List.filter_eq_self.mpr
      intro x hx
      simpa using hc x hx
    unfold localTurnPotential
    rw [hmacro, hnames, Finset.sum_singleton, hcell]
    omega

end CyclicRuns

/-- Projection through fine labels preserves the actual transition word. -/
theorem transitionsFrom_project_fine {α C F : Type*} [DecidableEq C] [DecidableEq F]
    (coarse : α → C) (fine : α → F) (projectCoarse : F → C)
    (factor : ∀ x, projectCoarse (fine x) = coarse x) (a : α) (xs : List α) :
    transitionsFrom projectCoarse id (fine a) (xs.map fine) = transitionsFrom coarse fine a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases hc : coarse a = coarse b <;> by_cases hf : fine a = fine b <;>
      simp [transitionsFrom, transitionLabel, factor, hc, hf, ih]
    exact hc (by rw [← factor a, ← factor b, hf])

theorem demands_project_fine {α C F : Type*} [DecidableEq C] [DecidableEq F]
    (coarse : α → C) (fine : α → F) (projectCoarse : F → C)
    (factor : ∀ x, projectCoarse (fine x) = coarse x) (xs : List α) :
    demands projectCoarse id (xs.map fine) = demands coarse fine xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
    simp only [List.map_cons, demands, transitionWord]
    rw [transitionsFrom_project_fine coarse fine projectCoarse factor]

theorem Gadget.coarse_fine {H : Nat} {q : Gadget} (hq : q ∈ allGadgets H) (x : Key) :
    q.coarse (q.fine x) = q.coarse x := by
  have hb := DepthTree.node_bounds _ (mem_allGadgets.mp hq).1
  simp only [Gadget.coarse, Gadget.fine, List.take_take,
    Nat.min_eq_left (by omega : q.split.cut + 1 ≤ q.split.hi + 1)]

/-- The manuscript's actual local demand is unchanged by using its fine labels. -/
theorem Gadget.count_eq_fine_demands {H : Nat} {q : Gadget} (hq : q ∈ allGadgets H)
    (xs : List Key) : q.count xs = demands q.coarse id ((ownerWord q.owner xs).map q.fine) :=
  (demands_project_fine q.coarse q.fine q.coarse (Gadget.coarse_fine hq) _).symm

/-- The per-gadget hierarchy term is the pure local potential of its actual fine word. -/
theorem Gadget.potentialDifference_eq_local {H : Nat} {q : Gadget}
    (hq : q ∈ allGadgets H) (xs : List Key) (hleaves : OnLeaves H xs) :
    q.potentialDifference H xs =
      localTurnPotential q.coarse ((ownerWord q.owner xs).map q.fine) := by
  have hb := DepthTree.node_bounds _ (mem_allGadgets.mp hq).1
  have hmap : (((ownerWord q.owner xs).map q.fine).map q.coarse) =
      (ownerWord q.owner xs).map q.coarse := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_def, Gadget.coarse, Gadget.fine, List.take_take,
      Nat.min_eq_left (by omega : q.split.cut + 1 ≤ q.split.hi + 1)]
  rw [Gadget.potentialDifference, Gadget.parentPotential_eq_actual q H xs hleaves,
    Gadget.macroPotential_eq_actual q H xs hleaves, Gadget.microPotential_eq_visited hq xs hleaves]
  unfold localTurnPotential
  rw [hmap]
  congr 2
  apply Finset.sum_congr
  · ext v
    simp
  · intro v hv
    rfl

/-- A rotated run layout has exactly the original gadget's telescoping term. -/
theorem Gadget.layout_local_turn_identity {H : Nat} {q : Gadget}
    (hq : q ∈ allGadgets H) (xs : List Key) (hleaves : OnLeaves H xs)
    (layout : CyclicLayout q.coarse ((ownerWord q.owner xs).map q.fine))
    (returns : ReturnsMatch q.coarse (layout.first :: layout.rest)) :
    (groupedJoins q.coarse (layout.first :: layout.rest) : ℤ) +
      (TurnAccounting.nontrivialMacroTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) =
      q.potentialDifference H xs +
        (TurnAccounting.entryTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) +
        (TurnAccounting.exitTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) := by
  have h := local_turn_potential_identity q.coarse (fun _ _ h => take_mono_lex h _)
    layout.first layout.rest layout.homogeneous layout.boundaries returns
  have hp : localTurnPotential q.coarse ((layout.first :: layout.rest).map Block.word).flatten =
      q.potentialDifference H xs := by
    rw [layout.rotation, localTurnPotential_swap_append, ← layout.split,
      ← Gadget.potentialDifference_eq_local hq xs hleaves]
  rw [hp] at h
  exact h

/-- A gadget that visits at most one coarse cell has zero demand and zero
potential difference; no sign assumption about an arbitrary zero-demand word is used. -/
theorem Gadget.constant_case {H : Nat} {q : Gadget} (hq : q ∈ allGadgets H)
    (xs : List Key) (hleaves : OnLeaves H xs)
    (hconstant : CoarseConstant q.coarse ((ownerWord q.owner xs).map q.fine)) :
    q.count xs = 0 ∧ q.potentialDifference H xs = 0 := by
  constructor
  · rw [Gadget.count_eq_fine_demands hq xs]
    cases hw : (ownerWord q.owner xs).map q.fine with
    | nil => rfl
    | cons a as =>
      rw [hw] at hconstant
      apply rlFrom_transitionsFrom_of_same_coarse q.coarse id a as false
      intro y hy
      exact hconstant y (by simp [hy]) a (by simp)
  · rw [Gadget.potentialDifference_eq_local hq xs hleaves]
    exact localTurnPotential_of_constant _ _ hconstant

end ChaCha
