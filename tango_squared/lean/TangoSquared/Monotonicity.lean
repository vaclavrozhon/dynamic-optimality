import TangoSquared.Primary
import TangoSquared.Reference
import TangoSquared.Demands
import TangoSquared.FilteredDeletion
import Mathlib.Data.Finset.Prod

/-!
# The concrete global subsequence argument

Gadgets are actual pairs of a midpoint depth split and a primary owner.
Their demand counts are computed from the owner-filtered access word.
-/

namespace TangoSquared
open Primary

structure Gadget where
  split : DepthSplit
  owner : Key
  deriving DecidableEq

/-- Precisely the nonterminal fragments of the manuscript. -/
def gadgets (H : Nat) : Finset Gadget :=
  (((DepthTree.midpoint 0 H (Nat.zero_le H)).nodes ×ˢ owners H).filter
    (fun q => q.2.length = q.1.lo ∧ q.1.hi < H)).image (fun q => ⟨q.1, q.2⟩)

theorem mem_gadgets {H : Nat} {q : Gadget} : q ∈ gadgets H ↔
    q.split ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes ∧
    q.owner ∈ owners H ∧ q.owner.length = q.split.lo ∧ q.split.hi < H := by
  cases q
  simp [gadgets, and_assoc]

def Gadget.coarse (q : Gadget) (x : Key) : Key := x.take (q.split.cut + 1)
def Gadget.fine (q : Gadget) (x : Key) : Key := x.take (q.split.hi + 1)
def Gadget.count (q : Gadget) (xs : List Key) : Nat :=
  demands q.coarse q.fine (ownerWord q.owner xs)

def secondaryDemands (H : Nat) (xs : List Key) : Nat :=
  ∑ q ∈ gadgets H, q.count xs

def primaryCount (H : Nat) (xs : List Key) : Nat :=
  primaryAlternations (owners H) branch xs

theorem primaryCount_sublist (H : Nat) {xs ys : List Key} (h : xs.Sublist ys) :
    primaryCount H xs ≤ primaryCount H ys :=
  primaryAlternations_sublist _ _ h

/-- The sequence is on the leaves of the height-`H` reference tree. -/
def OnLeaves (H : Nat) (xs : List Key) : Prop := ∀ x ∈ xs, x.length = H

theorem ownerWord_append (u : Key) (xs ys : List Key) :
    ownerWord u (xs ++ ys) = ownerWord u xs ++ ownerWord u ys := by
  simp [ownerWord]

theorem count_delete_le_add_one (q : Gadget) (pre post : List Key) (x : Key) :
    q.count (pre ++ post) ≤ q.count (pre ++ x :: post) + 1 := by
  by_cases hx : q.owner.IsPrefix x
  · simpa [Gadget.count, ownerWord, hx] using
      demands_delete_le_add_one q.coarse q.fine
        (ownerWord q.owner pre) (ownerWord q.owner post) x
  · simp [Gadget.count, ownerWord, hx]

theorem owner_prefix_of_increase (q : Gadget) (pre post : List Key) (x : Key)
    (hi : q.count (pre ++ x :: post) < q.count (pre ++ post)) :
    q.owner.IsPrefix x := by
  by_contra hx
  simp [Gadget.count, ownerWord, hx] at hi

theorem creation_separates {H : Nat} {q : Gadget} (hq : q ∈ gadgets H)
    {p x z : Key} (hp : p.length = H) (hx : x.length = H) (hz : z.length = H)
    (hup : q.owner.IsPrefix p) (hux : q.owner.IsPrefix x)
    (hc : DemandCreation q.coarse q.fine p x z) :
    q.split.Separates (lcaDepth p x) (lcaDepth p z) := by
  obtain ⟨hqs, _, hlen, hhi⟩ := mem_gadgets.mp hq
  obtain ⟨_, hlo, hcut, _⟩ := DepthTree.node_bounds _ hqs
  have ho : p.take q.split.lo = x.take q.split.lo := by
    have hp' := List.prefix_iff_eq_take.mp hup
    have hx' := List.prefix_iff_eq_take.mp hux
    rw [hlen] at hp' hx'
    exact hp'.symm.trans hx'
  have helo : q.split.lo ≤ lcaDepth p x :=
    (take_eq_iff (by omega) (by omega)).mp ho
  have hep : ¬ q.split.cut + 1 ≤ lcaDepth p x := by
    intro h
    exact hc.2.1 ((take_eq_iff (by omega) (by omega)).mpr h)
  have hfp : q.split.cut + 1 ≤ lcaDepth p z :=
    (take_eq_iff (by omega) (by omega)).mp hc.1
  have hfb : ¬ q.split.hi + 1 ≤ lcaDepth p z := by
    intro h
    exact hc.2.2 ((take_eq_iff (by omega) (by omega)).mpr h)
  exact ⟨helo, by omega, by omega, by omega⟩

theorem prefix_of_branch_some {w x : Key} {b : Bool} (h : branch w x = some b) :
    w.IsPrefix x := by
  by_contra hn
  simp [branch, hn] at h

/-- A charge records concrete immediate neighbors and a primary projection.
All fields will be derived from a strictly increased gadget. -/
structure DeletionCharge (q : Gadget) (w : Key) (pre : List Key) (x : Key)
    (post : List Key) where
  before : List Key
  after : List Key
  p : Key
  z : Key
  leftNeighbor : ownerWord q.owner pre = before ++ [p]
  rightNeighbor : ownerWord q.owner post = z :: after
  nested : q.owner.IsPrefix w
  wp : w.IsPrefix p
  wz : w.IsPrefix z
  a : Bool
  b : Bool
  pBranch : branch w p = some a
  xBranch : branch w x = some b
  zBranch : branch w z = some a
  opposite : a ≠ b
  separated : q.split.Separates (lcaDepth p x) (lcaDepth p z)

theorem DeletionCharge.loss {q : Gadget} {w : Key} {pre post : List Key} {x : Key}
    (c : DeletionCharge q w pre x post) :
    alternations ((pre ++ x :: post).filterMap (branch w)) =
      alternations ((pre ++ post).filterMap (branch w)) + 2 := by
  apply projected_alternations_delete_singleton
    (fun y => decide (q.owner.IsPrefix y)) (branch w) _
    pre c.before post c.after c.p x c.z c.a c.b
    c.leftNeighbor c.rightNeighbor c.pBranch c.xBranch c.zBranch c.opposite
  intro y hy
  have hn : ¬ q.owner.IsPrefix y := by simpa using hy
  have hw : ¬ w.IsPrefix y := fun h => hn (c.nested.trans h)
  simp [branch, hw]

/-- If two gadgets use one primary node, their neighbors are identical. -/
theorem DeletionCharge.neighbors_unique {q r : Gadget} {w : Key}
    {pre post : List Key} {x : Key}
    (c : DeletionCharge q w pre x post) (d : DeletionCharge r w pre x post) :
    c.p = d.p ∧ c.z = d.z := by
  have nest (u : Key) (h : u.IsPrefix w) :
      ∀ y, decide (w.IsPrefix y) = true → decide (u.IsPrefix y) = true := by
    intro y hy
    simpa using h.trans (of_decide_eq_true hy)
  have hlc := filter_last_of_imp _ _ (nest q.owner c.nested)
    pre c.before c.p c.leftNeighbor (by simpa using c.wp)
  have hld := filter_last_of_imp _ _ (nest r.owner d.nested)
    pre d.before d.p d.leftNeighbor (by simpa using d.wp)
  have hrc := filter_first_of_imp _ _ (nest q.owner c.nested)
    post c.after c.z c.rightNeighbor (by simpa using c.wz)
  have hrd := filter_first_of_imp _ _ (nest r.owner d.nested)
    post d.after d.z d.rightNeighbor (by simpa using d.wz)
  exact ⟨filtered_last_unique _ pre _ _ _ _ hlc hld,
    filtered_first_unique _ post _ _ _ _ hrc hrd⟩

/-- Global injectivity is obtained from concrete neighbors and the actual
secondary tree; no abstract disjoint-charging assumption is used. -/
theorem DeletionCharge.gadget_unique {H : Nat} {q r : Gadget} {w : Key}
    {pre post : List Key} {x : Key} (hq : q ∈ gadgets H) (hr : r ∈ gadgets H)
    (c : DeletionCharge q w pre x post) (d : DeletionCharge r w pre x post) : q = r := by
  obtain ⟨hp, hz⟩ := c.neighbors_unique d
  obtain ⟨hqs, _, hql, _⟩ := mem_gadgets.mp hq
  obtain ⟨hrs, _, hrl, _⟩ := mem_gadgets.mp hr
  have ds := d.separated
  rw [← hp, ← hz] at ds
  have hs : q.split = r.split := by
    have h₁ := DepthTree.locate_of_separates _ hqs c.separated
    have h₂ := DepthTree.locate_of_separates _ hrs ds
    exact Option.some.inj (h₁.symm.trans h₂)
  have ho : q.owner = r.owner := by
    have hlen : q.owner.length = r.owner.length := by rw [hql, hrl, hs]
    have hc := List.prefix_iff_eq_take.mp c.nested
    have hd := List.prefix_iff_eq_take.mp d.nested
    rw [hc, hd, hlen]
  cases q
  cases r
  simp_all

/-- Every newly created demand supplies an actual charged primary node. -/
theorem charged_node_exists {H : Nat} {q : Gadget} {pre post : List Key} {x : Key}
    (hq : q ∈ gadgets H) (hleaves : OnLeaves H (pre ++ x :: post))
    (hi : q.count (pre ++ x :: post) < q.count (pre ++ post)) :
    ∃ w ∈ owners H, Nonempty (DeletionCharge q w pre x post) := by
  have hux := owner_prefix_of_increase q pre post x hi
  have hi' : demands q.coarse q.fine
      (ownerWord q.owner pre ++ x :: ownerWord q.owner post) <
      demands q.coarse q.fine (ownerWord q.owner pre ++ ownerWord q.owner post) := by
    simpa [Gadget.count, ownerWord, hux] using hi
  obtain ⟨before, p, z, after, hl, hr, hc, _⟩ :=
    demand_neighbors_of_delete_increase q.coarse q.fine _ _ x hi'
  have hpm : p ∈ ownerWord q.owner pre := by rw [hl]; simp
  have hzm : z ∈ ownerWord q.owner post := by rw [hr]; simp
  obtain ⟨hpmem, hup⟩ := List.mem_filter.mp hpm
  obtain ⟨hzmem, huz⟩ := List.mem_filter.mp hzm
  have hp : p.length = H := hleaves p (by simp [hpmem])
  have hx : x.length = H := hleaves x (by simp)
  have hz : z.length = H := hleaves z (by simp [hzmem])
  have hsep := creation_separates hq hp hx hz (of_decide_eq_true hup) hux hc
  obtain ⟨hqs, _, _, hhi⟩ := mem_gadgets.mp hq
  obtain ⟨_, _, hcut, _⟩ := DepthTree.node_bounds _ hqs
  have hef : lcaDepth p x < lcaDepth p z := by
    obtain ⟨_, he, hf, _⟩ := hsep
    omega
  have heH : lcaDepth p x < H := by
    obtain ⟨_, he, _, _⟩ := hsep
    omega
  obtain ⟨a, b, hab, hpa, hza, hxb⟩ := branches_at_lca hef (by omega)
  refine ⟨x.take (lcaDepth p x), ?_, ⟨{
    before := before, after := after, p := p, z := z,
    leftNeighbor := hl, rightNeighbor := hr,
    nested := prefix_take_lca (of_decide_eq_true hup) hux,
    wp := prefix_of_branch_some hpa, wz := prefix_of_branch_some hza,
    a := a, b := b, pBranch := hpa, xBranch := hxb, zBranch := hza,
    opposite := hab, separated := hsep }⟩⟩
  rw [mem_owners, List.length_take, hx]
  omega

/-- Deleting one access cannot increase the actual global count `2D + P`. -/
theorem weighted_delete {H : Nat} (pre post : List Key) (x : Key)
    (hleaves : OnLeaves H (pre ++ x :: post)) :
    2 * secondaryDemands H (pre ++ post) + primaryCount H (pre ++ post) ≤
      2 * secondaryDemands H (pre ++ x :: post) + primaryCount H (pre ++ x :: post) := by
  classical
  let increased := (gadgets H).filter
    (fun q => q.count (pre ++ x :: post) < q.count (pre ++ post))
  have hc (q : ↑increased) : ∃ w ∈ owners H,
      Nonempty (DeletionCharge q.val w pre x post) := by
    obtain ⟨hq, hi⟩ := Finset.mem_filter.mp q.property
    exact charged_node_exists hq hleaves hi
  let charge : ↑increased → Key := fun q => Classical.choose (hc q)
  have hcharge (q : ↑increased) : charge q ∈ owners H ∧
      Nonempty (DeletionCharge q.val (charge q) pre x post) :=
    Classical.choose_spec (hc q)
  have hinj : Function.Injective charge := by
    intro q r heq
    apply Subtype.ext
    have cq := Classical.choice (hcharge q).2
    have cr := Classical.choice (hcharge r).2
    rw [← heq] at cr
    exact cq.gadget_unique (Finset.mem_filter.mp q.property).1
      (Finset.mem_filter.mp r.property).1 cr
  let selected := increased.attach.image charge
  have hs : selected ⊆ owners H := by
    intro w hw
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hcharge q).1
  have hcard : selected.card = increased.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hsub : (pre ++ post).Sublist (pre ++ x :: post) :=
    (List.sublist_cons_self x post).append_left pre
  have hp := primaryAlternations_charge (owners H) selected branch hsub hs
    (by
      intro w hw
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
      have h := (Classical.choice (hcharge q).2).loss
      omega)
  rw [hcard] at hp
  change primaryCount H (pre ++ post) + 2 * increased.card ≤
    primaryCount H (pre ++ x :: post) at hp
  have hd : secondaryDemands H (pre ++ post) ≤
      secondaryDemands H (pre ++ x :: post) + increased.card := by
    have hsum := Finset.sum_le_sum (s := gadgets H)
      (f := fun q => q.count (pre ++ post))
      (g := fun q => q.count (pre ++ x :: post) +
        if q.count (pre ++ x :: post) < q.count (pre ++ post) then 1 else 0)
      (fun q _ => by
        split_ifs with h
        · exact count_delete_le_add_one q pre post x
        · omega)
    rw [Finset.sum_add_distrib] at hsum
    simpa only [secondaryDemands, increased, ← Finset.sum_filter,
      Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
      using hsum
  omega

/-- Arbitrary subsequence monotonicity, for every complete primary reference
height and its actual midpoint secondary reference. -/
theorem weighted_sublist {H : Nat} {xs ys : List Key} (h : xs.Sublist ys)
    (hleaves : OnLeaves H ys) :
    2 * secondaryDemands H xs + primaryCount H xs ≤
      2 * secondaryDemands H ys + primaryCount H ys := by
  have aux {as bs : List Key} (hs : as.Sublist bs) : ∀ pre : List Key,
      OnLeaves H (pre ++ bs) →
      2 * secondaryDemands H (pre ++ as) + primaryCount H (pre ++ as) ≤
        2 * secondaryDemands H (pre ++ bs) + primaryCount H (pre ++ bs) := by
    induction hs with
    | slnil => intro pre _; exact Nat.le_refl _
    | @cons as bs x hs ih =>
      intro pre hl
      have hl' : OnLeaves H (pre ++ bs) := by
        intro y hy
        apply hl y
        simpa only [List.mem_append, List.mem_cons] using
          (by rcases List.mem_append.mp hy with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr h) : y ∈ pre ∨ y = x ∨ y ∈ bs)
      exact (ih pre hl').trans (weighted_delete pre bs x hl)
    | @cons_cons as bs x hs ih =>
      intro pre hl
      simpa only [List.append_assoc, List.singleton_append] using
        ih (pre ++ [x]) (by simpa only [List.append_assoc, List.singleton_append] using hl)
  simpa using aux h [] (by simpa using hleaves)

/-- The unweighted candidate bound is monotone as well: combine the proved
`2D + P` monotonicity with ordinary primary alternation monotonicity. -/
theorem demand_primary_sublist {H : Nat} {xs ys : List Key} (h : xs.Sublist ys)
    (hleaves : OnLeaves H ys) :
    secondaryDemands H xs + primaryCount H xs ≤
      secondaryDemands H ys + primaryCount H ys := by
  have hw := weighted_sublist h hleaves
  have hp := primaryCount_sublist H h
  omega

/-- Include the unavoidable cost of the accesses themselves. -/
theorem total_sublist {H : Nat} {xs ys : List Key} (h : xs.Sublist ys)
    (hleaves : OnLeaves H ys) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤
      ys.length + secondaryDemands H ys + primaryCount H ys := by
  have hd := demand_primary_sublist h hleaves
  have hl := h.length_le
  omega

end TangoSquared
