import MultiSplay.IntervalGadgets

/-!
# Subsequence monotonicity for arbitrary binary interval hierarchies

Actual neighboring access occurrences locate the unique charged primary node.
The hierarchy supplies uniqueness of the separating depth split. The shared
primary counter and concrete deletion-charge records are unchanged.
-/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary

theorem creation_separates {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : q ∈ gadgets hierarchy)
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


theorem DeletionCharge.gadget_unique {H : Nat} {hierarchy : DepthTree 0 H} {q r : Gadget} {w : Key}
    {pre post : List Key} {x : Key} (hq : q ∈ gadgets hierarchy) (hr : r ∈ gadgets hierarchy)
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


theorem charged_node_exists {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {pre post : List Key} {x : Key}
    (hq : q ∈ gadgets hierarchy) (hleaves : OnLeaves H (pre ++ x :: post))
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
    wp := ChaCha.prefix_of_branch_some hpa, wz := ChaCha.prefix_of_branch_some hza,
    a := a, b := b, pBranch := hpa, xBranch := hxb, zBranch := hza,
    opposite := hab, separated := hsep }⟩⟩
  rw [mem_owners, List.length_take, hx]
  omega


theorem weighted_delete {H : Nat} {hierarchy : DepthTree 0 H} (pre post : List Key) (x : Key)
    (hleaves : OnLeaves H (pre ++ x :: post)) :
    2 * secondaryDemands hierarchy (pre ++ post) + primaryCount H (pre ++ post) ≤
      2 * secondaryDemands hierarchy (pre ++ x :: post) + primaryCount H (pre ++ x :: post) := by
  classical
  let increased := (gadgets hierarchy).filter
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
    exact MultiSplay.IntervalLower.DeletionCharge.gadget_unique (Finset.mem_filter.mp q.property).1
      (Finset.mem_filter.mp r.property).1 cq cr
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
  have hd : secondaryDemands hierarchy (pre ++ post) ≤
      secondaryDemands hierarchy (pre ++ x :: post) + increased.card := by
    have hsum := Finset.sum_le_sum (s := gadgets hierarchy)
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


theorem weighted_sublist {H : Nat} {hierarchy : DepthTree 0 H} {xs ys : List Key} (h : xs.Sublist ys)
    (hleaves : OnLeaves H ys) :
    2 * secondaryDemands hierarchy xs + primaryCount H xs ≤
      2 * secondaryDemands hierarchy ys + primaryCount H ys := by
  have aux {as bs : List Key} (hs : as.Sublist bs) : ∀ pre : List Key,
      OnLeaves H (pre ++ bs) →
      2 * secondaryDemands hierarchy (pre ++ as) + primaryCount H (pre ++ as) ≤
        2 * secondaryDemands hierarchy (pre ++ bs) + primaryCount H (pre ++ bs) := by
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
      exact (ih pre hl').trans (weighted_delete (hierarchy := hierarchy) pre bs x hl)
    | @cons_cons as bs x hs ih =>
      intro pre hl
      simpa only [List.append_assoc, List.singleton_append] using
        ih (pre ++ [x]) (by simpa only [List.append_assoc, List.singleton_append] using hl)
  simpa using aux h [] (by simpa using hleaves)


theorem demand_primary_sublist {H : Nat} {hierarchy : DepthTree 0 H} {xs ys : List Key} (h : xs.Sublist ys)
    (hleaves : OnLeaves H ys) :
    secondaryDemands hierarchy xs + primaryCount H xs ≤
      secondaryDemands hierarchy ys + primaryCount H ys := by
  have hw := weighted_sublist (hierarchy := hierarchy) h hleaves
  have hp := primaryCount_sublist H h
  omega


theorem total_sublist {H : Nat} {hierarchy : DepthTree 0 H} {xs ys : List Key} (h : xs.Sublist ys)
    (hleaves : OnLeaves H ys) :
    xs.length + secondaryDemands hierarchy xs + primaryCount H xs ≤
      ys.length + secondaryDemands hierarchy ys + primaryCount H ys := by
  have hd := demand_primary_sublist (hierarchy := hierarchy) h hleaves
  have hl := h.length_le
  omega


end MultiSplay.IntervalLower
