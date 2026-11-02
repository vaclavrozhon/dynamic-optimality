import ChaCha.Paper20261030.SourceInorderLabels

set_option autoImplicit false

/-! Pairing two preserved inorder words retains the association between
each unique physical identifier and its metadata. This is used for root
caches: preserving their multiset alone would not retain that association. -/

namespace ChaCha.Paper20261030.ColoredStorage

variable {α ρ ι μ : Type*}

theorem Source.inorderLabels_pair (first : ρ → ι) (second : ρ → μ) (tree : Source α ρ) :
    tree.inorderLabels (fun record => (first record,second record)) =
      (tree.inorderLabels first).zip (tree.inorderLabels second) := by
  induction tree with
  | leaf => rfl
  | fork record left right ihl ihr =>
    have lengths : (left.inorderLabels first).length = (left.inorderLabels second).length := by
      have a := left.inorderLabels_length first
      have b := left.inorderLabels_length second
      omega
    simp only [Source.inorderLabels,ihl,ihr,List.zip_append lengths,List.zip_cons_cons]

theorem Source.inorderLabels_multiset (label : ρ → ι) (tree : Source α ρ) :
    (tree.inorderLabels label : Multiset ι) = tree.inventory label := by
  induction tree with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [Source.inorderLabels,← Multiset.coe_add,← Multiset.cons_coe,← Multiset.singleton_add,
      ihl,ihr,Source.inventory_fork]
    ac_rfl

theorem Source.paired_inventory (first : ρ → ι) (second : ρ → μ) (before after : Source α ρ)
    (firstOrder : after.inorderLabels first = before.inorderLabels first)
    (secondOrder : after.inorderLabels second = before.inorderLabels second) :
    after.inventory (fun record => (first record,second record)) =
      before.inventory (fun record => (first record,second record)) := by
  rw [← Source.inorderLabels_multiset,← Source.inorderLabels_multiset,
    Source.inorderLabels_pair,Source.inorderLabels_pair,firstOrder,secondOrder]

theorem Source.metadata_of_paired_inventory (identify : ρ → ι) (metadata : ρ → μ)
    (before after : Source α ρ) (unique : (before.inventory identify).Nodup)
    (paired : after.inventory (fun record => (identify record,metadata record)) =
      before.inventory (fun record => (identify record,metadata record)))
    (old fresh : ρ) (oldPresent : old ∈ before.inventory id) (freshPresent : fresh ∈ after.inventory id)
    (same : identify fresh = identify old) : metadata fresh = metadata old := by
  simp only [Source.inventory,Multiset.map_id] at oldPresent freshPresent
  have oldMember : (identify old,metadata old) ∈ before.inventory (fun record => (identify record,metadata record)) :=
    Multiset.mem_map.mpr ⟨old,oldPresent,rfl⟩
  have freshMember : (identify fresh,metadata fresh) ∈ before.inventory (fun record => (identify record,metadata record)) := by
    rw [← paired]
    exact Multiset.mem_map.mpr ⟨fresh,freshPresent,rfl⟩
  have pairUnique : ((before.inventory (fun record => (identify record,metadata record))).map Prod.fst).Nodup := by
    simpa only [Source.inventory,Multiset.map_map,Function.comp_def] using unique
  have values := Multiset.inj_on_of_nodup_map pairUnique _ freshMember _ oldMember same
  exact congrArg Prod.snd values

end ChaCha.Paper20261030.ColoredStorage
