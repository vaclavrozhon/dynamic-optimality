import TangoSquared.Paper20261030.GlobalPrimaryInventory

set_option autoImplicit false

/-! Initial logical names may be tagged by their owning endpoint. This
proves the finite global uniqueness invariant from the existing local
uniqueness proofs. It is only a ghost naming lemma: it does not install
stored names or claim a local initialization program. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryInventory

variable {α η : Type*} [DecidableEq α]

theorem mem_total (keys : Finset α) (owned : α → Multiset η) (record : η) :
    record ∈ total keys owned ↔ ∃ key ∈ keys, record ∈ owned key := by
  induction keys using Finset.induction_on with
  | empty => simp [total]
  | @insert key keys absent ih =>
    simp only [total,Finset.sum_insert absent,Multiset.mem_add] at ih ⊢
    constructor
    · intro member
      rcases member with here | there
      · exact ⟨key,Finset.mem_insert_self _ _,here⟩
      · obtain ⟨other,present,inside⟩ := ih.mp there
        exact ⟨other,Finset.mem_insert_of_mem present,inside⟩
    · rintro ⟨other,present,inside⟩
      rcases Finset.mem_insert.mp present with rfl | present
      · exact Or.inl inside
      · exact Or.inr (ih.mpr ⟨other,present,inside⟩)

theorem unique_of_components (keys : Finset α) (owned : α → Multiset η)
    (localUnique : ∀ key ∈ keys, (owned key).Nodup)
    (separate : ∀ first ∈ keys, ∀ second ∈ keys, first ≠ second → Disjoint (owned first) (owned second)) :
    Unique keys owned := by
  induction keys using Finset.induction_on with
  | empty => simp [Unique,total]
  | @insert key keys absent ih =>
    unfold Unique total
    rw [Finset.sum_insert absent]
    apply Multiset.nodup_add.mpr
    refine ⟨localUnique key (Finset.mem_insert_self _ _),
      ih (fun other member => localUnique other (Finset.mem_insert_of_mem member))
        (fun first hm second hn => separate first (Finset.mem_insert_of_mem hm) second (Finset.mem_insert_of_mem hn)),?_⟩
    apply Multiset.disjoint_left.mpr
    intro record here there
    obtain ⟨other,present,inside⟩ := (mem_total keys owned record).mp there
    have different : key ≠ other := fun same => absent (same.symm ▸ present)
    exact Multiset.disjoint_left.mp
      (separate key (Finset.mem_insert_self _ _) other (Finset.mem_insert_of_mem present) different) here inside

theorem owner_tagged_unique (keys : Finset α) (owned : α → Multiset η)
    (localUnique : ∀ key ∈ keys, (owned key).Nodup) :
    Unique keys (fun key => (owned key).map (fun record => (key,record))) := by
  apply unique_of_components
  · intro key member
    exact (Multiset.nodup_map_iff_of_injective
      (show Function.Injective (fun record : η => (key,record)) from fun _ _ equality => congrArg Prod.snd equality)).mpr
        (localUnique key member)
  · intro first firstMem second secondMem different
    apply Multiset.disjoint_left.mpr
    intro record inFirst inSecond
    obtain ⟨left,_,leftEq⟩ := Multiset.mem_map.mp inFirst
    obtain ⟨right,_,rightEq⟩ := Multiset.mem_map.mp inSecond
    exact different (congrArg Prod.fst (leftEq.trans rightEq.symm))

end TangoSquared.Paper20261030.GlobalPrimaryInventory
