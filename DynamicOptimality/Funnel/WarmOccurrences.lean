import DynamicOptimality.Funnel.WarmVisibility

/-! # Occurrence visibility and warm search ancestors -/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

theorem exposed_iff_split (history : List α) (x q : α) :
    Exposed x q history ↔ ∃ newer older, history = newer ++ q :: older ∧ q ≠ x ∧
      ∀ z ∈ newer, ¬ Between q x z := by
  induction history with
  | nil => simp [Exposed]
  | cons a history ih =>
    constructor
    · rintro (⟨rfl,different⟩ | ⟨outside,rest⟩)
      · exact ⟨[],history,rfl,different,by simp⟩
      · obtain ⟨newer,older,split,different,empty⟩ := ih.mp rest
        refine ⟨a::newer,older,by simp [split],different,?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact outside
        · exact empty z hz
    · rintro ⟨newer,older,split,different,empty⟩
      cases newer with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at split
        exact Or.inl ⟨split.1,different⟩
      | cons b newer =>
        simp only [List.cons_append,List.cons.injEq] at split
        obtain ⟨rfl,split⟩ := split
        exact Or.inr ⟨empty _ (by simp),ih.mpr ⟨newer,older,split,different,
          fun z hz => empty z (List.mem_cons_of_mem _ hz)⟩⟩

theorem exposed_reverse_iff_split (history : List α) (x q : α) :
    Exposed x q history.reverse ↔ ∃ older newer, history = older ++ q :: newer ∧ q ≠ x ∧
      ∀ z ∈ newer, ¬ Between q x z := by
  rw [exposed_iff_split]
  constructor
  · rintro ⟨newer,older,split,different,empty⟩
    refine ⟨older.reverse,newer.reverse,?_,different,?_⟩
    · have rev := congrArg List.reverse split
      simpa only [List.reverse_reverse,List.reverse_append,List.reverse_cons,
        List.append_assoc,List.singleton_append] using rev
    · intro z hz
      exact empty z (List.mem_reverse.mp hz)
  · rintro ⟨older,newer,split,different,empty⟩
    refine ⟨newer.reverse,older.reverse,?_,different,?_⟩
    · simp only [split,List.reverse_append,List.reverse_cons,List.append_assoc,List.singleton_append]
    · intro z hz
      exact empty z (List.mem_reverse.mp hz)

theorem visible_exposed {word : List α} {p q : Fin word.length}
    (visible : Visible word.get Finset.univ p q) :
    Exposed (word.get p) (word.get q) (word.take p.val).reverse := by
  let older := word.take q.val
  let newer := (word.take p.val).drop (q.val+1)
  have qp : q.val < p.val := visible.2.2.1
  have split : word.take p.val = older ++ word.get q :: newer := by
    have decomposition := List.take_append_drop (q.val+1) (word.take p.val)
    rw [List.take_take,Nat.min_eq_left (by omega),List.take_succ_eq_append_getElem q.isLt] at decomposition
    simpa only [older,newer,List.get_eq_getElem,List.append_assoc,List.singleton_append] using decomposition.symm
  apply (exposed_reverse_iff_split _ _ _).mpr
  refine ⟨older,newer,split,visible.2.2.2.1,?_⟩
  intro z hz
  obtain ⟨k,hk,hz⟩ := List.mem_iff_getElem.mp hz
  have bound : q.val+1+k < p.val := by
    simp only [newer,List.length_drop,List.length_take] at hk
    omega
  let s : Fin word.length := ⟨q.val+1+k,by omega⟩
  have qs : q < s := by change q.val < q.val+1+k; omega
  have sp : s < p := bound
  have key : word.get s = z := by
    simpa only [newer,List.getElem_drop,List.getElem_take,List.get_eq_getElem,s] using hz
  simpa only [key] using visible.2.2.2.2 s (Finset.mem_univ _) qs sp

theorem visible_mem_warm_ancestors {word : List α} {p q : Fin word.length}
    (visible : Visible word.get Finset.univ p q) :
    word.get q ∈ ancestors (word.get p) (cartesian (word.take p.val).reverse) :=
  (mem_ancestors_cartesian _ _ _).mpr (visible_exposed visible)

/-- Every warm visible key comes from a unique geometrically visible occurrence.
The existential formulation is essential when the input repeats a key. -/
theorem exposed_exists_visible {word : List α} {p : Fin word.length} {key : α}
    (exposed : Exposed (word.get p) key (word.take p.val).reverse) :
    ∃ q : Fin word.length, Visible word.get Finset.univ p q ∧ word.get q = key := by
  obtain ⟨older,newer,split,different,empty⟩ :=
    (exposed_reverse_iff_split _ _ _).mp exposed
  have size : p.val = older.length + (newer.length + 1) := by
    have sizes := congrArg List.length split
    simpa only [List.length_take,Nat.min_eq_left p.isLt.le,List.length_append,
      List.length_cons] using sizes
  let q : Fin word.length := ⟨older.length,by omega⟩
  have qp : q < p := by change older.length < p.val; omega
  have keyAt : word.get q = key := by
    have takeKey : (word.take p.val)[older.length]'(by simp only [List.length_take]; omega) = key := by
      simp [split]
    simpa only [List.getElem_take,List.get_eq_getElem,q] using takeKey
  refine ⟨q,⟨Finset.mem_univ _,Finset.mem_univ _,qp,?_,?_⟩,keyAt⟩
  · simpa only [keyAt] using different
  · intro r _ qr rp
    have suffix : (word.take p.val).drop (older.length + 1) = newer := by
      rw [split,List.drop_append]
      simp
    have occurs : word.get r ∈ (word.take p.val).drop (older.length + 1) := by
      apply List.mem_iff_getElem.mpr
      refine ⟨r.val - (older.length + 1),?_,?_⟩
      · simp only [List.length_drop,List.length_take]
        change older.length < r.val at qr
        change r.val < p.val at rp
        omega
      · simp only [List.getElem_drop,List.getElem_take,List.get_eq_getElem]
        congr 1
        change older.length < r.val at qr
        omega
    rw [suffix] at occurs
    simpa only [keyAt] using empty (word.get r) occurs

theorem mem_warm_ancestors_iff_visible {word : List α} {p : Fin word.length} {key : α} :
    key ∈ ancestors (word.get p) (cartesian (word.take p.val).reverse) ↔
      ∃ q : Fin word.length, Visible word.get Finset.univ p q ∧ word.get q = key := by
  rw [mem_ancestors_cartesian]
  constructor
  · exact exposed_exists_visible
  · rintro ⟨q,visible,rfl⟩
    exact visible_exposed visible

end DynamicOptimality.Funnel.Warm
