import MultiSplay.InterfacePackingReplay

/-! # Flattening nested component forests without resetting the archive -/

noncomputable section

namespace MultiSplay.InterfacePacking

open Splay.Interface

variable {n m : Nat}

def Component.embed (element : Element n → Element m) (injective : Function.Injective element)
    (component : Component n) : Component m where
  size := component.size
  source := component.source
  element := element ∘ component.element
  injective := injective.comp component.injective

theorem pack_append (archive : State m) (front back : List (Component m)) :
    pack archive (front ++ back) = pack (pack archive back) front := by
  induction front with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, pack, ih]

theorem equivalent_archive {a b : State m} (same : InterfacePermutation.Equivalent a b)
    (components : List (Component m)) :
    InterfacePermutation.Equivalent (pack a components) (pack b components) := by
  induction components with
  | nil => exact same
  | cons head tail ih => exact equivalent_frame ih head.element head.source

theorem pack_embed (element : Element n → Element m) (injective : Function.Injective element)
    (frame : State m) (archive : State n) (components : List (Component n)) :
    InterfacePrefix.state element frame (pack archive components) =
      pack (InterfacePrefix.state element frame archive) (components.map (Component.embed element injective)) := by
  induction components with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, pack, Component.embed]
      rw [← InterfacePrefix.assoc head.element element head.injective injective, ih]

/-- Moving a whole local archive past unrelated components only permutes records.
Its stored creators and pass counts are unchanged. -/
theorem move_archive (element : Element n → Element m) (injective : Function.Injective element)
    (archive : State n) (frame : State m) (others : List (Component m))
    (disjoint : ∀ component ∈ others, ∀ x y, element x ≠ component.element y) :
    InterfacePermutation.Equivalent
      (InterfacePrefix.state element (pack frame others) archive)
      (pack (InterfacePrefix.state element frame archive) others) := by
  induction others with
  | nil => exact ⟨List.Perm.refl _, rfl⟩
  | cons head tail ih =>
      let added : Component m := ⟨n, archive, element, injective⟩
      have first := swap (pack frame tail) added head (disjoint head (List.mem_cons_self))
      have rest := equivalent_frame (ih (fun component member => disjoint component (List.mem_cons_of_mem _ member)))
        head.element head.source
      exact ⟨first.1.trans rest.1, first.2.trans rest.2⟩

/-- A nested replacement becomes a single packed forest, with all newly retired
records added to the old archive and all other components retained. -/
theorem flatten (element : Element n → Element m) (injective : Function.Injective element)
    (archive : State n) (frame : State m) (children : List (Component n)) (others : List (Component m))
    (disjoint : ∀ component ∈ others, ∀ x y, element x ≠ component.element y) :
    InterfacePermutation.Equivalent
      (InterfacePrefix.state element (pack frame others) (pack archive children))
      (pack (InterfacePrefix.state element frame archive)
        (children.map (Component.embed element injective) ++ others)) := by
  rw [pack_embed, pack_append]
  exact equivalent_archive (move_archive element injective archive frame others disjoint) _

/-- An archive consists of exhausted shrinking records and neutral values.
The historical creators and pass counts remain unrestricted. -/
structure Closed (archive : State m) : Prop where
  blocks : ∀ block ∈ archive.blocks, block.mode = .shrinking ∧ block.elements = []
  values : ∀ x, archive.value x = 1

theorem Closed.passive {archive : State m} (closed : Closed archive) (element : Element n → Element m) :
    InterfacePrefix.Passive element archive := by
  constructor
  · intro x member
    obtain ⟨block, present, contains⟩ := List.mem_flatMap.mp member
    rw [(closed.blocks block present).2] at contains
    exact False.elim (List.not_mem_nil contains)
  · intro block member growing
    have mode := (closed.blocks block member).1
    rw [mode] at growing
    cases growing

theorem Closed.valid {params : Parameters} {archive : State m} (closed : Closed archive) : archive.Valid params := by
  have empty : archive.allElements = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x member
    exact (closed.passive id).elements x member x rfl
  refine ⟨by rw [empty]; exact List.nodup_nil, ?_, ?_⟩
  · intro x
    rw [closed.values]
    have cap := params.valueBound_ge_two
    omega
  · intro creator
    change (archive.blocks.filter _).length ≤ params.growingLimit
    rw [List.filter_eq_nil_iff.mpr ?_]
    · exact Nat.zero_le _
    · intro block member
      simp [(closed.blocks block member).1]

theorem Closed.prefix {frame : State m} {archive : State n} (outer : Closed frame) (inner : Closed archive)
    (element : Element n → Element m) (injective : Function.Injective element) :
    Closed (InterfacePrefix.state element frame archive) := by
  constructor
  · intro block member
    rcases List.mem_append.mp member with old | fresh
    · exact outer.blocks block old
    · obtain ⟨original, present, rfl⟩ := List.mem_map.mp fresh
      have data := inner.blocks original present
      simpa [InterfaceEmbedding.block, data.1, data.2]
  · intro x
    by_cases inside : x ∈ Set.range element
    · obtain ⟨y, rfl⟩ := inside
      rw [InterfacePrefix.value_image element injective]
      exact inner.values y
    · rw [InterfacePrefix.value_outside element _ _ _ inside]
      exact outer.values x

theorem separate_embed (element : Element n → Element m) (injective : Function.Injective element)
    (children : List (Component n)) (separate : children.Pairwise Component.Disjoint) :
    (children.map (Component.embed element injective)).Pairwise Component.Disjoint := by
  rw [List.pairwise_map]
  apply separate.imp
  intro a b disjoint x y same
  exact disjoint x y (injective same)

theorem separate_replacement (element : Element n → Element m) (injective : Function.Injective element)
    (children : List (Component n)) (others : List (Component m))
    (childSeparate : children.Pairwise Component.Disjoint) (otherSeparate : others.Pairwise Component.Disjoint)
    (disjoint : ∀ component ∈ others, ∀ x y, element x ≠ component.element y) :
    (children.map (Component.embed element injective) ++ others).Pairwise Component.Disjoint := by
  rw [List.pairwise_append]
  refine ⟨separate_embed element injective children childSeparate, otherSeparate, ?_⟩
  intro a member b otherMember
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact fun x y => disjoint b otherMember (original.element x) y

end MultiSplay.InterfacePacking
