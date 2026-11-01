import MultiSplay.InterfaceFrameComposition

/-!
# Packing disjoint current components into one persistent interface

Every component retains its own universe and actual block records. `pack`
overlays their values on a passive archive and concatenates their blocks.
Disjointness concerns element images, including the local growing creators.
The archived shrinking creators need not belong to any active component.
-/

namespace MultiSplay.InterfacePacking

open Splay.Interface

variable {m : Nat}

structure Component (m : Nat) where
  size : Nat
  source : State size
  element : Element size → Element m
  injective : Function.Injective element

def Component.Disjoint (a b : Component m) : Prop := ∀ x y, a.element x ≠ b.element y

theorem Component.Disjoint.symm {a b : Component m} (disjoint : a.Disjoint b) : b.Disjoint a :=
  fun y x => (disjoint x y).symm

noncomputable def pack (archive : State m) : List (Component m) → State m
  | [] => archive
  | head :: tail => InterfacePrefix.state head.element (pack archive tail) head.source

theorem passive_prefix {n k : Nat} (active : Element n → Element m) (other : Element k → Element m)
    (archive : State m) (source : State k) (passive : InterfacePrefix.Passive active archive)
    (disjoint : ∀ x y, other x ≠ active y) :
    InterfacePrefix.Passive active (InterfacePrefix.state other archive source) := by
  constructor
  · intro x member y same
    rw [InterfacePrefix.allElements] at member
    rcases List.mem_append.mp member with old | fresh
    · exact passive.elements x old y same
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp fresh
      exact disjoint z y same
  · intro block member growing y same
    rcases List.mem_append.mp member with old | fresh
    · exact passive.creators block old growing y same
    · obtain ⟨original, _, rfl⟩ := List.mem_map.mp fresh
      exact disjoint original.creator y same

theorem passive_pack {n : Nat} (active : Element n → Element m) (archive : State m)
    (components : List (Component m)) (passive : InterfacePrefix.Passive active archive)
    (disjoint : ∀ component ∈ components, ∀ x y, component.element x ≠ active y) :
    InterfacePrefix.Passive active (pack archive components) := by
  induction components with
  | nil => exact passive
  | cons head tail ih =>
      exact passive_prefix active head.element (pack archive tail) head.source
        (ih (fun component member => disjoint component (List.mem_cons_of_mem _ member)))
        (disjoint head (List.mem_cons_self))

theorem valid {params : Parameters} (archive : State m) (components : List (Component m))
    (archiveValid : archive.Valid params) (separate : components.Pairwise Component.Disjoint)
    (sources : ∀ component ∈ components, component.source.Valid params)
    (passive : ∀ component ∈ components, InterfacePrefix.Passive component.element archive) :
    (pack archive components).Valid params := by
  induction components with
  | nil => exact archiveValid
  | cons head tail ih =>
      obtain ⟨cross, separateTail⟩ := List.pairwise_cons.mp separate
      apply InterfacePrefix.valid head.element head.injective (pack archive tail)
        (passive_pack head.element archive tail (passive head (List.mem_cons_self))
          (fun component member => (cross component member).symm))
      · exact ih separateTail (fun component member => sources component (List.mem_cons_of_mem _ member))
          (fun component member => passive component (List.mem_cons_of_mem _ member))
      · exact sources head (List.mem_cons_self)

/-- Extracting the leading component is constructive and keeps the entire
remaining packed history as its passive frame. -/
noncomputable def headFrame {params : Parameters} (archive : State m) (head : Component m) (tail : List (Component m))
    (archiveValid : archive.Valid params) (separate : (head :: tail).Pairwise Component.Disjoint)
    (sources : ∀ component ∈ tail, component.source.Valid params)
    (passive : ∀ component ∈ head :: tail, InterfacePrefix.Passive component.element archive) :
    InterfaceFramedTrace.Framed params head.source (pack archive (head :: tail)) where
  element := head.element
  injective := head.injective
  frame := pack archive tail
  passive := passive_pack head.element archive tail (passive head (List.mem_cons_self))
    (fun component member => ((List.pairwise_cons.mp separate).1 component member).symm)
  frameValid := valid archive tail archiveValid (List.pairwise_cons.mp separate).2 sources
    (fun component member => passive component (List.mem_cons_of_mem _ member))
  equivalent := ⟨List.Perm.refl _, rfl⟩

theorem equivalent_frame {n : Nat} {a b : State m} (same : InterfacePermutation.Equivalent a b)
    (element : Element n → Element m) (source : State n) :
    InterfacePermutation.Equivalent (InterfacePrefix.state element a source) (InterfacePrefix.state element b source) := by
  constructor
  · simpa only [InterfacePrefix.state, List.map_append] using same.1.append_right (source.blocks.map (InterfaceEmbedding.block element) |>.map InterfaceHistory.observable)
  · change Function.extend element source.value a.value = Function.extend element source.value b.value
    rw [same.2]

theorem swap (archive : State m) (a b : Component m) (disjoint : a.Disjoint b) :
    InterfacePermutation.Equivalent (pack archive [a,b]) (pack archive [b,a]) := by
  constructor
  · simp only [pack, InterfacePrefix.state, List.map_append]
    simpa only [List.append_assoc] using
      (List.perm_append_comm :
        ((b.source.blocks.map (InterfaceEmbedding.block b.element)).map InterfaceHistory.observable ++
          (a.source.blocks.map (InterfaceEmbedding.block a.element)).map InterfaceHistory.observable).Perm
        ((a.source.blocks.map (InterfaceEmbedding.block a.element)).map InterfaceHistory.observable ++
          (b.source.blocks.map (InterfaceEmbedding.block b.element)).map InterfaceHistory.observable)).append_left
            (archive.blocks.map InterfaceHistory.observable)
  · funext x
    change (InterfacePrefix.state a.element (InterfacePrefix.state b.element archive b.source) a.source).value x =
      (InterfacePrefix.state b.element (InterfacePrefix.state a.element archive a.source) b.source).value x
    by_cases inA : x ∈ Set.range a.element
    · obtain ⟨y, rfl⟩ := inA
      rw [InterfacePrefix.value_image a.element a.injective,
        InterfacePrefix.value_outside b.element _ _ _ (by rintro ⟨z, same⟩; exact disjoint y z same.symm),
        InterfacePrefix.value_image a.element a.injective]
    · by_cases inB : x ∈ Set.range b.element
      · obtain ⟨y, rfl⟩ := inB
        rw [InterfacePrefix.value_outside a.element _ _ _ inA,
          InterfacePrefix.value_image b.element b.injective, InterfacePrefix.value_image b.element b.injective]
      · rw [InterfacePrefix.value_outside a.element _ _ _ inA, InterfacePrefix.value_outside b.element _ _ _ inB,
          InterfacePrefix.value_outside b.element _ _ _ inB, InterfacePrefix.value_outside a.element _ _ _ inA]


theorem perm (archive : State m) {before after : List (Component m)} (order : before.Perm after)
    (separate : before.Pairwise Component.Disjoint) :
    InterfacePermutation.Equivalent (pack archive before) (pack archive after) := by
  induction order with
  | nil => exact ⟨List.Perm.refl _, rfl⟩
  | cons head order ih =>
      exact equivalent_frame (ih (List.pairwise_cons.mp separate).2) head.element head.source
  | swap a b tail =>
      have cross := (List.pairwise_cons.mp separate).1 _ (List.mem_cons_self)
      exact swap (pack archive tail) b a cross
  | trans first second ih₁ ih₂ =>
      have left := ih₁ separate
      have right := ih₂ (first.pairwise separate (fun h => h.symm))
      exact ⟨left.1.trans right.1, left.2.trans right.2⟩

/-- A component at any list position has a frame constructed from the archive
and the other current components. No placement or history oracle is needed. -/
noncomputable def componentFrame {params : Parameters} (archive : State m) (head : Component m)
    (front back : List (Component m)) (archiveValid : archive.Valid params)
    (separate : (front ++ head :: back).Pairwise Component.Disjoint)
    (sources : ∀ component ∈ front ++ back, component.source.Valid params)
    (passive : ∀ component ∈ front ++ head :: back, InterfacePrefix.Passive component.element archive) :
    InterfaceFramedTrace.Framed params head.source (pack archive (front ++ head :: back)) := by
  have order : (front ++ head :: back).Perm (head :: (front ++ back)) := List.perm_middle
  let result := headFrame archive head (front ++ back) archiveValid
    (order.pairwise separate (fun h => h.symm)) sources (fun component member => passive component (order.mem_iff.mpr member))
  have same := perm archive order separate
  exact {result with equivalent := ⟨same.1.symm, same.2.symm⟩}

end MultiSplay.InterfacePacking
