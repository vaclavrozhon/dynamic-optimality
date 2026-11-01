import MultiSplay.InterfacePackingAlgebra
import MultiSplay.InterfaceCommonJoin

/-! # Selecting an entire region containing two current components -/

noncomputable section

namespace MultiSplay.InterfacePacking

open Splay.Interface

variable {n m l r : Nat} {params : Parameters}

def neutral (n : Nat) : State n := ⟨[], fun _ => 1⟩

theorem neutral_closed (n : Nat) : Closed (neutral n) := by
  constructor
  · intro block member
    cases member
  · intro x
    rfl

theorem value_outside (archive : State m) (components : List (Component m)) (x : Element m)
    (outside : ∀ component ∈ components, x ∉ Set.range component.element) :
    (pack archive components).value x = archive.value x := by
  induction components with
  | nil => rfl
  | cons head tail ih =>
      rw [pack, InterfacePrefix.value_outside _ _ _ _ (outside head (List.mem_cons_self))]
      exact ih (fun component member => outside component (List.mem_cons_of_mem _ member))

theorem prefix_neutral (element : Element n → Element m) (injective : Function.Injective element)
    (frame : State m) (values : ∀ x, frame.value (element x) = 1) :
    InterfacePrefix.state element frame (neutral n) = frame := by
  apply congrArg₂ State.mk
  · simp [InterfacePrefix.state, neutral]
  · funext x
    by_cases inside : x ∈ Set.range element
    · obtain ⟨y, rfl⟩ := inside
      exact (InterfacePrefix.value_image element injective _ _ y).trans (values y).symm
    · exact InterfacePrefix.value_outside element _ _ _ inside

/-- A common parent region has a frame determined by the other components.
Only geometric disjointness is supplied; no execution or cost witness is assumed. -/
def regionFrame (element : Element n → Element m) (injective : Function.Injective element)
    (source : State n) (children : List (Component n))
    (localEq : InterfacePermutation.Equivalent source (pack (neutral n) children))
    (archive : State m) (closed : Closed archive) (others : List (Component m))
    (separate : others.Pairwise Component.Disjoint)
    (sources : ∀ component ∈ others, component.source.Valid params)
    (disjoint : ∀ component ∈ others, ∀ x y, element x ≠ component.element y)
    (whole : State m)
    (represented : InterfacePermutation.Equivalent
      (pack archive (children.map (Component.embed element injective) ++ others)) whole) :
    InterfaceFramedTrace.Framed params source whole where
  element := element
  injective := injective
  frame := pack archive others
  passive := passive_pack element archive others (closed.passive element)
    (fun component member x y => (disjoint component member y x).symm)
  frameValid := valid archive others closed.valid separate sources (fun component _ => closed.passive component.element)
  equivalent := by
    have prefixed := localEq.prefix element (pack archive others)
    rw [pack_embed element injective] at prefixed
    have values : ∀ x, (pack archive others).value (element x) = 1 := by
      intro x
      rw [value_outside]
      · exact closed.values _
      · intro component member
        rintro ⟨y, same⟩
        exact disjoint component member x y same.symm
    rw [prefix_neutral element injective _ values, ← pack_append] at prefixed
    exact ⟨prefixed.1.trans represented.1, prefixed.2.trans represented.2⟩

def leftJoinComponent (a : State l) (r : Nat) : Component (0+l+1+r) :=
  ⟨l, a, JoinIntervals.leftEmbedding l r, RankEmbedding.external_injective _ _⟩

def rightJoinComponent (l : Nat) (b : State r) : Component (0+l+1+r) :=
  ⟨r, b, JoinIntervals.rightEmbedding l r, RankEmbedding.external_injective _ _⟩

theorem join_initial_packed (a : State l) (b : State r) :
    InterfacePermutation.Equivalent (InterfaceCommonJoin.initial a b)
      (pack (neutral (0+l+1+r)) [leftJoinComponent a r, rightJoinComponent l b]) := by
  constructor
  · simpa only [InterfaceCommonJoin.initial, InterfaceSum.state, pack, InterfacePrefix.state,
      neutral, leftJoinComponent, rightJoinComponent, List.map_append, List.nil_append] using
      (List.perm_append_comm :
        ((a.blocks.map (InterfaceEmbedding.block (JoinIntervals.leftEmbedding l r))).map InterfaceHistory.observable ++
          (b.blocks.map (InterfaceEmbedding.block (JoinIntervals.rightEmbedding l r))).map InterfaceHistory.observable).Perm
        ((b.blocks.map (InterfaceEmbedding.block (JoinIntervals.rightEmbedding l r))).map InterfaceHistory.observable ++
          (a.blocks.map (InterfaceEmbedding.block (JoinIntervals.leftEmbedding l r))).map InterfaceHistory.observable))
  · rfl

end MultiSplay.InterfacePacking
