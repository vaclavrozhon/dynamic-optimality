import DynamicOptimality.Funnel.WarmVisibility
import DynamicOptimality.Funnel.ChargeExistence

/-! # Visibility and ancestry inside convex key components

A monotone key-label map describes ordered, disjoint intervals: a component
is one fiber of the map. Closed rectangles between keys of one component
cannot contain a key from another component. The exact warm-tree ancestry
invariance below is the interval-structure lemma used by composition.
-/

namespace DynamicOptimality.Funnel

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem same_label_between (label : α → β) (mono : Monotone label)
    {x y z : α} (same : label x = label y) (between : Between x y z) :
    label z = label x := by
  rcases between with ⟨xz,zy⟩ | ⟨yz,zx⟩
  · exact le_antisymm (by simpa only [same] using mono zy) (mono xz)
  · exact le_antisymm (mono zx) (by simpa only [same] using mono yz)

/-- Foreign components never block a rectangle internal to one component. -/
theorem visible_convex_component {m : Nat} (word : Fin m → α)
    (active : Finset (Fin m)) (label : α → β) (mono : Monotone label)
    {p q : Fin m} (same : label (word q) = label (word p)) :
    Visible word (active.filter (fun r => label (word r) = label (word p))) p q ↔
      Visible word active p q := by
  constructor
  · rintro ⟨hp,hq,qp,different,empty⟩
    refine ⟨(Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hq).1,qp,different,?_⟩
    intro r hr qr rp between
    have color := same_label_between label mono same between
    exact empty r (Finset.mem_filter.mpr ⟨hr,color.trans same⟩) qr rp between
  · intro visible
    apply visible.restrict (Finset.filter_subset _ _)
    · exact Finset.mem_filter.mpr ⟨visible.1,rfl⟩
    · exact Finset.mem_filter.mpr ⟨visible.2.1,same⟩

namespace Warm

/-- Ancestry among keys of one interval survives in the physical Cartesian tree. -/
theorem convex_ancestor_iff (history : List α) (label : α → β) (mono : Monotone label)
    (x q : α) (same : label q = label x) :
    q ∈ ancestors x (cartesian (history.filter (fun y => decide (label y = label x)))) ↔
      q ∈ ancestors x (cartesian history) := by
  rw [mem_ancestors_cartesian,mem_ancestors_cartesian]
  apply exposed_filter
  intro z hz
  apply decide_eq_true
  exact (same_label_between label mono same hz).trans same

/-- The most recent key of a component lies on every subsequent search into
that component, including an insertion search for a previously unseen key. -/
theorem active_root_ancestor (history : List α) (label : α → β) (mono : Monotone label)
    (x root : α) (rest : List α)
    (component : history.filter (fun y => decide (label y = label x)) = root :: rest)
    (different : root ≠ x) : root ∈ ancestors x (cartesian history) := by
  have root_mem : root ∈ history.filter (fun y => decide (label y = label x)) := by
    rw [component]
    exact List.mem_cons_self
  have same : label root = label x := of_decide_eq_true (List.mem_filter.mp root_mem).2
  apply (convex_ancestor_iff history label mono x root same).mp
  rw [component,mem_ancestors_cartesian]
  exact Or.inl ⟨rfl,different⟩

end Warm
end DynamicOptimality.Funnel
