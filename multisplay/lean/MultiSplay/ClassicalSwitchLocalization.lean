import MultiSplay.ClassicalSwitchMarkedFrame

/-!
# Locating a switch below the root preferred component

An owner outside the root preferred path lies inside one annotated opaque
subtree. Its toggle leaves the root skeleton and ordered attachments literally
unchanged. Only the restricted preference state inside that unique hole changes.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.Primary (Key)
open EndpointEncoding

variable {α : Type*}

theorem preferredHoles_contains (state : State) (reference : RawTree α) (address : Key)
    (outside : ¬ RootPreferred state address) :
    ∃ entry ∈ preferredHoles state reference, entry.1.IsPrefix address := by
  induction reference generalizing state address with
  | empty => exact ⟨([], .empty),by simp [preferredHoles],by simp⟩
  | node left pivot right ihl ihr =>
      cases address with
      | nil => exact False.elim (outside (rootPreferred_nil state))
      | cons edge rest =>
          by_cases agrees : state [] = edge
          · have belowOutside : ¬ RootPreferred (below state edge) rest := by
              intro follows
              exact outside ((rootPreferred_cons _ _ _).mpr ⟨agrees,follows⟩)
            cases edge with
            | false =>
                obtain ⟨child,member,ancestor⟩ := ihl (below state false) rest belowOutside
                refine ⟨(false::child.1,child.2),?_,by simpa using ancestor⟩
                simp only [preferredHoles, agrees, Bool.false_eq_true, ↓reduceIte, List.mem_append]
                exact Or.inl (List.mem_map.mpr ⟨child,member,rfl⟩)
            | true =>
                obtain ⟨child,member,ancestor⟩ := ihr (below state true) rest belowOutside
                refine ⟨(true::child.1,child.2),?_,by simpa using ancestor⟩
                simp only [preferredHoles, agrees, ↓reduceIte, List.mem_cons]
                exact Or.inr (List.mem_map.mpr ⟨child,member,rfl⟩)
          · cases edge <;> cases side : state [] <;>
              simp_all only [Bool.true_eq_false, Bool.false_eq_true, not_true_eq_false, not_false_eq_true]
            · exact ⟨([false],left),by simp [preferredHoles, side],by simp⟩
            · exact ⟨([true],right),by simp [preferredHoles, side],by simp⟩

/-- Two distinct holes cannot both contain the same reference address. -/
theorem preferredHoles_prefix_unique (state : State) (reference : RawTree α)
    {first second : Key × RawTree α} {address : Key}
    (firstMember : first ∈ preferredHoles state reference)
    (secondMember : second ∈ preferredHoles state reference)
    (firstPrefix : first.1.IsPrefix address) (secondPrefix : second.1.IsPrefix address) :
    first = second := by
  induction reference generalizing state first second address with
  | empty => exact (List.mem_singleton.mp firstMember).trans (List.mem_singleton.mp secondMember).symm
  | node left pivot right ihl ihr =>
      cases side : state [] with
      | false =>
          simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte, List.mem_append,
            List.mem_singleton] at firstMember secondMember
          rcases firstMember with firstChild | rfl
          · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp firstChild
            obtain ⟨suffix,rfl⟩ := firstPrefix
            rcases secondMember with secondChild | rfl
            · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp secondChild
              have same := ihl (below state false) ha hb (List.prefix_append a.1 suffix)
                (by simpa using secondPrefix)
              exact congrArg (fun entry : Key × RawTree α => (false::entry.1,entry.2)) same
            · simp at secondPrefix
          · obtain ⟨suffix,rfl⟩ := firstPrefix
            rcases secondMember with secondChild | rfl
            · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp secondChild
              simp at secondPrefix
            · rfl
      | true =>
          simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at firstMember secondMember
          rcases firstMember with rfl | firstChild
          · obtain ⟨suffix,rfl⟩ := firstPrefix
            rcases secondMember with rfl | secondChild
            · rfl
            · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp secondChild
              simp at secondPrefix
          · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp firstChild
            obtain ⟨suffix,rfl⟩ := firstPrefix
            rcases secondMember with rfl | secondChild
            · simp at secondPrefix
            · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp secondChild
              have same := ihr (below state true) ha hb (List.prefix_append a.1 suffix)
                (by simpa using secondPrefix)
              exact congrArg (fun entry : Key × RawTree α => (true::entry.1,entry.2)) same

theorem preferredHoles_prefix_free (state : State) (reference : RawTree α)
    {first second : Key × RawTree α}
    (firstMember : first ∈ preferredHoles state reference)
    (secondMember : second ∈ preferredHoles state reference)
    (ancestor : first.1.IsPrefix second.1) : first = second :=
  preferredHoles_prefix_unique state reference firstMember secondMember ancestor (List.prefix_refl _)

theorem preferredHoles_toggle_frame (state : State) (reference : RawTree α)
    {entry : Key × RawTree α} (member : entry ∈ preferredHoles state reference) (suffix : Key) :
    preferred (toggle state (entry.1 ++ suffix)) reference = preferred state reference ∧
    preferredHoles (toggle state (entry.1 ++ suffix)) reference = preferredHoles state reference := by
  induction reference generalizing state entry with
  | empty => exact ⟨rfl,rfl⟩
  | node left pivot right ihl ihr =>
      cases side : state [] with
      | false =>
          simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte, List.mem_append,
            List.mem_singleton] at member
          rcases member with previous | rfl
          · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
            have result := ihl (below state false) present
            have root : toggle state (false::(child.1 ++ suffix)) [] = false := by simp [toggle, side]
            simp only [List.cons_append, List.nil_append, preferred, preferredHoles, root, side, Bool.false_eq_true,
              ↓reduceIte, below_toggle_cons, result.1, result.2, and_self]
          · have root : toggle state (true::suffix) [] = false := by simp [toggle, side]
            have unchanged := below_toggle_other state true false suffix (by decide)
            simp only [List.cons_append, List.nil_append, preferred, preferredHoles, root, side,
              Bool.false_eq_true, ↓reduceIte, unchanged, and_self]
      | true =>
          simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | previous
          · have root : toggle state (false::suffix) [] = true := by simp [toggle, side]
            have unchanged := below_toggle_other state false true suffix (by decide)
            simp only [List.cons_append, List.nil_append, preferred, preferredHoles, root, side,
              ↓reduceIte, unchanged, and_self]
          · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
            have result := ihr (below state true) present
            have root : toggle state (true::(child.1 ++ suffix)) [] = true := by simp [toggle, side]
            simp only [List.cons_append, List.nil_append, preferred, preferredHoles, root, side,
              ↓reduceIte, below_toggle_cons, result.1, result.2, and_self]

theorem restrict_toggle_append (state : State) (address suffix : Key) :
    restrict (toggle state (address ++ suffix)) address = toggle (restrict state address) suffix := by
  funext owner
  simp [restrict_eq, toggle]

/-- Canonical localization supplies the selected opaque subtree and proves
that every other opaque subtree retains its full internal preference state. -/
theorem localize_outside (state : State) (reference : RawTree α) (address : Key)
    (outside : ¬ RootPreferred state address) :
    ∃ entry ∈ preferredHoles state reference, ∃ suffix,
      address = entry.1 ++ suffix ∧
      preferred (toggle state address) reference = preferred state reference ∧
      preferredHoles (toggle state address) reference = preferredHoles state reference ∧
      restrict (toggle state address) entry.1 = toggle (restrict state entry.1) suffix ∧
      ∀ other ∈ preferredHoles state reference, other ≠ entry →
        restrict (toggle state address) other.1 = restrict state other.1 := by
  obtain ⟨entry,member,suffix,rfl⟩ := preferredHoles_contains state reference address outside
  obtain ⟨skeleton,holes⟩ := preferredHoles_toggle_frame state reference member suffix
  refine ⟨entry,member,suffix,rfl,skeleton,holes,restrict_toggle_append state entry.1 suffix,?_⟩
  intro other present different
  apply restrict_toggle_of_not_prefix
  intro ancestor
  exact different (preferredHoles_prefix_unique state reference present member ancestor (List.prefix_append _ _))

end MultiSplay.ClassicalSwitch
