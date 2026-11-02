import MultiSplay.GlobalPreferredAttached
import MultiSplay.GlobalPreferredRepartitionReflection
import MultiSplay.ClassicalSwitchMarkedFrame

/-! # Preservation of the physical root-component invariant -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

private theorem size_of_keys {a b : RawTree α} (keys : a.inorder = b.inorder) :
    a.size = b.size := by
  simpa only [Tree.length_inorder] using congrArg List.length keys

/-- The literal ordered-hole exchange preserves the recursively attached
reference subtrees. This closes the physical attachment premise for the
next switch; equality of component domains alone would not suffice. -/
theorem repartition_components {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right))
    {before foreign main old : MarkedTree α}
    (represented : Component state reference before)
    (foreignRep : Component (restrict state (address ++ [!(state address)]))
      (if state address then left else right) foreign)
    (mainKeys : main.skeleton.inorder = (preferred (toggle state address) reference).inorder)
    (oldKeys : old.skeleton.inorder =
      (tail (restrict state address) (state address) (.node left pivot right)).inorder)
    (partition : Repartition (state address) spine.lower before foreign main old) :
    Component (toggle state address) reference main ∧
      Component (restrict state (address ++ [state address]))
        (if state address then right else left) old := by
  obtain ⟨front, back, beforeHoles, afterHoles, frontLength⟩ := path.holes_switch
  obtain ⟨actualFront, actualBack, actualLength, beforeActual, afterActual⟩ := partition
  have attached := represented.attached
  rw [beforeHoles, beforeActual] at attached
  have aligned : front.length = actualFront.length := frontLength.trans actualLength.symm
  have assembled : Attached state (preferredHoles (toggle state address) reference) main.holes ∧
      Component (restrict state (address ++ [state address]))
        (if state address then right else left) old := by
    cases direction : state address with
    | false =>
        simp only [direction, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at attached afterHoles afterActual foreignRep oldKeys
        have oldDomain : old.skeleton.inorder =
            (preferred (restrict state (address ++ [false])) left).inorder := by
          simpa [tail, restrict_child] using oldKeys
        have oldLength : (childHoles state address false left).length = old.holes.length := by
          rw [childHoles_length, MarkedTree.holes_length, size_of_keys oldDomain]
        have frontSplit : Attached state front actualFront ∧
            Attached state (childHoles state address false left ++ [(address ++ [true],right)] ++ back)
              (old.holes ++ [foreign.erase] ++ actualBack) :=
          Attached.split (by simpa only [List.append_assoc] using attached) aligned
        obtain ⟨frontAttached, restAttached⟩ := frontSplit
        have oldSplit : Attached state (childHoles state address false left) old.holes ∧
            Attached state ((address ++ [true],right) :: back) (foreign.erase :: actualBack) :=
          Attached.split (by simpa only [List.append_assoc, List.singleton_append] using restAttached) oldLength
        obtain ⟨oldAttached, incomingBack⟩ := oldSplit
        have oldRep : Component (restrict state (address ++ [false])) left old :=
          component_of_attached oldDomain (oldAttached.unprefix (address ++ [false]))
        cases incomingBack with
        | cons incomingRoot backAttached =>
            have foreignAttached := foreignRep.attached.prefix (address ++ [true])
            have middle : Attached state
                ((address ++ [false],left) :: childHoles state address true right)
                (old.erase :: foreign.holes) := .cons oldRep.realizes foreignAttached
            refine ⟨?_,by simpa only [direction, Bool.false_eq_true, ↓reduceIte] using oldRep⟩
            rw [afterHoles, afterActual]
            simpa only [List.singleton_append, List.append_assoc] using
              frontAttached.append (middle.append backAttached)
    | true =>
        simp only [direction, ↓reduceIte, Bool.not_true] at attached afterHoles afterActual foreignRep oldKeys
        have oldDomain : old.skeleton.inorder =
            (preferred (restrict state (address ++ [true])) right).inorder := by
          simpa [tail, restrict_child] using oldKeys
        have oldLength : (childHoles state address true right).length = old.holes.length := by
          rw [childHoles_length, MarkedTree.holes_length, size_of_keys oldDomain]
        have frontSplit : Attached state front actualFront ∧
            Attached state ((address ++ [false],left) :: (childHoles state address true right ++ back))
              (foreign.erase :: (old.holes ++ actualBack)) :=
          Attached.split (by simpa only [Attached, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using attached) aligned
        obtain ⟨frontAttached, restAttached⟩ := frontSplit
        cases restAttached with
        | cons incomingRoot oldBack =>
            have ⟨oldAttached, backAttached⟩ := Attached.split oldBack oldLength
            have oldRep : Component (restrict state (address ++ [true])) right old :=
              component_of_attached oldDomain (oldAttached.unprefix (address ++ [true]))
            have foreignAttached := foreignRep.attached.prefix (address ++ [false])
            have middle := foreignAttached.append
              (show Attached state [(address ++ [true],right)] [old.erase] from
                .cons oldRep.realizes .nil)
            refine ⟨?_,by simpa only [direction, ↓reduceIte] using oldRep⟩
            rw [afterHoles, afterActual]
            simpa only [Attached, childHoles, List.append_assoc] using
              frontAttached.append (middle.append backAttached)
  exact ⟨component_of_attached mainKeys (assembled.1.state_congr fun entry member =>
    path.after_hole_restrict_toggle (by simp) member),assembled.2⟩


theorem repartition_component {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right))
    {before foreign main old : MarkedTree α}
    (represented : Component state reference before)
    (foreignRep : Component (restrict state (address ++ [!(state address)]))
      (if state address then left else right) foreign)
    (mainKeys : main.skeleton.inorder = (preferred (toggle state address) reference).inorder)
    (oldKeys : old.skeleton.inorder =
      (tail (restrict state address) (state address) (.node left pivot right)).inorder)
    (partition : Repartition (state address) spine.lower before foreign main old) :
    Component (toggle state address) reference main :=
  (repartition_components path represented foreignRep mainKeys oldKeys partition).1

end MultiSplay.Global.Preferred
