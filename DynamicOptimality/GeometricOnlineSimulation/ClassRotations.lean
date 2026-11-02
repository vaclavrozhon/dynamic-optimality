import DynamicOptimality.GeometricOnlineSimulation.ClassFrameProperty

/-!
# Rotating class skeletons with their interval-indexed holes

A rotation of a class skeleton is the same ordinary rotation after every
older class in its external holes is restored. The interval assigned to
each hole stays unchanged, so arbitrary interval-dependent properties and
the sum of all hole credits are preserved.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

namespace ClassFrame

theorem rotation_property {system : SplitTreeSystem} {before after : RawTree Nat}
    (step : Rotation before after) (source : ClassFrame system before)
    {keyProperty : Nat → Prop}
    {holeProperty : Nat → Nat → ClassTree system → Prop}
    {lower upper : Nat}
    (valid : source.Property keyProperty holeProperty lower upper) :
    ∃ target : ClassFrame system after,
      Rotation source.tree target.tree ∧ target.credit = source.credit ∧
        target.Property keyProperty holeProperty lower upper := by
  induction step generalizing lower upper with
  | rootRight a b c x y =>
      cases source with
      | node front _ back =>
          cases front with
          | node first _ middle =>
              cases valid with
              | node lowerY upperY frontValid backValid keyY =>
                  cases frontValid with
                  | node lowerX upperX firstValid middleValid keyX =>
                      refine ⟨.node first x (.node middle y back),
                        .rootRight first.tree middle.tree back.tree x y, ?_, ?_⟩
                      · simp only [credit, Nat.add_assoc]
                      · exact .node lowerX (by omega) firstValid
                          (.node (by omega) upperY middleValid backValid keyY) keyX
  | rootLeft a b c x y =>
      cases source with
      | node front _ back =>
          cases back with
          | node middle _ last =>
              cases valid with
              | node lowerX upperX frontValid backValid keyX =>
                  cases backValid with
                  | node lowerY upperY middleValid lastValid keyY =>
                      refine ⟨.node (.node front x middle) y last,
                        .rootLeft front.tree middle.tree last.tree x y, ?_, ?_⟩
                      · simp only [credit, Nat.add_assoc]
                      · exact .node (by omega) upperY
                          (.node lowerX (by omega) frontValid middleValid keyX)
                          lastValid keyY
  | leftContext step key right ih =>
      cases source with
      | node front _ back =>
          cases valid with
          | node lowerBound upperBound first last keyValid =>
              obtain ⟨target, rotation, equalCredit, property⟩ := ih front first
              refine ⟨.node target key back, .leftContext rotation key back.tree, ?_,
                .node lowerBound upperBound property last keyValid⟩
              simp only [credit, equalCredit]
  | rightContext left key step ih =>
      cases source with
      | node front _ back =>
          cases valid with
          | node lowerBound upperBound first last keyValid =>
              obtain ⟨target, rotation, equalCredit, property⟩ := ih back last
              refine ⟨.node front key target, .rightContext front.tree key rotation, ?_,
                .node lowerBound upperBound first property keyValid⟩
              simp only [credit, equalCredit]

theorem rotations_property {system : SplitTreeSystem} {before after : RawTree Nat}
    {count : Nat} (run : Rotations before after count)
    (source : ClassFrame system before)
    {keyProperty : Nat → Prop}
    {holeProperty : Nat → Nat → ClassTree system → Prop}
    {lower upper : Nat}
    (valid : source.Property keyProperty holeProperty lower upper) :
    ∃ target : ClassFrame system after,
      Rotations source.tree target.tree count ∧ target.credit = source.credit ∧
        target.Property keyProperty holeProperty lower upper := by
  induction run with
  | refl => exact ⟨source, .refl _, rfl, valid⟩
  | step first rest ih =>
      obtain ⟨middle, firstRotation, firstCredit, firstProperty⟩ :=
        rotation_property first source valid
      obtain ⟨target, restRotations, restCredit, restProperty⟩ := ih middle firstProperty
      exact ⟨target, .step firstRotation restRotations,
        restCredit.trans firstCredit, restProperty⟩

theorem rotations_realizes {system : SplitTreeSystem} {before after : RawTree Nat}
    {count : Nat} (run : Rotations before after count)
    (source : ClassFrame system before) {height : Nat → Int} {time : Int}
    {lower upper : Nat} (valid : source.Realizes height time lower upper) :
    ∃ target : ClassFrame system after,
      Rotations source.tree target.tree count ∧ target.credit = source.credit ∧
        target.Realizes height time lower upper := by
  obtain ⟨target, rotations, equalCredit, property⟩ :=
    rotations_property run source ((realizes_iff_property height time source).mp valid)
  exact ⟨target, rotations, equalCredit,
    (realizes_iff_property height time target).mpr property⟩

end ClassFrame

end DynamicOptimality.GeometricOnlineSimulation
