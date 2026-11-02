import DynamicOptimality.GeometricOnlineSimulation.ClassTree

/-! # Interval properties carried by binary class frames -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

namespace ClassFrame

/-- Skeleton keys satisfy `keyProperty`; each literal hole satisfies its
interval-dependent property. The full half-open interval is preserved. -/
inductive Property {system : SplitTreeSystem} (keyProperty : Nat → Prop)
    (holeProperty : Nat → Nat → ClassTree system → Prop) :
    Nat → Nat → {skeleton : RawTree Nat} → ClassFrame system skeleton → Prop
  | hole {lower upper} {child : ClassTree system}
      (valid : holeProperty lower upper child) :
      Property keyProperty holeProperty lower upper (.hole child)
  | node {lower key upper} {left right : RawTree Nat}
      {front : ClassFrame system left} {back : ClassFrame system right}
      (lowerBound : lower ≤ key) (upperBound : key < upper)
      (first : Property keyProperty holeProperty lower key front)
      (last : Property keyProperty holeProperty (key+1) upper back)
      (valid : keyProperty key) :
      Property keyProperty holeProperty lower upper (.node front key back)

theorem realizes_iff_property {system : SplitTreeSystem} (height : Nat → Int)
    (time : Int) {lower upper : Nat} {skeleton : RawTree Nat}
    (frame : ClassFrame system skeleton) :
    frame.Realizes height time lower upper ↔
      frame.Property (fun key => height key = time)
        (fun lo hi child => child.Realizes height lo hi ∧
          ∀ key, lo ≤ key → key < hi → height key < time) lower upper := by
  induction skeleton generalizing lower upper with
  | empty =>
      cases frame with
      | hole child =>
          constructor
          · intro valid
            cases valid with
            | hole tree older => exact .hole ⟨tree, older⟩
          · intro valid
            cases valid with
            | hole both => exact .hole both.1 both.2
  | node left key right ihl ihr =>
      cases frame with
      | node front _ back =>
          constructor
          · intro valid
            cases valid with
            | node lowerBound upperBound first last sameTime =>
                exact .node lowerBound upperBound ((ihl front).mp first)
                  ((ihr back).mp last) sameTime
          · intro valid
            cases valid with
            | node lowerBound upperBound first last sameTime =>
                exact .node lowerBound upperBound ((ihl front).mpr first)
                  ((ihr back).mpr last) sameTime

end ClassFrame

end DynamicOptimality.GeometricOnlineSimulation
