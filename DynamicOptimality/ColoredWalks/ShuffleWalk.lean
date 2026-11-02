import DynamicOptimality.ColoredWalks.ShuffleMetric
import DynamicOptimality.MultiFinger.StaticWalk

/-! # Persistent fingers for an interleaving of colored walks

An unseen source starts at its first requested key. Once it has been seen,
its finger keeps its previous position through all events of other sources.
The backwards existence proof below chooses only these initial positions;
the resulting `ShortWalk` is an actual forward execution without resets.
-/

namespace DynamicOptimality.ColoredWalks.Encoding

open ChaCha.MTR MultiFinger

variable {n k : Nat} {full : List (Fin k × Fin n)}

def Known (encoding : Encoding full) (seen : Fin k → Option (Fin n)) : Prop :=
  ∀ color key, seen color = some key → (color,key) ∈ full

def Filled (encoding : Encoding full) (seen : Fin k → Option (Fin n))
    (positions : Fin encoding.count → Nat) : Prop :=
  ∀ color key, seen color = some key →
    positions (encoding.color color) = (encoding.encode (color,key)).val

def InRange (encoding : Encoding full) (positions : Fin encoding.count → Nat) : Prop :=
  ∀ index, positions index < encoding.size

def encodedEvents (encoding : Encoding full) (events : List (Fin k × Fin n)) :
    List (Fin encoding.count × Nat) :=
  events.map (fun event => (encoding.color event.1,(encoding.encode event).val))

theorem exists_filled (encoding : Encoding full) {seen : Fin k → Option (Fin n)}
    (known : encoding.Known seen) :
    ∃ positions, encoding.InRange positions ∧ encoding.Filled seen positions := by
  classical
  let candidates (index : Fin encoding.count) : Prop :=
    ∃ color key, seen color = some key ∧ encoding.color color = index
  let positions (index : Fin encoding.count) : Nat :=
    if present : candidates index then
      (encoding.encode (Classical.choose present,Classical.choose (Classical.choose_spec present))).val
    else 0
  refine ⟨positions,?_,?_⟩
  · intro index
    dsimp only [positions]
    split
    · exact (encoding.encode _).isLt
    · exact encoding.size_pos
  · intro color key atKey
    have present : candidates (encoding.color color) := ⟨color,key,atKey,rfl⟩
    dsimp only [positions]
    rw [dif_pos present]
    let other := Classical.choose present
    let otherKey := Classical.choose (Classical.choose_spec present)
    have otherSpec : seen other = some otherKey ∧ encoding.color other = encoding.color color :=
      Classical.choose_spec (Classical.choose_spec present)
    have sameColor : other = color := encoding.color_injective_on_events
      (known other otherKey otherSpec.1) (known color key atKey) otherSpec.2
    have sameKey : otherKey = key := by
      apply Option.some.inj
      exact otherSpec.1.symm.trans (sameColor ▸ atKey)
    change (encoding.encode (other,otherKey)).val = _
    rw [sameColor,sameKey]

theorem known_update (encoding : Encoding full) {seen : Fin k → Option (Fin n)}
    (known : encoding.Known seen) (color : Fin k) (key : Fin n)
    (present : (color,key) ∈ full) :
    encoding.Known (Function.update seen color (some key)) := by
  intro other value found
  by_cases same : other = color
  · subst other
    rw [Function.update_self] at found
    cases Option.some.inj found
    exact present
  · exact known other value (by simpa only [Function.update_of_ne same] using found)

theorem short_walk (encoding : Encoding full) (sets : Fin k → Finset (Fin n))
    (members : ∀ event ∈ full, event.2 ∈ sets event.1)
    {tree : RawTree Nat} {height : Nat}
    (embedding : Embedding encoding.natLabel (List.range encoding.size) height tree)
    {seen : Fin k → Option (Fin n)} {events : List (Fin k × Fin n)}
    (walk : WalkFrom sets seen events) (known : encoding.Known seen)
    (contained : ∀ event ∈ events, event ∈ full) :
    ∃ positions, encoding.InRange positions ∧ encoding.Filled seen positions ∧
      ShortWalk tree encoding.count (4*height) positions (encoding.encodedEvents events) := by
  induction walk with
  | nil seen =>
    obtain ⟨positions,bounded,filled⟩ := encoding.exists_filled known
    exact ⟨positions,bounded,filled,.nil positions⟩
  | @cons seen events color key present step rest ih =>
    have current : (color,key) ∈ full := contained _ (by simp)
    have tailMem : ∀ event ∈ events, event ∈ full := fun event member =>
      contained event (List.mem_cons_of_mem _ member)
    obtain ⟨middle,middleRange,middleFilled,tail⟩ :=
      ih (encoding.known_update known color key current) tailMem
    have middleAt : middle (encoding.color color) = (encoding.encode (color,key)).val :=
      middleFilled color key (Function.update_self _ _ _)
    let old : Nat := match seen color with
      | some previous => (encoding.encode (color,previous)).val
      | none => (encoding.encode (color,key)).val
    let positions := Function.update middle (encoding.color color) old
    have oldRange : old < encoding.size := by
      dsimp only [old]
      split <;> exact (encoding.encode _).isLt
    have bounded : encoding.InRange positions := by
      intro index
      by_cases same : index = encoding.color color
      · subst index
        simpa only [positions,Function.update_self] using oldRange
      · simpa only [positions,Function.update_of_ne same] using middleRange index
    have filled : encoding.Filled seen positions := by
      intro other value found
      by_cases same : other = color
      · subst other
        simp only [positions,Function.update_self,old,found]
      · have separate : encoding.color other ≠ encoding.color color := by
          intro equal
          exact same (encoding.color_injective_on_events (known other value found) current equal)
        have still : Function.update seen color (some key) other = some value := by
          simpa only [Function.update_of_ne same] using found
        simpa only [positions,Function.update_of_ne separate] using middleFilled other value still
    have close : DistanceLE tree (positions (encoding.color color))
        (encoding.encode (color,key)).val (4*height) := by
      simp only [positions,Function.update_self]
      cases previous : seen color with
      | none =>
        simp only [old,previous]
        exact encoding.stay_distance embedding _
      | some value =>
        simp only [old,previous]
        exact encoding.neighbor_distance sets members embedding color value key
          (known color value previous) current (step value previous)
    have updated : Function.update positions (encoding.color color)
        (encoding.encode (color,key)).val = middle := by
      funext index
      by_cases same : index = encoding.color color
      · subst index
        simpa only [Function.update_self] using middleAt.symm
      · simp only [Function.update_of_ne same,positions]
    refine ⟨positions,bounded,filled,?_⟩
    change ShortWalk tree encoding.count (4*height) positions
      ((encoding.color color,(encoding.encode (color,key)).val)::encoding.encodedEvents events)
    exact .cons _ _ close (updated.symm ▸ tail)

theorem shuffle_short_walk (encoding : Encoding full) (sets : Fin k → Finset (Fin n))
    (walk : ShuffleWalk sets full) {tree : RawTree Nat} {height : Nat}
    (embedding : Embedding encoding.natLabel (List.range encoding.size) height tree) :
    ∃ positions, encoding.InRange positions ∧
      ShortWalk tree encoding.count (4*height) positions (encoding.encodedEvents full) := by
  obtain ⟨positions,bounded,_,actual⟩ := encoding.short_walk sets walk.members embedding walk
    (by intro color key impossible; cases impossible) (by intro event member; exact member)
  exact ⟨positions,bounded,actual⟩

end DynamicOptimality.ColoredWalks.Encoding
