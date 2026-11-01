import MultiSplay.ClassicalSwitchStart

/-!
# The common event word determined by the actual primary state

The reference address fixes a real pivot, its original ancestor spine, and
both preferred tails. The deepest nonpreferred edge trims the spine to the
current component. Each switch word is evaluated in the state reached after
the preceding switches, in exactly `actualEmissions` order. Auxiliary shapes
and comparator decisions are absent from these definitions.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree BST)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*}

def referenceAt : RawTree α → Key → RawTree α
  | tree, [] => tree
  | .empty, _::_ => .empty
  | .node left _ right, edge::rest => referenceAt (if edge then right else left) rest

def referenceSpine : RawTree α → Key → Spine α
  | _, [] => []
  | .empty, _::_ => []
  | .node left key right, edge::rest =>
      referenceSpine (if edge then right else left) rest ++ [(edge,key)]

def componentSpine (state : State) (reference : RawTree α) (address : Key) : Spine α :=
  (referenceSpine reference address).take (address.length - startDepth state address)

theorem referenceAt_empty (address : Key) : referenceAt (.empty : RawTree α) address = .empty := by
  cases address <;> rfl

theorem referenceAt_append (reference : RawTree α) (first rest : Key) :
    referenceAt reference (first ++ rest) = referenceAt (referenceAt reference first) rest := by
  induction first generalizing reference with
  | nil => rfl
  | cons edge first ih =>
      cases reference with
      | empty => simp [referenceAt, referenceAt_empty]
      | node left key right => simpa only [List.cons_append, referenceAt] using ih (if edge then right else left)

theorem referenceAt_nodeAddress {lower upper key : Nat} (reference : BST lower upper)
    (lo : lower ≤ key) (hi : key < upper) :
    ∃ left right, referenceAt reference.toRaw (nodeAddress reference key) = .node left key right := by
  induction reference with
  | empty => omega
  | @node lower root upper left right ihl ihr =>
      by_cases atRoot : key = root
      · subst key
        exact ⟨DynamicOptimality.BST.toRaw left,DynamicOptimality.BST.toRaw right,
          by simp [nodeAddress, referenceAt, DynamicOptimality.BST.toRaw]⟩
      · by_cases inLeft : key < root
        · simpa only [nodeAddress, if_neg atRoot, if_pos inLeft, DynamicOptimality.BST.toRaw,
            referenceAt, Bool.false_eq_true, ↓reduceIte] using ihl lo inLeft
        · simpa only [nodeAddress, if_neg atRoot, if_neg inLeft, DynamicOptimality.BST.toRaw,
            referenceAt, ↓reduceIte] using ihr (by omega) hi

theorem referenceAt_prefix_nonempty {reference : RawTree α} {address owner : Key}
    (real : referenceAt reference address ≠ .empty) (ancestor : owner.IsPrefix address) :
    referenceAt reference owner ≠ .empty := by
  obtain ⟨rest,rfl⟩ := ancestor
  intro absent
  apply real
  rw [referenceAt_append, absent, referenceAt_empty]

theorem actualEmissions_real {lower upper key : Nat} (reference : BST lower upper)
    (lo : lower ≤ key) (hi : key < upper) (state : State) {owner : Key}
    (emitted : owner ∈ actualEmissions state (nodeAddress reference key)) :
    referenceAt reference.toRaw owner ≠ .empty := by
  obtain ⟨left,right,found⟩ := referenceAt_nodeAddress reference lo hi
  apply referenceAt_prefix_nonempty (address := nodeAddress reference key) (by simp [found])
  exact ascendingEmissions_prefix ((actualEmissions_perm state _).mem_iff.mp emitted)

theorem Path.referenceSpine {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    referenceSpine reference address = spine := by
  induction path with
  | here => rfl
  | left agrees rest ih => simpa only [ClassicalSwitch.referenceSpine, Bool.false_eq_true, ↓reduceIte] using congrArg (· ++ [_]) ih
  | right agrees rest ih => simpa only [ClassicalSwitch.referenceSpine, ↓reduceIte] using congrArg (· ++ [_]) ih

theorem Path.referenceAt {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    referenceAt reference address = focus := by
  induction path with
  | here => rfl
  | left agrees rest ih => simpa only [ClassicalSwitch.referenceAt, Bool.false_eq_true, ↓reduceIte] using ih
  | right agrees rest ih => simpa only [ClassicalSwitch.referenceAt, ↓reduceIte] using ih

theorem Path.rootPreferred {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    RootPreferred state address := by
  induction path with
  | here => exact rootPreferred_nil _
  | left agrees rest ih => exact (rootPreferred_cons _ _ _).mpr ⟨agrees,ih⟩
  | right agrees rest ih => exact (rootPreferred_cons _ _ _).mpr ⟨agrees,ih⟩

theorem Path.componentSpine {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    componentSpine state reference address = spine := by
  have depth : spine.length = address.length := by
    simpa only [List.length_reverse, List.length_map] using congrArg List.length path.address
  simp [ClassicalSwitch.componentSpine, path.referenceSpine, (startDepth_zero _ _).mpr path.rootPreferred, ← depth]

def eventWord (reference : RawTree α) (state : State) (owner : Key) : List (Event α) :=
  match referenceAt reference owner with
  | .empty => []
  | .node left pivot right =>
      let spine := componentSpine state reference owner
      let current := restrict state owner
      word (state owner) spine.lower spine.upper
        (inorder (tail current (state owner) (.node left pivot right)))
        (inorder (tail current (!(state owner)) (.node left pivot right))) pivot

def requestWord (reference : RawTree α) (state : State) (address : Key) : List (Event α) :=
  (schedule state (actualEmissions state address)).flatMap fun entry => eventWord reference entry.1 entry.2

def historyWord (reference : RawTree α) (state : State) : List Key → List (Event α)
  | [] => []
  | address::rest => requestWord reference state address ++ historyWord reference (nodeStep state address) rest

theorem requestWord_final (reference : RawTree α) (state : State) (address : Key) :
    requestWord reference state address =
      ((schedule state (ancestorEmissions state address).reverse).flatMap fun entry =>
        eventWord reference entry.1 entry.2) ++ eventWord reference (beforeFinal state address) address := by
  simp [requestWord, schedule_actual, List.flatMap_append]

theorem eventWord_structural_le_six (reference : RawTree α) (state : State) (owner : Key) :
    structuralCount (eventWord reference state owner) ≤ 6 := by
  unfold eventWord
  split
  · simp [structuralCount]
  · exact word_structural_le_six _ _ _ _ _ _

theorem eventWord_structural_ge_two {reference : RawTree α} (state : State) (owner : Key)
    (real : referenceAt reference owner ≠ .empty) :
    2 ≤ structuralCount (eventWord reference state owner) := by
  unfold eventWord
  split
  · contradiction
  · exact word_structural_pos _ _ _ _ _ _

theorem structuralCount_append (first rest : List (Event α)) :
    structuralCount (first ++ rest) = structuralCount first + structuralCount rest := by
  simp [structuralCount, List.sum_append]

theorem scheduleWord_structural_le (reference : RawTree α) (state : State) (owners : List Key) :
    structuralCount ((schedule state owners).flatMap fun entry => eventWord reference entry.1 entry.2) ≤
      6 * owners.length := by
  induction owners generalizing state with
  | nil => simp [schedule, structuralCount]
  | cons owner rest ih =>
      have head := eventWord_structural_le_six reference state owner
      have tail := ih (toggle state owner)
      simp only [schedule, List.flatMap_cons, structuralCount_append, List.length_cons]
      omega

theorem requestWord_structural_le (reference : RawTree α) (state : State) (address : Key) :
    structuralCount (requestWord reference state address) ≤ 6 * (actualEmissions state address).length :=
  scheduleWord_structural_le reference state _

theorem scheduleWord_structural_ge (reference : RawTree α) (state : State) (owners : List Key)
    (real : ∀ owner ∈ owners, referenceAt reference owner ≠ .empty) :
    2 * owners.length ≤
      structuralCount ((schedule state owners).flatMap fun entry => eventWord reference entry.1 entry.2) := by
  induction owners generalizing state with
  | nil => simp [schedule, structuralCount]
  | cons owner rest ih =>
      have head := eventWord_structural_ge_two state owner (real owner (by simp))
      have tail := ih (toggle state owner) (fun next member => real next (by simp [member]))
      simp only [schedule, List.flatMap_cons, structuralCount_append, List.length_cons]
      omega

theorem requestWord_structural_ge (reference : RawTree α) (state : State) (address : Key)
    (real : referenceAt reference address ≠ .empty) :
    2 * (actualEmissions state address).length ≤ structuralCount (requestWord reference state address) := by
  apply scheduleWord_structural_ge
  intro owner member
  exact referenceAt_prefix_nonempty real
    (ascendingEmissions_prefix ((actualEmissions_perm state address).mem_iff.mp member))

theorem historyWord_structural_le (reference : RawTree α) (state : State) (addresses : List Key) :
    structuralCount (historyWord reference state addresses) ≤ 6 * (actualHistory state addresses).length := by
  induction addresses generalizing state with
  | nil => simp [historyWord, actualHistory, structuralCount]
  | cons address rest ih =>
      have head := requestWord_structural_le reference state address
      have tail := ih (nodeStep state address)
      simp only [historyWord, structuralCount_append, actualHistory, List.length_append]
      omega

theorem historyWord_structural_ge (reference : RawTree α) (state : State) (addresses : List Key)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty) :
    2 * (actualHistory state addresses).length ≤ structuralCount (historyWord reference state addresses) := by
  induction addresses generalizing state with
  | nil => simp [historyWord, actualHistory, structuralCount]
  | cons address rest ih =>
      have head := requestWord_structural_ge reference state address (real address (by simp))
      have tail := ih (nodeStep state address) (fun next member => real next (by simp [member]))
      simp only [historyWord, structuralCount_append, actualHistory, List.length_append]
      omega

end MultiSplay.ClassicalSwitch
