import MultiSplay.EndpointLedgerEmbedding
import MultiSplay.EndpointPrimary

/-!
# Sparse support of the encoded primary history

Only the original pivots and their two connectors can change preference.
The padding is initialized right and stays right. Consequently initialization
is charged on at most three times the original number of reference nodes.
-/

namespace MultiSplay.EndpointEncoding

open ChaCha.Primary (Key branch owners mem_owners)

def coreNodes (height : Nat) : Finset Key :=
  (owners height).image core ∪
    (owners height).image (fun address => core address ++ [false]) ∪
    (owners height).image (fun address => core address ++ [true])

theorem mem_coreNodes {height : Nat} {owner : Key} : owner ∈ coreNodes height ↔
    ∃ address, address.length < height ∧
      (owner = core address ∨ ∃ side : Bool, owner = core address ++ [side]) := by
  simp only [coreNodes, Finset.mem_union, Finset.mem_image, mem_owners]
  constructor
  · rintro ((⟨address,inside,rfl⟩ | ⟨address,inside,rfl⟩) | ⟨address,inside,rfl⟩)
    · exact ⟨address,inside,Or.inl rfl⟩
    · exact ⟨address,inside,Or.inr ⟨false,rfl⟩⟩
    · exact ⟨address,inside,Or.inr ⟨true,rfl⟩⟩
  · rintro ⟨address,inside,rfl | ⟨side,rfl⟩⟩
    · exact Or.inl (Or.inl ⟨address,inside,rfl⟩)
    · cases side
      · exact Or.inl (Or.inr ⟨address,inside,rfl⟩)
      · exact Or.inr ⟨address,inside,rfl⟩

theorem coreNodes_card (height : Nat) : (coreNodes height).card ≤ 3 * (2^height-1) := by
  have first := Finset.card_union_le ((owners height).image core)
    ((owners height).image (fun address => core address ++ [false]))
  have second := Finset.card_union_le
    ((owners height).image core ∪ (owners height).image (fun address => core address ++ [false]))
    ((owners height).image (fun address => core address ++ [true]))
  have p := Finset.card_image_le (s := owners height) (f := core)
  have l := Finset.card_image_le (s := owners height) (f := fun address => core address ++ [false])
  have r := Finset.card_image_le (s := owners height) (f := fun address => core address ++ [true])
  have count := owners_card_add_one height
  unfold coreNodes
  omega

theorem core_prefix_decomposition (address : Key) (side : Bool) {owner : Key}
    (ancestor : owner.IsPrefix (core address ++ [side])) :
    ∃ original, original.IsPrefix address ∧
      (owner = core original ∨ ∃ edge : Bool, owner = core original ++ [edge]) := by
  induction address generalizing owner with
  | nil =>
      simp only [core, List.nil_append, List.prefix_cons_iff] at ancestor
      rcases ancestor with rfl | ⟨tail,rfl,empty⟩
      · exact ⟨[],List.prefix_refl _,Or.inl rfl⟩
      · have : tail = [] := List.prefix_nil.mp empty
        subst tail
        exact ⟨[],List.prefix_refl _,Or.inr ⟨side,rfl⟩⟩
  | cons edge rest ih =>
      simp only [core, List.cons_append, List.prefix_cons_iff] at ancestor
      rcases ancestor with rfl | ⟨tail,rfl,rfl | ⟨suffix,rfl,remaining⟩⟩
      · exact ⟨[],List.nil_prefix,Or.inl rfl⟩
      · exact ⟨[],List.nil_prefix,Or.inr ⟨edge,rfl⟩⟩
      · obtain ⟨original,pre,eqn⟩ := ih remaining
        refine ⟨edge::original,List.cons_prefix_cons.mpr ⟨rfl,pre⟩,?_⟩
        rcases eqn with rfl | ⟨last,rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨last,rfl⟩

theorem prefix_mem_coreNodes {height : Nat} {address owner : Key} (inside : address.length < height)
    (side : Bool) (ancestor : owner.IsPrefix (core address ++ [side])) : owner ∈ coreNodes height := by
  obtain ⟨original,pre,eqn⟩ := core_prefix_decomposition address side ancestor
  exact mem_coreNodes.mpr ⟨original,lt_of_le_of_lt pre.length_le inside,eqn⟩

theorem coreNodes_prefix_closed {height : Nat} {owner ancestor : Key}
    (member : owner ∈ coreNodes height) (pre : ancestor.IsPrefix owner) : ancestor ∈ coreNodes height := by
  obtain ⟨address,inside,rfl | ⟨side,rfl⟩⟩ := mem_coreNodes.mp member
  · exact prefix_mem_coreNodes inside false (pre.trans (List.prefix_append _ _))
  · exact prefix_mem_coreNodes inside side pre

/-- A left edge of an active copy always starts at a pivot or connector. -/
theorem false_branch_core {height : Nat} {address owner : Key} (inside : address.length < height)
    (side : Bool) (left : branch owner (copy height address side) = some false) : owner ∈ coreNodes height := by
  have pre : owner.IsPrefix (copy height address side) := by
    by_contra absent
    simp [branch,absent] at left
  have letter : (copy height address side)[owner.length]? = some false := by
    simpa only [branch,if_pos pre] using left
  have short : owner.length < (core address ++ [side,!side]).length := by
    by_contra large
    have ge : (core address ++ [side,!side]).length ≤ owner.length := by omega
    unfold copy at letter
    rw [List.getElem?_append_right ge, List.getElem?_replicate] at letter
    split at letter <;> cases letter
  have early : (core address ++ [side]).IsPrefix (copy height address side) := by
    exact ⟨(!side)::List.replicate (2*(height-address.length-1)) true, by simp [copy,List.append_assoc]⟩
  apply prefix_mem_coreNodes inside side
  apply List.prefix_of_prefix_length_le pre early
  simp only [List.length_append, List.length_cons, List.length_nil] at short ⊢
  omega

def RightOutside (height : Nat) (state : State) : Prop :=
  ∀ owner, owner.length < 2*height → owner ∉ coreNodes height → state owner = true

theorem RightOutside.leafStep {height : Nat} {state : State} (right : RightOutside height state)
    {address : Key} (inside : address.length < height) (side : Bool) :
    RightOutside height (leafStep state (copy height address side)) := by
  intro owner internal absent
  have old := right owner internal absent
  have noLeft : branch owner (copy height address side) ≠ some false :=
    fun left => absent (false_branch_core inside side left)
  cases write : branch owner (copy height address side) with
  | none => simp [EndpointEncoding.leafStep,write,old]
  | some bit => cases bit <;> simp_all [EndpointEncoding.leafStep]

theorem ancestorEmissions_changes {state : State} {leaf owner : Key}
    (member : owner ∈ ancestorEmissions state leaf) : changes (state owner) (branch owner leaf) := by
  have increasing := ascendingEmissions_increasing state leaf
  rw [ascendingEmissions, List.pairwise_append] at increasing
  have less := increasing.2.2 owner member leaf (by simp)
  have different : owner ≠ leaf := fun same => by subst owner; omega
  have written := ascendingEmissions_mem.mp (List.mem_append_left [leaf] member)
  simpa only [nodeWrite,if_neg different] using written

theorem ancestorEmissions_core {height : Nat} {state : State} (right : RightOutside height state)
    {address owner : Key} (inside : address.length < height) (side : Bool)
    (member : owner ∈ ancestorEmissions state (copy height address side)) : owner ∈ coreNodes height := by
  by_contra absent
  have sorted := ascendingEmissions_increasing state (copy height address side)
  rw [ascendingEmissions,List.pairwise_append] at sorted
  have shorter := sorted.2.2 owner member (copy height address side) (by simp)
  have length := copy_length inside side
  have old := right owner (by omega) absent
  have changed := ancestorEmissions_changes member
  have noLeft : branch owner (copy height address side) ≠ some false :=
    fun left => absent (false_branch_core inside side left)
  cases write : branch owner (copy height address side) with
  | none => simp [changes,write] at changed
  | some bit => cases bit <;> simp_all [changes]

end MultiSplay.EndpointEncoding
