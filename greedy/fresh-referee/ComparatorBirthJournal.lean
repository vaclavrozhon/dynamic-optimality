import OrderedComparatorMacro
import CutBirthJournal

/-!
Executed administration birth journals. Only actually born logical
instances enter the list: replacement growers, both children of an actual
straddling split, and installed paid singletons. Reserved names are absent.
The length theorem ties this explicit journal to the derived macro budget.
Global identifier freshness is a separate allocator invariant.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.BirthJournal (cutBirthIds cutBirthIds_length)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

noncomputable def collectIds {α : Type*} (locations : Finset α) (journal : α → List ℕ) : List ℕ :=
  locations.toList.flatMap journal

theorem collectIds_length {α : Type*} (locations : Finset α) (journal : α → List ℕ) :
    (collectIds locations journal).length = ∑ location ∈ locations, (journal location).length := by
  classical
  unfold collectIds
  rw [List.length_flatMap]
  rw [← List.sum_toFinset _ locations.nodup_toList, Finset.toList_toFinset]

/-- Conversion logs only the replacement; the old grower continues as a
frozen instance under its unchanged logical id. -/
def conversionIds (replacementId : ℕ) (state : SideState) : List ℕ :=
  match state.grower with
  | none => []
  | some grower => if grower.members=[] then [] else [replacementId]

@[simp] theorem conversionIds_length (replacementId : ℕ) (state : SideState) :
    (conversionIds replacementId state).length = conversionBirths state := by
  cases same : state.grower with
  | none => simp [conversionIds,conversionBirths,same]
  | some grower =>
      by_cases empty : grower.members=[] <;> simp [conversionIds,conversionBirths,same,empty]

def growerPreparationIds {n : ℕ} (before after : BST 0 n) (owner : External n)
    (replacementId : ℕ) (state : SideState) : List ℕ :=
  if GrowerMismatch before after owner state then conversionIds replacementId state else []

@[simp] theorem growerPreparationIds_length {n : ℕ} (before after : BST 0 n) (owner : External n)
    (replacementId : ℕ) (state : SideState) :
    (growerPreparationIds before after owner replacementId state).length =
      growerPreparationBirths before after owner state := by
  simp only [growerPreparationIds,growerPreparationBirths]
  split_ifs <;> simp

noncomputable def prepareAllGrowersIds {n : ℕ} (before after : BST 0 n)
    (ids : External n → Bool → ℕ) (states : HeapSides n) : List ℕ :=
  collectIds Finset.univ (fun owner =>
    growerPreparationIds before after owner (ids owner false) (states owner false) ++
    growerPreparationIds before after owner (ids owner true) (states owner true))

@[simp] theorem prepareAllGrowersIds_length {n : ℕ} (before after : BST 0 n)
    (ids : External n → Bool → ℕ) (states : HeapSides n) :
    (prepareAllGrowersIds before after ids states).length = allGrowerPreparationBirths before after states := by
  simp [prepareAllGrowersIds,collectIds_length,allGrowerPreparationBirths]

noncomputable def detachAllIds {n : ℕ} (key : ℕ) (ids : External n → Bool → ℕ)
    (states : HeapSides n) : List ℕ :=
  (portSources key states).toList.map (fun place => ids place.1 place.2)

@[simp] theorem detachAllIds_length {n : ℕ} (key : ℕ) (ids : External n → Bool → ℕ)
    (states : HeapSides n) : (detachAllIds key ids states).length = (portSources key states).card := by
  simp [detachAllIds]

noncomputable def detachPortsIds {n : ℕ} (before : BST 0 n) (families ids : NameSupply n) :
    List ℕ → ℕ → HeapSides n → List ℕ
  | [], _, _ => []
  | key::rest, stage, states =>
      detachAllIds key (ids stage) states ++
        detachPortsIds before families ids rest (stage+1) (detachAll before key (families stage) (ids stage) states)

@[simp] theorem detachPortsIds_length {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) :
    (detachPortsIds before families ids ports stage states).length =
      (detachPorts before families ids ports stage states).2 := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons key rest ih => simp only [detachPortsIds,List.length_append,detachAllIds_length,ih,detachPorts]

noncomputable def sealOwnersIds {n : ℕ} (owners : Finset (External n))
    (ids : External n → Bool → ℕ) (states : HeapSides n) : List ℕ :=
  collectIds owners (fun owner => conversionIds (ids owner false) (states owner false) ++
    conversionIds (ids owner true) (states owner true))

@[simp] theorem sealOwnersIds_length {n : ℕ} (owners : Finset (External n))
    (ids : External n → Bool → ℕ) (states : HeapSides n) :
    (sealOwnersIds owners ids states).length = sealOwnersBirths owners states := by
  simp [sealOwnersIds,collectIds_length,sealOwnersBirths]

noncomputable def cutAllOwnersIds {n : ℕ} (cut : ℕ) (allocate : External n → Bool → ℕ)
    (states : HeapSides n) : List ℕ :=
  collectIds Finset.univ (fun owner =>
    cutBirthIds cut (allocate owner false) (states owner false).shrinking ++
    cutBirthIds cut (allocate owner true) (states owner true).shrinking)

@[simp] theorem cutAllOwnersIds_length {n : ℕ} (cut : ℕ) (allocate : External n → Bool → ℕ)
    (states : HeapSides n) : (cutAllOwnersIds cut allocate states).length = allOwnerCutBirths states cut := by
  simp [cutAllOwnersIds,collectIds_length,cutBirthIds_length,allOwnerCutBirths,ownerCutBirths]

noncomputable def prepareCutsIds {n : ℕ} (allocate : NameSupply n) :
    List (ℕ × ℕ) → ℕ → HeapSides n → List ℕ
  | [], _, _ => []
  | entry::rest, stage, states =>
      cutAllOwnersIds entry.1 (allocate stage) states ++
        prepareCutsIds allocate rest (stage+1) (cutAllOwners entry.1 (allocate stage) states)

@[simp] theorem prepareCutsIds_length {n : ℕ} (allocate : NameSupply n)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : HeapSides n) :
    (prepareCutsIds allocate cuts stage states).length = (prepareCuts allocate cuts stage states).2 := by
  induction cuts generalizing stage states with
  | nil => rfl
  | cons entry rest ih => simp only [prepareCutsIds,List.length_append,cutAllOwnersIds_length,ih,prepareCuts]

noncomputable def prepareComparatorIds {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n) : List ℕ :=
  let growing := prepareAllGrowers before after (families 0) (ids 0) states
  let detached := (detachPorts before families ids ports 1 growing).1
  let sealed := sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1)) detached
  prepareAllGrowersIds before after (ids 0) states ++
    detachPortsIds before families ids ports 1 growing ++
    sealOwnersIds bulkOwners (ids (ports.length+1)) detached ++
    prepareCutsIds ids profile.entries (ports.length+2) sealed

@[simp] theorem prepareComparatorIds_length {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n) :
    (prepareComparatorIds profile families ids ports bulkOwners states).length =
      (prepareComparator profile families ids ports bulkOwners states).2 := by
  simp [prepareComparatorIds,prepareComparator,Nat.add_assoc]

noncomputable def junctionTransferIds {n : ℕ} (oldOwner : External n) (lo hi : ℕ)
    (fresh : Bool → ℕ) (states : HeapSides n) : List ℕ :=
  cutBirthIds (junctionCut false lo hi) (fresh false) (states oldOwner false).shrinking ++
    cutBirthIds (junctionCut true lo hi) (fresh true) (states oldOwner true).shrinking

@[simp] theorem junctionTransferIds_length {n : ℕ} (oldOwner : External n) (lo hi : ℕ)
    (fresh : Bool → ℕ) (states : HeapSides n) :
    (junctionTransferIds oldOwner lo hi fresh states).length = junctionTransferBirths oldOwner lo hi states := by
  simp [junctionTransferIds,cutBirthIds_length,junctionTransferBirths]

noncomputable def paidInsertionIds (owner replacementFamily replacementId splitStart paidId base : ℕ)
    (entry : Entry) (state : SideState) : List ℕ :=
  conversionIds replacementId state ++
    cutBirthIds entry.key splitStart (convert owner replacementFamily replacementId base state).shrinking ++ [paidId]

@[simp] theorem paidInsertionIds_length (owner replacementFamily replacementId splitStart paidId base : ℕ)
    (entry : Entry) (state : SideState) :
    (paidInsertionIds owner replacementFamily replacementId splitStart paidId base entry state).length =
      paidInsertionBirths owner replacementFamily replacementId base entry state := by
  simp [paidInsertionIds,cutBirthIds_length,paidInsertionBirths,Nat.add_assoc]

noncomputable def restorePortIds {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n) : List ℕ :=
  match canonicalParent snapshot tree record with
  | none => []
  | some owner => paidInsertionIds owner.val names.replacementFamily names.replacementId
      names.splitStart names.paidId (snapshot.rank owner) (makeEntry owner)
      (states owner (decide (record.val < owner.val)))

@[simp] theorem restorePortIds_length {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n) :
    (restorePortIds snapshot tree names makeEntry record states).length =
      (restorePort snapshot tree names makeEntry record states).2 := by
  cases parent : canonicalParent snapshot tree record <;> simp [restorePortIds,restorePort,parent]

noncomputable def restorePortsIds {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry) :
    List (External n) → ℕ → HeapSides n → List ℕ
  | [], _, _ => []
  | record::rest, stage, states =>
      restorePortIds snapshot tree (names stage) (makeEntry stage record) record states ++
        restorePortsIds snapshot tree names makeEntry rest (stage+1)
          (restorePort snapshot tree (names stage) (makeEntry stage record) record states).1

@[simp] theorem restorePortsIds_length {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (stage : ℕ) (states : HeapSides n) :
    (restorePortsIds snapshot tree names makeEntry ports stage states).length =
      (restorePorts snapshot tree names makeEntry ports stage states).2 := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons record rest ih => simp only [restorePortsIds,List.length_append,restorePortIds_length,ih,restorePorts]

noncomputable def administerJunctionIds {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (node : AtNode n)
    (oldOwner newOwner : External n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (states : HeapSides n) : List ℕ :=
  let prepared := prepareComparator profile families ids (junctionPorts (Snapshot.ofTree before) node)
    {oldOwner,newOwner} states
  let moved := moveJunction oldOwner newOwner node.lower node.upper bulkFresh prepared.1
  prepareComparatorIds profile families ids (junctionPorts (Snapshot.ofTree before) node)
      {oldOwner,newOwner} states ++
    junctionTransferIds oldOwner node.lower node.upper bulkFresh prepared.1 ++
    restorePortsIds (Snapshot.ofTree after) tree paidNames makeEntry
      (junctionRecords (Snapshot.ofTree before) node) 0 (rebaseAll before after moved)

/-- Exact counting of the executed logical births. This list contains no
unused reserved identifier merely because it is below an allocator counter. -/
theorem administerJunctionIds_length {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (node : AtNode n)
    (oldOwner newOwner : External n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (states : HeapSides n) :
    (administerJunctionIds profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).length =
      (administerJunction profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).2 := by
  simp [administerJunctionIds,administerJunction,prepareMoveJunction,Nat.add_assoc]

#print axioms administerJunctionIds_length

end GreedyMerge.OrderedBlocks
