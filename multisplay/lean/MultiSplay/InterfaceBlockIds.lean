import MultiSplay.InterfaceEmbedding

/-! # Renaming persistent interface block IDs without changing any charge -/

namespace MultiSplay.InterfaceBlockIds

open Splay.Interface

variable {n : Nat}

def pairing (rename : BlockId → BlockId) (pair : Pairing n) : Pairing n :=
  {pair with destination := rename pair.destination}

def operation (rename : BlockId → BlockId) : Operation n → Operation n
  | .convert id => .convert (rename id)
  | .create creator => .create creator
  | .insert id x => .insert (rename id) x
  | .delete id x => .delete (rename id) x
  | .pass id pairs => .pass (rename id) (pairs.map (pairing rename))
  | .split id count => .split (rename id) count
  | .valueChange x delta => .valueChange x delta

@[simp] theorem activity (rename : BlockId → BlockId) (word : List (Operation n)) :
    totalActivity (word.map (operation rename)) = totalActivity word := by
  induction word with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all [totalActivity, operation, Operation.activity]

@[simp] theorem inserts (rename : BlockId → BlockId) (word : List (Operation n)) :
    totalInserts (word.map (operation rename)) = totalInserts word := by
  induction word with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all [totalInserts, operation, Operation.insertCount]

@[simp] theorem increases (rename : BlockId → BlockId) (word : List (Operation n)) :
    totalIncreases (word.map (operation rename)) = totalIncreases word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp_all [totalIncreases, operation, Operation.increaseCount]

@[simp] theorem decreases (rename : BlockId → BlockId) (word : List (Operation n)) :
    totalDecreases (word.map (operation rename)) = totalDecreases word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp_all [totalDecreases, operation, Operation.decreaseCount]

/-- Placing a passive front before a component only shifts its persistent IDs. -/
theorem modify_prefix {α : Type*} (front values : List α) (index : Nat) (f : α → α) :
    (front ++ values).modify (front.length + index) f = front ++ values.modify index f := by
  induction front with
  | nil => simp
  | cons head tail ih => simpa only [List.length_cons, List.cons_append, Nat.succ_add, List.modify, List.modifyTailIdx, List.modifyTailIdx.go] using congrArg (head :: ·) ih

@[simp] theorem lookup_prefix {α : Type*} (front values : List α) (index : Nat) :
    (front ++ values)[front.length + index]? = values[index]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem removeLosers (rename : BlockId → BlockId) (values : List (Element n)) (pairs : List (Pairing n)) :
    Splay.Interface.removeLosers values (pairs.map (pairing rename)) = Splay.Interface.removeLosers values pairs := by
  induction pairs generalizing values with
  | nil => rfl
  | cons pair tail ih => simpa [Splay.Interface.removeLosers, pairing] using ih (values.erase pair.loser)

theorem destinations_prefix (front blocks : List (Block n)) (pairs : List (Pairing n)) :
    insertAtDestinations (front ++ blocks) (pairs.map (pairing (front.length + ·))) =
      front ++ insertAtDestinations blocks pairs := by
  induction pairs generalizing blocks with
  | nil => rfl
  | cons pair tail ih =>
      simp only [insertAtDestinations, List.map_cons, List.foldl_cons, pairing, modify_prefix]
      exact ih _

theorem pass_prefix (front blocks : List (Block n)) (index : BlockId) (source : Block n) (pairs : List (Pairing n)) :
    passBlocks (front ++ blocks) (front.length + index) source (pairs.map (pairing (front.length + ·))) =
      front ++ passBlocks blocks index source pairs := by
  simp only [passBlocks, removeLosers, modify_prefix, destinations_prefix]

theorem split_prefix (front blocks : List (Block n)) (index : BlockId) (source : Block n) (count : Nat) :
    splitBlocks (front ++ blocks) (front.length + index) source count =
      front ++ splitBlocks blocks index source count := by
  simp only [splitBlocks, modify_prefix, List.append_assoc]

end MultiSplay.InterfaceBlockIds
