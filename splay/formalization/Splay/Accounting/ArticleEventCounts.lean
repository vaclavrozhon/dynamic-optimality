import Splay.Accounting.ArticlePairingLoserRestoration
import Splay.Interface.BlockCount
import Splay.Lazy.ValueAdjustmentCost

namespace Splay.Accounting

open Splay.Lazy

@[simp] theorem totalInserts_articlePairingPassEvents {n : ℕ} (state : Lazy.State n)
    (source : Interface.BlockId) (matching : List (Interface.Pairing n)) :
    Interface.totalInserts (eraseOperations (articlePairingPassEvents state source matching)) = 0 := by
  simp [articlePairingPassEvents, eraseOperations, List.flatMap_map, ← List.map_eq_flatMap, Function.comp_def, Event.operations,
    Interface.totalInserts, Interface.Operation.insertCount]

@[simp] theorem totalIncreases_articlePairingPassEvents {n : ℕ} (state : Lazy.State n)
    (source : Interface.BlockId) (matching : List (Interface.Pairing n)) :
    Interface.totalIncreases (eraseOperations (articlePairingPassEvents state source matching)) =
      (articleGoodWinners state matching).length := by
  simp [articlePairingPassEvents, eraseOperations, List.flatMap_map, ← List.map_eq_flatMap, Function.comp_def, Event.operations,
    Interface.totalIncreases, Interface.Operation.increaseCount]

@[simp] theorem totalActivity_articlePairingPassEvents {n : ℕ} (state : Lazy.State n)
    (source : Interface.BlockId) (matching : List (Interface.Pairing n)) :
    Interface.totalActivity (eraseOperations (articlePairingPassEvents state source matching)) =
      matching.length := by
  simp [articlePairingPassEvents, eraseOperations, List.flatMap_map, ← List.map_eq_flatMap, Function.comp_def, Event.operations,
    Interface.totalActivity, Interface.Operation.activity]

@[simp] theorem totalBlockGrowth_articlePairingPassEvents {n : ℕ} (state : Lazy.State n)
    (source : Interface.BlockId) (matching : List (Interface.Pairing n)) :
    Interface.totalBlockGrowth (eraseOperations (articlePairingPassEvents state source matching)) = 0 := by
  simp [articlePairingPassEvents, eraseOperations, List.flatMap_map, ← List.map_eq_flatMap, Function.comp_def, Event.operations,
    Interface.totalBlockGrowth, Interface.Operation.blockGrowth]

@[simp] theorem totalActivity_restoreArticlePairingLoserEvents {n : ℕ}
    (view : HeapView n) (state : Lazy.State n) (matching : List (Interface.Pairing n)) :
    Interface.totalActivity (eraseOperations (restoreArticlePairingLoserEvents view state matching)) = 0 := by
  induction matching generalizing state with
  | nil => rfl
  | cons pairing matching ih =>
      simp only [restoreArticlePairingLoserEvents, eraseOperations_append,
        Interface.totalActivity_append, State.totalActivity_adjustValueEvents, ih, Nat.zero_add]

end Splay.Accounting
