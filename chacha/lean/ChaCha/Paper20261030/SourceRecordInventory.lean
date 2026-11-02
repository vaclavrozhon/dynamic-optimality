import ChaCha.Paper20261030.DecompositionLeaves

/-!
# The complete record inventory of a balanced component

For any observation of key/payload pairs that ignores cached sizes, the
inventory is the sum of the core word and the inventories of all actual
ports. Consequently equivalent cores preserve every such inventory,
regardless of their balanced shape or cached-size values.
-/

namespace ChaCha.Paper20261030.ColoredStorage

variable {α ρ ι : Type*}

def Source.inventory (identify : ρ → ι) (source : Source α ρ) : Multiset ι :=
  source.records.map identify

@[simp] theorem Source.inventory_leaf (identify : ρ → ι) (key : α) (record : ρ) :
    (Source.leaf key record).inventory identify = {identify record} := rfl

@[simp] theorem Source.inventory_fork (identify : ρ → ι) (record : ρ) (l r : Source α ρ) :
    (Source.fork record l r).inventory identify = {identify record} + l.inventory identify + r.inventory identify := by
  simp [inventory,records,Multiset.map_add]

theorem Source.inventory_setRoot (identify : ρ → ι) (source : Source α ρ) (fresh : ρ)
    (same : identify fresh = identify source.rootRecord) :
    (source.setRoot fresh).inventory identify = source.inventory identify := by
  cases source <;> simp_all only [Source.setRoot,Source.rootRecord,inventory_leaf,inventory_fork]

end ChaCha.Paper20261030.ColoredStorage

namespace ChaCha.Paper20261030.GapSource

open ColoredStorage

variable {α ρ ι : Type*}

theorem encode_inventory (identify : ρ → ι) (t : MTR.Tree ρ) (ports : Nat → Source α ρ) (base : Nat) :
    (encode t ports base).inventory identify = (t.inorder.map identify : Multiset ι) +
      ((List.range' base (t.size+1)).map (fun i => (ports i).inventory identify)).sum := by
  induction t generalizing base with
  | empty => simp [encode,MTR.Tree.inorder,MTR.Tree.size,List.range']
  | node l record r ihl ihr =>
    simp only [encode,Source.inventory_fork,ihl,ihr,MTR.Tree.inorder,MTR.Tree.size]
    have split : List.range' base (l.size+1+r.size+1) =
        List.range' base (l.size+1) ++ List.range' (base+l.size+1) (r.size+1) := by
      simpa only [Nat.add_assoc] using
        (List.range'_append_1 (s := base) (m := l.size+1) (n := r.size+1)).symm
    rw [split]
    simp only [List.map_append,List.sum_append,List.map_singleton,← Multiset.coe_add,Multiset.coe_singleton]
    ac_rfl

end ChaCha.Paper20261030.GapSource

namespace ChaCha.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ ι : Type*} {β : κ → Type*}

theorem recordTree_inventory (identify : Sigma β → ι) (core : Impl κ β) :
    (recordTree core).inorder.map (fun record => identify record.2) = core.toListModel.map identify := by
  induction core <;> simp_all [recordTree,MTR.Tree.inorder,Impl.toListModel,List.map_append]

theorem tree_inventory (identify : Sigma β → ι) (c : AuxiliaryComponent α κ β) :
    c.tree.inventory (fun record => identify record.2) = (c.core.toListModel.map identify : Multiset ι) +
      (c.portWord.map (fun port => port.inventory (fun record => identify record.2))).sum := by
  rw [tree,GapSource.encode_inventory,recordTree_inventory,recordTree_size_of_balanced c.core c.balanced]
  simp only [portWord,List.map_map,List.range_eq_range',Function.comp_def]

theorem Equivalent.inventory (identify : Sigma β → ι) {a b : AuxiliaryComponent α κ β}
    (same : Equivalent a b) :
    a.tree.inventory (fun record => identify record.2) = b.tree.inventory (fun record => identify record.2) := by
  rw [tree_inventory,tree_inventory,same.word,same.portWord]

theorem append_inventory [Ord κ] (identify : Sigma β → ι) (c : AuxiliaryComponent α κ β)
    (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β)) :
    (append c key value sibling).tree.inventory (fun record => identify record.2) =
      {identify ⟨key,value⟩} + c.tree.inventory (fun record => identify record.2) +
        sibling.inventory (fun record => identify record.2) := by
  rw [tree_inventory,tree_inventory,append_word,append_portWord]
  simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,
    ← Multiset.coe_add,Multiset.coe_singleton]
  ac_rfl

theorem prepend_inventory [Ord κ] (identify : Sigma β → ι) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) (c : AuxiliaryComponent α κ β) :
    (prepend key value sibling c).tree.inventory (fun record => identify record.2) =
      {identify ⟨key,value⟩} + sibling.inventory (fun record => identify record.2) +
        c.tree.inventory (fun record => identify record.2) := by
  rw [tree_inventory,tree_inventory,prepend_word,prepend_portWord]
  simp only [List.map_cons,List.sum_cons,← Multiset.cons_coe,← Multiset.singleton_add]
  ac_rfl

end ChaCha.Paper20261030.AuxiliaryComponent
