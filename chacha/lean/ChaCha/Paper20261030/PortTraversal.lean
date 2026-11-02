import ChaCha.Paper20261030.PathPorts
import ChaCha.Paper20261030.ProjectionLocal

/-!
# Visiting and transforming all ports of an auxiliary

A depth-first traversal reaches each hanging port, runs its supplied
root-to-root trace, and returns to the auxiliary root. Every skeleton
vertex is read and its two child excursions are charged. The resulting
cost is the sum of the actual port costs plus five per skeleton vertex;
the sizes of the hanging subtrees do not enter the traversal overhead.
-/

namespace ChaCha.Paper20261030.GapSource

open ColoredStorage SourcePointer ChaCha.MTR

variable {α ρ : Type*}

def portCost (cost : Nat → Nat) (base count : Nat) : Nat :=
  ((List.range' base count).map cost).sum

theorem portCost_add (cost : Nat → Nat) (base left right : Nat) :
    portCost cost base (left + right) = portCost cost base left + portCost cost (base + left) right := by
  simp only [portCost,← List.range'_append_1,List.map_append,List.sum_append]

theorem transform_ports (t : MTR.Tree ρ) (before after : Nat → Source α ρ) (cost : Nat → Nat)
    (h : ∀ i, SourcePointer.Rearranges (before i) (after i) (cost i)) (base : Nat) :
    SourcePointer.Rearranges (encode t before base) (encode t after base)
      (portCost cost base (t.size + 1) + 5 * t.size) := by
  induction t generalizing base with
  | empty => simpa only [encode,MTR.Tree.size,portCost,List.range',List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_zero] using h base
  | node l record r ihl ihr =>
    have read : SourcePointer.Rearranges
        (.fork record (encode l before base) (encode r before (base + l.size + 1)))
        (.fork record (encode l before base) (encode r before (base + l.size + 1))) 1 :=
      fun rest => ⟨[record],1,.read (.nil _),le_rfl⟩
    have all := ((read.trans (ihl base).left).trans (ihr (base + l.size + 1)).right)
    apply all.mono
    have he : l.size + 1 + r.size + 1 = (l.size + 1) + (r.size + 1) := by omega
    simp only [MTR.Tree.size,he,portCost_add,Nat.add_assoc]
    omega

end ChaCha.Paper20261030.GapSource
