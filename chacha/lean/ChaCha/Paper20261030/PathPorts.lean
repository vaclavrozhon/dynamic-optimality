import ChaCha.Paper20261030.GapSource

/-!
# A source path's actual hanging ports

Following one selected child at each internal source vertex leaves a
one-child skeleton. The omitted children and the terminal leaf are its
inorder gap ports. Encoding this skeleton with these very subtrees
reconstructs the original source tree exactly, including every record.
-/

namespace ChaCha.Paper20261030.GapSource

open ChaCha.MTR ColoredStorage

variable {α ρ : Type*}

theorem encode_congr (t : MTR.Tree ρ) (ports other : Nat → Source α ρ) (base : Nat)
    (h : ∀ i, base ≤ i → i ≤ base + t.size → ports i = other i) :
    encode t ports base = encode t other base := by
  induction t generalizing base with
  | empty => exact h base le_rfl (by simp [MTR.Tree.size])
  | node l record r ihl ihr =>
    simp only [encode]
    congr 1
    · apply ihl
      intro i hlo hhi
      exact h i hlo (by simp only [MTR.Tree.size]; omega)
    · apply ihr
      intro i hlo hhi
      exact h i (by omega) (by simp only [MTR.Tree.size]; omega)

theorem encode_offset (t : MTR.Tree ρ) (ports : Nat → Source α ρ) (offset base : Nat) :
    encode t ports (offset + base) = encode t (fun i => ports (offset + i)) base := by
  induction t generalizing base with
  | empty => rfl
  | node l record r ihl ihr =>
    simp only [encode,ihl,Nat.add_assoc,ihr]

end ChaCha.Paper20261030.GapSource

namespace ChaCha.Paper20261030.PathPorts

open ChaCha.MTR ColoredStorage

variable {α ρ : Type*}

def skeleton (right : ρ → Bool) : Source α ρ → MTR.Tree ρ
  | .leaf _ _ => .empty
  | .fork record l r =>
      if right record then .node .empty record (skeleton right r)
      else .node (skeleton right l) record .empty

def port (right : ρ → Bool) : Source α ρ → Nat → Source α ρ
  | .leaf key record,_ => .leaf key record
  | .fork record l r,i =>
      if right record then
        if i = 0 then l else port right r (i - 1)
      else if i ≤ (skeleton right l).size then port right l i else r

theorem reconstruct (right : ρ → Bool) (source : Source α ρ) :
    GapSource.encode (skeleton right source) (port right source) 0 = source := by
  induction source with
  | leaf key record => rfl
  | fork record l r ihl ihr =>
    cases hp : right record
    · simp only [skeleton,hp,Bool.false_eq_true,if_false,GapSource.encode]
      have hl : GapSource.encode (skeleton right l) (port right (.fork record l r)) 0 = l := by
        rw [GapSource.encode_congr _ _ (port right l) 0 ?_,ihl]
        intro i hlo hhi
        simp only [Nat.zero_add] at hhi
        simp only [port,hp,Bool.false_eq_true,if_false,if_pos hhi]
      have hr : port right (.fork record l r) (0 + (skeleton right l).size + 1) = r := by
        simp [port,hp]
      rw [hl,hr]
    · simp only [skeleton,hp,if_true,GapSource.encode,MTR.Tree.size,Nat.zero_add]
      have hl : port right (.fork record l r) 0 = l := by simp [port,hp]
      have hr : GapSource.encode (skeleton right r) (port right (.fork record l r)) 1 = r := by
        have hs : (fun i => port right (.fork record l r) (1 + i)) = port right r := by
          funext i
          simp [port,hp,Nat.add_comm]
        rw [show 1 = 1 + 0 by rfl,GapSource.encode_offset,hs,ihr]
      rw [hl,hr]

theorem port_leaf_word (right : ρ → Bool) (source : Source α ρ) :
    (List.range' 0 ((skeleton right source).size + 1)).flatMap
      (fun i => (port right source i).shape.leaves) = source.shape.leaves := by
  rw [← GapSource.encode_leaves,reconstruct]

end ChaCha.Paper20261030.PathPorts
