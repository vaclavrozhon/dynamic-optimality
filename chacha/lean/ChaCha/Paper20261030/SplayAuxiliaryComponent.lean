import DynamicOptimality.Basic
import ChaCha.Paper20261030.PathPorts

/-!
# Auxiliary components without a balance restriction

The core is the shared ordinary BST. Its inorder gaps contain the actual
attached source trees. Reference metadata is kept separately, so rotations
and preference changes never change a physical separator's key.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage

structure RawComponent (α κ : Type*) where
  core : RawTree κ
  ports : Nat → Source α κ

namespace RawComponent

variable {α κ : Type*}

def closed (c : RawComponent α κ) : Source α κ := GapSource.encode c.core c.ports 0

def terminal (port : Source α κ) : RawComponent α κ := ⟨.empty,fun _ => port⟩

def prepend (key : κ) (sibling : Source α κ) (c : RawComponent α κ) : RawComponent α κ :=
  ⟨.node .empty key c.core,fun i => if i = 0 then sibling else c.ports (i-1)⟩

def append (c : RawComponent α κ) (key : κ) (sibling : Source α κ) : RawComponent α κ :=
  ⟨.node c.core key .empty,fun i => if i ≤ c.core.size then c.ports i else sibling⟩

@[simp] theorem prepend_size (key : κ) (sibling : Source α κ) (c : RawComponent α κ) :
    (prepend key sibling c).core.size = c.core.size+1 := by
  simp [prepend,MTR.Tree.size,Nat.add_comm]

@[simp] theorem append_size (c : RawComponent α κ) (key : κ) (sibling : Source α κ) :
    (append c key sibling).core.size = c.core.size+1 := by
  simp [append,MTR.Tree.size]

@[simp] theorem prepend_word (key : κ) (sibling : Source α κ) (c : RawComponent α κ) :
    (prepend key sibling c).core.inorder = key :: c.core.inorder := by
  simp [prepend,MTR.Tree.inorder]

@[simp] theorem append_word (c : RawComponent α κ) (key : κ) (sibling : Source α κ) :
    (append c key sibling).core.inorder = c.core.inorder ++ [key] := by
  simp [append,MTR.Tree.inorder]

@[simp] theorem terminal_closed (port : Source α κ) : (terminal port).closed = port := rfl

theorem prepend_closed (key : κ) (sibling : Source α κ) (c : RawComponent α κ) :
    (prepend key sibling c).closed = .fork key sibling c.closed := by
  change Source.fork key ((prepend key sibling c).ports 0)
    (GapSource.encode c.core (prepend key sibling c).ports 1) = _
  have shift : (fun i => (prepend key sibling c).ports (1+i)) = c.ports := by
    funext i
    simp [prepend,Nat.add_comm]
  rw [show 1 = 1+0 by rfl,GapSource.encode_offset,shift]
  rfl

theorem append_closed (c : RawComponent α κ) (key : κ) (sibling : Source α κ) :
    (append c key sibling).closed = .fork key c.closed sibling := by
  change Source.fork key (GapSource.encode c.core (append c key sibling).ports 0)
    ((append c key sibling).ports (0+c.core.size+1)) = _
  simp only [Nat.zero_add]
  have same : GapSource.encode c.core (append c key sibling).ports 0 = c.closed := by
    apply GapSource.encode_congr
    intro i lower upper
    simp only [Nat.zero_add] at upper
    simp only [append,if_pos upper]
  rw [same]
  simp [append]

/-- Equal separator words and identical physical subtrees in every valid gap. -/
structure Equivalent (a b : RawComponent α κ) : Prop where
  word : a.core.inorder = b.core.inorder
  ports : ∀ i, i ≤ a.core.size → a.ports i = b.ports i

theorem Equivalent.size {a b : RawComponent α κ} (same : Equivalent a b) :
    a.core.size = b.core.size := by
  rw [← MTR.Tree.length_inorder,← MTR.Tree.length_inorder,same.word]

theorem Equivalent.refl (a : RawComponent α κ) : Equivalent a a := ⟨rfl,fun _ _ => rfl⟩

theorem Equivalent.symm {a b : RawComponent α κ} (same : Equivalent a b) : Equivalent b a :=
  ⟨same.word.symm,fun i bound => (same.ports i (by rw [same.size]; exact bound)).symm⟩

theorem Equivalent.trans {a b c : RawComponent α κ} (ab : Equivalent a b) (bc : Equivalent b c) :
    Equivalent a c :=
  ⟨ab.word.trans bc.word,fun i bound => (ab.ports i bound).trans
    (bc.ports i (by rw [← ab.size]; exact bound))⟩

theorem Equivalent.append {a b : RawComponent α κ} (same : Equivalent a b)
    (key : κ) (sibling : Source α κ) : Equivalent (append a key sibling) (append b key sibling) := by
  refine ⟨by simp only [append_word,same.word],?_⟩
  intro i bound
  by_cases before : i ≤ a.core.size
  · have other : i ≤ b.core.size := by rw [← same.size]; exact before
    simpa only [RawComponent.append,if_pos before,if_pos other] using same.ports i before
  · have other : ¬ i ≤ b.core.size := by rw [← same.size]; exact before
    simp only [RawComponent.append,if_neg before,if_neg other]

theorem Equivalent.prepend {a b : RawComponent α κ} (same : Equivalent a b)
    (key : κ) (sibling : Source α κ) : Equivalent (prepend key sibling a) (prepend key sibling b) := by
  refine ⟨by simp only [prepend_word,same.word],?_⟩
  intro i bound
  by_cases zero : i = 0
  · simp only [RawComponent.prepend,if_pos zero]
  · have before : i-1 ≤ a.core.size := by rw [prepend_size] at bound; omega
    simpa only [RawComponent.prepend,if_neg zero] using same.ports (i-1) before

def portWord (c : RawComponent α κ) : List (Source α κ) :=
  (List.range (c.core.size+1)).map c.ports

theorem portWord_length (c : RawComponent α κ) : c.portWord.length = c.core.size+1 := by
  simp only [portWord,List.length_map,List.length_range]

theorem Equivalent.portWord {a b : RawComponent α κ} (same : Equivalent a b) :
    a.portWord = b.portWord := by
  unfold RawComponent.portWord
  rw [← same.size]
  apply List.map_inj_left.mpr
  intro i member
  exact same.ports i (by have := List.mem_range.mp member; omega)

theorem equivalent_of_words {a b : RawComponent α κ}
    (word : a.core.inorder = b.core.inorder) (ports : a.portWord = b.portWord) : Equivalent a b := by
  have size : a.core.size = b.core.size := by
    rw [← MTR.Tree.length_inorder,← MTR.Tree.length_inorder,word]
  refine ⟨word,?_⟩
  intro i bound
  have member : i ∈ List.range (a.core.size+1) := List.mem_range.mpr (by omega)
  have same : (List.range (a.core.size+1)).map a.ports =
      (List.range (a.core.size+1)).map b.ports := by
    simpa only [portWord,← size] using ports
  exact List.map_inj_left.mp same i member

theorem append_portWord (c : RawComponent α κ) (key : κ) (sibling : Source α κ) :
    (append c key sibling).portWord = c.portWord ++ [sibling] := by
  unfold portWord
  rw [append_size,List.range_succ,List.map_append,List.map_singleton]
  have last : (append c key sibling).ports (c.core.size+1) = sibling := by simp [append]
  rw [last]
  congr 1
  apply List.map_inj_left.mpr
  intro i member
  have bound : i ≤ c.core.size := by have := List.mem_range.mp member; omega
  simp only [append,if_pos bound]

theorem prepend_portWord (key : κ) (sibling : Source α κ) (c : RawComponent α κ) :
    (prepend key sibling c).portWord = sibling :: c.portWord := by
  unfold portWord
  rw [prepend_size,List.range_succ_eq_map,List.map_cons,List.map_map]
  have first : (prepend key sibling c).ports 0 = sibling := by simp only [prepend,if_true]
  rw [first]
  congr 1

end RawComponent
end ChaCha.Paper20261030.SplayAuxiliary
