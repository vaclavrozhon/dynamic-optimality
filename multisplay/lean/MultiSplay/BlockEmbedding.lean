import MultiSplay.JoinHeap

/-!
# Retaining lazy interval data through a common join

The mapped block keeps its mode, pass counter, interval gap, and element order.
Its owner and immutable creator are translated by the same component embedding.
For every old valid block, common joining preserves its interval minimum, point
gaps, and contracted values. This includes empty retired shrinking records.
-/

namespace MultiSplay.BlockEmbedding

open Splay.Lazy (Block HeapView Element)
open Splay.Rank (External Snapshot)
open Splay.Tree (BST)
open Splay.Lazy.Canonical
open RankEmbedding (external)

variable {n m : Nat}

def block (embedding : Element n → Element m) (source : Block n) : Block m where
  creator := embedding source.creator
  owner := embedding source.owner
  side := source.side
  passCount := source.passCount
  mode := source.mode
  elements := source.elements.map embedding
  intervalGap := source.intervalGap

/-- Mapping a retained block preserves the actual attained interval minimum,
including the empty shrinking-block convention. -/
theorem gapValid (embedding : Element n → Element m) (before : HeapView n) (after : HeapView m)
    (source : Block n) (valid : source.GapValid before)
    (gaps : ∀ element ∈ source.elements, after.rawGap (embedding element) = before.rawGap element) :
    (block embedding source).GapValid after := by
  cases modeEq : source.mode with
  | growing =>
      simp only [block, Block.GapValid, modeEq]
      have old : source.intervalGap = 0 ∧ ∀ element ∈ source.elements, 0 ≤ before.rawGap element := by
        simpa [Block.GapValid, modeEq] using valid
      refine ⟨old.1, ?_⟩
      intro element member
      obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp member
      rw [gaps original originalMem]
      exact old.2 original originalMem
  | shrinking =>
      have old := valid
      simp only [Block.GapValid, modeEq] at old
      rcases old with empty | nonempty
      · simp [block, Block.GapValid, modeEq, empty.1, empty.2]
      · have minimum := nonempty.2
        simp only [Splay.Analysis.IsIntervalGap] at minimum
        obtain ⟨witness, member, attained⟩ := minimum.1
        have witnessMem : witness ∈ source.elements := by simpa using member
        have mappedMem : embedding witness ∈ (source.elements.map embedding).toFinset := by
          simpa using List.mem_map.mpr ⟨witness, witnessMem, rfl⟩
        simp only [block, Block.GapValid, modeEq]
        refine Or.inr ⟨by simpa using nonempty.1, ⟨embedding witness, mappedMem, ?_⟩, ?_⟩
        · exact (gaps witness witnessMem).trans attained
        · intro element member
          obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
          rw [gaps original originalMem]
          exact minimum.2 original (by simpa using originalMem)

/-- A structurally attached element cannot be the old heap root. -/
theorem member_ne_root (view : HeapView n) (source : Block n) (assigned : List (Element n))
    (valid : source.StructurallyValid view assigned) {element : Element n}
    (member : element ∈ source.elements) : element ≠ view.root := by
  intro same
  have parent := valid.parent_eq member
  rw [same, view.root_parent] at parent
  cases parent

theorem pointGap (embedding : Element n → Element m) (before : HeapView n) (after : HeapView m)
    (source : Block n) {element : Element n}
    (same : after.rawGap (embedding element) = before.rawGap element) :
    Splay.Analysis.transientPointGap (after.rawGap (embedding element)) (block embedding source).intervalGap =
      Splay.Analysis.transientPointGap (before.rawGap element) source.intervalGap := by rw [same]; rfl

theorem contractedGap (embedding : Element n → Element m) (before : HeapView n) (after : HeapView m)
    (source : Block n) {element : Element n}
    (same : after.rawGap (embedding element) = before.rawGap element) :
    Splay.Analysis.transientContractedGap (after.rawGap (embedding element)) (block embedding source).intervalGap =
      Splay.Analysis.transientContractedGap (before.rawGap element) source.intervalGap := by rw [same]; rfl

theorem left_gapValid {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    (source : Block leftSize) (assigned : List (Element leftSize))
    (valid : source.StructurallyValid (canonicalHeapView (Snapshot.ofTree left) splayLeft) assigned) :
    (block (external 0 (by omega)) source).GapValid
      (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)) := by
  apply gapValid _ _ _ source valid.2.2
  intro element member
  exact JoinHeap.left_rawGap left right splayLeft splayRight (member_ne_root _ source assigned valid member)

theorem right_gapValid {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    (source : Block rightSize) (assigned : List (Element rightSize))
    (valid : source.StructurallyValid (canonicalHeapView (Snapshot.ofTree right) splayRight) assigned) :
    (block (external (0 + leftSize + 1) (by omega)) source).GapValid
      (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)) := by
  apply gapValid _ _ _ source valid.2.2
  intro element member
  exact JoinHeap.right_rawGap left right splayLeft splayRight (member_ne_root _ source assigned valid member)

end MultiSplay.BlockEmbedding
