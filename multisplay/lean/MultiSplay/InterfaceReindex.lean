import MultiSplay.ListReindex

/-!
# Legal interface histories under a fixed permutation of existing block IDs

The permutation fixes unused IDs, so newly created and split records are
appended at their actual fresh positions. No record is physically reordered
by the constructed target execution.
-/

namespace MultiSplay.InterfaceReindex

open Splay.Interface
open InterfaceBlockIds (pairing operation)

variable {n : Nat}

structure Related (rename : Equiv.Perm Nat) (a b : State n) : Prop where
  blocks : ListReindex.Related rename a.blocks b.blocks
  values : a.value = b.value

theorem Related.allElements {rename : Equiv.Perm Nat} {a b : State n} (related : Related rename a b) :
    a.allElements.Perm b.allElements := related.blocks.perm.flatMap fun _ _ => List.Perm.refl _

theorem Related.growingCount {rename : Equiv.Perm Nat} {a b : State n} (related : Related rename a b) (creator : Element n) :
    a.growingCount creator = b.growingCount creator := (related.blocks.perm.filter _).length_eq

theorem Related.valid {rename : Equiv.Perm Nat} {a b : State n} (related : Related rename a b)
    {params : Parameters} (valid : a.Valid params) : b.Valid params := by
  refine ⟨related.allElements.nodup_iff.mp valid.1, ?_, ?_⟩
  · simpa only [related.values] using valid.2.1
  · intro creator
    rw [← related.growingCount]
    exact valid.2.2 creator

theorem pairing_valid {rename : Equiv.Perm Nat} {a b : State n} (related : Related rename a b)
    (id : BlockId) (source : Block n) (pair : Pairing n) (legal : PairingValid a id source pair) :
    PairingValid b (rename id) source (pairing rename pair) := by
  obtain ⟨adjacent, order, different, destination, lookup, growing, creator⟩ := legal
  refine ⟨adjacent, ?_, ?_, destination, ?_, growing, creator⟩
  · simpa only [pairing, related.values] using order
  · exact fun eq => different (rename.injective eq)
  · exact (related.blocks.lookup pair.destination).trans lookup

theorem matching_valid {rename : Equiv.Perm Nat} {a b : State n} (related : Related rename a b)
    (params : Parameters) (id : BlockId) (source : Block n) (pairs : List (Pairing n))
    (legal : MatchingValid params a id source pairs) :
    MatchingValid params b (rename id) source (pairs.map (pairing rename)) := by
  refine ⟨legal.1, ?_, ?_, ?_, ?_⟩
  · simpa [List.flatMap_map, pairing] using legal.2.1
  · simpa [List.map_map, Function.comp_def, pairing] using legal.2.2.1.map rename.injective
  · intro pair member
    obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
    exact pairing_valid related id source old (legal.2.2.2.1 old oldMem)
  · simpa using legal.2.2.2.2

theorem destinations_related {rename : Equiv.Perm Nat} {a b : List (Block n)} (related : ListReindex.Related rename a b)
    (pairs : List (Pairing n)) :
    ListReindex.Related rename (insertAtDestinations a pairs) (insertAtDestinations b (pairs.map (pairing rename))) := by
  induction pairs generalizing a b with
  | nil => exact related
  | cons pair tail ih =>
      simp only [insertAtDestinations, List.map_cons, List.foldl_cons, pairing]
      exact ih (related.modify pair.destination (fun block => {block with elements := pair.loser :: block.elements}))

theorem pass_related {rename : Equiv.Perm Nat} {a b : List (Block n)} (related : ListReindex.Related rename a b)
    (id : BlockId) (source : Block n) (pairs : List (Pairing n)) :
    ListReindex.Related rename (passBlocks a id source pairs) (passBlocks b (rename id) source (pairs.map (pairing rename))) := by
  simp only [passBlocks, InterfaceBlockIds.removeLosers]
  exact destinations_related (related.modify id _) pairs

theorem split_related {rename : Equiv.Perm Nat} {a b : List (Block n)} (related : ListReindex.Related rename a b)
    (id : BlockId) (source : Block n) (count : Nat) :
    ListReindex.Related rename (splitBlocks a id source count) (splitBlocks b (rename id) source count) :=
  (related.modify id (fun block => {block with elements := []})).append _

theorem effect {rename : Equiv.Perm Nat} {a a' b : State n} (related : Related rename a b)
    {params : Parameters} {op : Operation n} (execution : Effect params a op a') :
    ∃ b', Effect params b (operation rename op) b' ∧ Related rename a' b' := by
  cases execution with
  | convert lookup growing blocksEq valuesEq =>
      rename_i id block
      refine ⟨⟨b.blocks.modify (rename id) (fun block => {block with mode := .shrinking}), b.value⟩,
        .convert ((related.blocks.lookup id).trans lookup) growing rfl rfl, ?_, valuesEq.trans related.values⟩
      rw [blocksEq]
      exact related.blocks.modify id _
  | create room blocksEq valuesEq =>
      rename_i creator
      refine ⟨⟨b.blocks ++ [⟨creator, 0, .growing, []⟩], b.value⟩,
        .create (by simpa only [← related.growingCount] using room) rfl rfl, ?_, valuesEq.trans related.values⟩
      rw [blocksEq]
      exact related.blocks.append _
  | insert lookup growing unassigned ordered blocksEq valuesEq =>
      rename_i id block x
      refine ⟨⟨b.blocks.modify (rename id) (fun block => {block with elements := x :: block.elements}), b.value⟩,
        .insert ((related.blocks.lookup id).trans lookup) growing ?_ ?_ rfl rfl, ?_, valuesEq.trans related.values⟩
      · exact fun member => unassigned (related.allElements.mem_iff.mpr member)
      · simpa only [related.values] using ordered
      · rw [blocksEq]
        exact related.blocks.modify id _
  | delete lookup shrinking present blocksEq valuesEq =>
      rename_i id block x
      refine ⟨⟨b.blocks.modify (rename id) (fun block => {block with elements := block.elements.erase x}), b.value⟩,
        .delete ((related.blocks.lookup id).trans lookup) shrinking present rfl rfl, ?_, valuesEq.trans related.values⟩
      rw [blocksEq]
      exact related.blocks.modify id _
  | pass lookup matching blocksEq valuesEq =>
      rename_i id block pairs
      refine ⟨⟨passBlocks b.blocks (rename id) block (pairs.map (pairing rename)), b.value⟩,
        .pass ((related.blocks.lookup id).trans lookup) (matching_valid related _ id block pairs matching) rfl rfl,
        ?_, valuesEq.trans related.values⟩
      rw [blocksEq]
      exact pass_related related.blocks id block pairs
  | split lookup shrinking prefixLe blocksEq valuesEq =>
      rename_i id block count
      refine ⟨⟨splitBlocks b.blocks (rename id) block count, b.value⟩,
        .split ((related.blocks.lookup id).trans lookup) shrinking prefixLe rfl rfl, ?_, valuesEq.trans related.values⟩
      rw [blocksEq]
      exact split_related related.blocks id block count
  | decrease allowed blocksEq valuesEq =>
      rename_i x
      refine ⟨⟨b.blocks, Function.update b.value x (b.value x - 1)⟩,
        .decrease (related.values ▸ allowed) rfl rfl, blocksEq ▸ related.blocks, ?_⟩
      simp only [valuesEq, related.values]
  | increase allowed blocksEq valuesEq =>
      rename_i x
      refine ⟨⟨b.blocks, Function.update b.value x (b.value x + 1)⟩,
        .increase (related.values ▸ allowed) rfl rfl, blocksEq ▸ related.blocks, ?_⟩
      simp only [valuesEq, related.values]

theorem step {rename : Equiv.Perm Nat} {a a' b : State n} (related : Related rename a b)
    {params : Parameters} {op : Operation n} (execution : Step params a op a') :
    ∃ b', Step params b (operation rename op) b' ∧ Related rename a' b' := by
  obtain ⟨b', effect, after⟩ := effect related execution.2.1
  exact ⟨b', ⟨related.valid execution.1, effect, after.valid execution.2.2⟩, after⟩

theorem trace {rename : Equiv.Perm Nat} {a a' b : State n} (related : Related rename a b)
    {params : Parameters} {word : List (Operation n)} (execution : Trace params a word a') :
    ∃ b', Trace params b (word.map (operation rename)) b' ∧ Related rename a' b' := by
  induction execution generalizing b with
  | nil valid => exact ⟨b, .nil (related.valid valid), related⟩
  | cons head tail ih =>
      obtain ⟨middle, first, middleRelated⟩ := step related head
      obtain ⟨final, rest, finalRelated⟩ := ih middleRelated
      exact ⟨final, .cons first rest, finalRelated⟩

end MultiSplay.InterfaceReindex
