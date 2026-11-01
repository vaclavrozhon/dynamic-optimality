import MappedConsolidation
import OrderedBlockPrimitives
import ActualSourceBlocks

/-!
Construction of the accounting source partition from literal consecutive
Frozen blocks on an actual ordered root-child list. Interval endpoints are
derived from before lengths; they are not supplied as source hypotheses.
-/
namespace GreedyMerge.ActualBlockPartition
open Splay.Tree Splay.Tree.BST Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest.Phase

def blockKeys (block : Frozen) : List ℕ := block.members.map Entry.key
def keys (blocks : List Frozen) : List ℕ := blocks.flatMap blockKeys

theorem keys_eq_entries (blocks : List Frozen) : keys blocks = (frozenEntries blocks).map Entry.key := by
  change blocks.flatMap blockKeys = (blocks.flatMap Frozen.members).map Entry.key
  rw [List.map_flatMap]
  rfl

theorem mem_range_iff {start count value : ℕ} :
    value ∈ List.range' start count ↔ start ≤ value ∧ value < start+count := by
  simp only [List.mem_range', Nat.one_mul]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨lower, upper⟩
    exact ⟨value-start, by omega, by omega⟩

theorem mapped_range_segment (map : ℕ → ℕ) (start count : ℕ)
    (before middle after : List ℕ)
    (cover : (List.range' start count).map map = before ++ middle ++ after) :
    middle = (List.range' (start+before.length) middle.length).map map := by
  have lengthEq := congrArg List.length cover
  simp only [List.length_map, List.length_range', List.length_append] at lengthEq
  have separated : before ++ (middle ++ after) =
      (List.range' start before.length).map map ++
        ((List.range' (start+before.length) middle.length).map map ++
         (List.range' (start+before.length+middle.length) after.length).map map) := by
    calc
      before ++ (middle ++ after) = (List.range' start count).map map := by
        simpa only [List.append_assoc] using cover.symm
      _ = (List.range' start (before.length+(middle.length+after.length))).map map := by
        rw [lengthEq]
        simp only [Nat.add_assoc]
      _ = _ := by
        rw [← List.range'_append_1, List.map_append,
          ← List.range'_append_1, List.map_append]
  have tailEq := List.append_inj_right separated (by simp)
  exact List.append_inj_left tailEq (by simp)

theorem mapped_segment_membership (map : ℕ → ℕ) (start count value : ℕ)
    (before middle after : List ℕ)
    (cover : (List.range' start count).map map = before ++ middle ++ after)
    (injective : ∀ a, start ≤ a → a < start+count → ∀ b,
      start ≤ b → b < start+count → map a = map b → a=b)
    (lower : start ≤ value) (upper : value < start+count) :
    map value ∈ middle ↔ start+before.length ≤ value ∧
      value < start+before.length+middle.length := by
  have lengthEq := congrArg List.length cover
  simp only [List.length_map, List.length_range', List.length_append] at lengthEq
  conv_lhs => rw [mapped_range_segment map start count before middle after cover]
  rw [List.mem_map]
  constructor
  · rintro ⟨index, member, equal⟩
    have bounds := mem_range_iff.mp member
    have indexEq := injective index (by omega) (by omega) value lower upper equal
    omega
  · rintro ⟨first, finish⟩
    exact ⟨value, mem_range_iff.mpr ⟨first,by omega⟩, rfl⟩

theorem shared_flatMap_member {α β : Type*} (map : α → List β) (blocks : List α)
    (distinct : (blocks.flatMap map).Nodup) {first second : α} {value : β}
    (firstMem : first ∈ blocks) (secondMem : second ∈ blocks)
    (inFirst : value ∈ map first) (inSecond : value ∈ map second) : first=second := by
  induction blocks with
  | nil => simp at firstMem
  | cons head tail ih =>
      have nd := List.nodup_append.mp distinct
      rcases List.mem_cons.mp firstMem with firstEq | firstTail
      · subst first
        rcases List.mem_cons.mp secondMem with secondEq | secondTail
        · exact secondEq.symm
        · have inTail := List.mem_flatMap.mpr ⟨second,secondTail,inSecond⟩
          exact False.elim (nd.2.2 value inFirst value inTail rfl)
      · rcases List.mem_cons.mp secondMem with secondEq | secondTail
        · subst second
          have inTail := List.mem_flatMap.mpr ⟨first,firstTail,inFirst⟩
          exact False.elim (nd.2.2 value inSecond value inTail rfl)
        · exact ih nd.2.1 firstTail secondTail

structure Location (blocks : List Frozen) (id : ℕ) where
  before : List Frozen
  focus : Frozen
  after : List Frozen
  split : blocks = before ++ focus :: after
  idEq : focus.id = id

theorem Location.member {blocks : List Frozen} {id : ℕ} (whereAt : Location blocks id) :
    whereAt.focus ∈ blocks := by
  rcases whereAt with ⟨before,focus,after,split,idEq⟩
  subst blocks
  simp

theorem location_exists {blocks : List Frozen} {id : ℕ}
    (member : id ∈ blocks.map Frozen.id) : Nonempty (Location blocks id) := by
  obtain ⟨block, blockMem, idEq⟩ := List.mem_map.mp member
  obtain ⟨before,after,split⟩ := List.mem_iff_append.mp blockMem
  exact ⟨⟨before,block,after,split,idEq⟩⟩

def Location.first {blocks : List Frozen} {id : ℕ} (whereAt : Location blocks id) (start : ℕ) : ℕ :=
  start+(keys whereAt.before).length

def Location.finish {blocks : List Frozen} {id : ℕ} (whereAt : Location blocks id) (start : ℕ) : ℕ :=
  whereAt.first start+(blockKeys whereAt.focus).length

theorem Location.bounds {blocks : List Frozen} {id start count : ℕ}
    (whereAt : Location blocks id) (map : ℕ → ℕ)
    (cover : keys blocks = (List.range' start count).map map) :
    start ≤ whereAt.first start ∧ whereAt.finish start ≤ start+count := by
  have lengthEq := congrArg List.length cover
  rw [whereAt.split] at lengthEq
  simp only [keys,List.flatMap_append,List.flatMap_cons,List.length_append,
    List.length_map,List.length_range'] at lengthEq
  unfold Location.first Location.finish
  change start ≤ start+(keys whereAt.before).length ∧
    start+(keys whereAt.before).length+(blockKeys whereAt.focus).length ≤ start+count
  change (keys whereAt.before).length + ((blockKeys whereAt.focus).length +
    (keys whereAt.after).length) = count at lengthEq
  omega

theorem Location.interval {blocks : List Frozen} {id start count value : ℕ}
    (whereAt : Location blocks id) (map : ℕ → ℕ)
    (cover : keys blocks = (List.range' start count).map map)
    (injective : ∀ a, start ≤ a → a < start+count → ∀ b,
      start ≤ b → b < start+count → map a = map b → a=b)
    (lower : start ≤ value) (upper : value < start+count) :
    map value ∈ blockKeys whereAt.focus ↔
      whereAt.first start ≤ value ∧ value < whereAt.finish start := by
  have cover' : (List.range' start count).map map =
      keys whereAt.before ++ blockKeys whereAt.focus ++ keys whereAt.after := by
    calc
      _ = keys blocks := cover.symm
      _ = keys (whereAt.before ++ whereAt.focus :: whereAt.after) := congrArg keys whereAt.split
      _ = _ := by simp only [keys, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  exact mapped_segment_membership map start count value _ _ _ cover' injective lower upper

/-- The actual frozen-list cover constructs all accounting source intervals.
The additional conclusions identify its IDs and bases with the literal live
instances, including empty blocks. No interval or source-map input is used. -/
theorem source_partition_of_blocks (map rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (lo hi : ℕ) (ordered : lo ≤ hi) (blocks : List Frozen)
    (ids : (blocks.map Frozen.id).Nodup)
    (cover : keys blocks = (List.range' (2*lo) (2*hi+1-2*lo)).map map)
    (injective : ∀ a, 2*lo ≤ a → a ≤ 2*hi → ∀ b,
      2*lo ≤ b → b ≤ 2*hi → map a = map b → a=b)
    (buckets : ∀ b ∈ blocks, ∀ e ∈ b.members,
      initial e.key = baseLabel rank b.base e.key)
    (floors : ∀ b ∈ blocks, ∀ e ∈ b.members, b.base ≤ rank e.key) :
    ∃ s : SourcePartition (rank ∘ map) (initial ∘ map) lo hi,
      (∀ v, 2*lo ≤ v → v ≤ 2*hi → ∀ b ∈ blocks,
        s.block v = b.id ↔ map v ∈ blockKeys b) ∧
      (∀ b ∈ blocks, s.base b.id = b.base) := by
  classical
  let start := 2*lo
  let count := 2*hi+1-2*lo
  have endEq : start+count=2*hi+1 := by dsimp [start,count]; omega
  have inj : ∀ a, start ≤ a → a < start+count → ∀ b,
      start ≤ b → b < start+count → map a=map b → a=b := by
    intro a ha haz b hb hbz heq
    exact injective a ha (by omega) b hb (by omega) heq
  have distinct : (keys blocks).Nodup := by
    rw [cover]
    apply (List.nodup_map_iff_inj_on (List.nodup_range' (s := 2*lo) (n := 2*hi+1-2*lo) (step := 1))).mpr
    intro a ha b hb heq
    have ba := mem_range_iff.mp ha
    have bb := mem_range_iff.mp hb
    exact inj a ba.1 ba.2 b bb.1 bb.2 heq
  have sourceExists : ∀ v, start ≤ v → v < start+count →
      ∃ b ∈ blocks, map v ∈ blockKeys b := by
    intro v hv hz
    apply List.mem_flatMap.mp
    change map v ∈ keys blocks
    rw [cover]
    exact List.mem_map.mpr ⟨v,mem_range_iff.mpr ⟨hv,hz⟩,rfl⟩
  have assign : ∀ v, ∃ id, start ≤ v → v < start+count →
      ∃ b ∈ blocks, map v ∈ blockKeys b ∧ b.id=id := by
    intro v
    by_cases inRange : start ≤ v ∧ v < start+count
    · obtain ⟨b,hb,hv⟩ := sourceExists v inRange.1 inRange.2
      exact ⟨b.id,fun _ _ => ⟨b,hb,hv,rfl⟩⟩
    · exact ⟨0,by intro hv hz; exact False.elim (inRange ⟨hv,hz⟩)⟩
  choose block block_spec using assign
  let loc : (id : ℕ) → id ∈ blocks.map Frozen.id → Location blocks id :=
    fun id member => Classical.choice (location_exists member)
  let first : ℕ → ℕ := fun id =>
    if member : id ∈ blocks.map Frozen.id then (loc id member).first start else start
  let finish : ℕ → ℕ := fun id =>
    if member : id ∈ blocks.map Frozen.id then (loc id member).finish start else start
  let base : ℕ → ℕ := fun id =>
    if member : id ∈ blocks.map Frozen.id then (loc id member).focus.base else 0
  have focus_eq : ∀ b (hb : b ∈ blocks),
      (loc b.id (List.mem_map.mpr ⟨b,hb,rfl⟩)).focus = b := by
    intro b hb
    apply List.inj_on_of_nodup_map ids (loc b.id (List.mem_map.mpr ⟨b,hb,rfl⟩)).member hb
    exact (loc b.id (List.mem_map.mpr ⟨b,hb,rfl⟩)).idEq
  have base_eq : ∀ b ∈ blocks, base b.id = b.base := by
    intro b hb
    have memId : b.id ∈ blocks.map Frozen.id := List.mem_map.mpr ⟨b,hb,rfl⟩
    simp only [base,dif_pos memId]
    exact congrArg Frozen.base (focus_eq b hb)
  have interval : ∀ b ∈ blocks, ∀ v, start ≤ v → v < start+count →
      (map v ∈ blockKeys b ↔ first b.id ≤ v ∧ v < finish b.id) := by
    intro b hb v hv hz
    have memId : b.id ∈ blocks.map Frozen.id := List.mem_map.mpr ⟨b,hb,rfl⟩
    have exactInterval := (loc b.id memId).interval map cover inj hv hz
    rw [focus_eq b hb] at exactInterval
    simpa only [first,finish,dif_pos memId] using exactInterval
  have matching : ∀ v, start ≤ v → v < start+count → ∀ b ∈ blocks,
      block v=b.id ↔ map v ∈ blockKeys b := by
    intro v hv hz b hb
    obtain ⟨chosen,hchosen,hvalue,hid⟩ := block_spec v hv hz
    constructor
    · intro sameId
      have same : chosen=b := List.inj_on_of_nodup_map ids hchosen hb (hid.trans sameId)
      simpa only [same] using hvalue
    · intro hvalue'
      have same := shared_flatMap_member blockKeys blocks distinct hchosen hb hvalue hvalue'
      simpa only [same] using hid.symm
  have bounds : ∀ id, start ≤ first id ∧ finish id ≤ start+count := by
    intro id
    by_cases member : id ∈ blocks.map Frozen.id
    · simpa only [first,finish,dif_pos member] using (loc id member).bounds map cover
    · simp only [first,finish,dif_neg member]
      omega
  have exactInterval : ∀ v, start ≤ v → v < start+count → ∀ id,
      block v=id ↔ first id ≤ v ∧ v < finish id := by
    intro v hv hz id
    by_cases member : id ∈ blocks.map Frozen.id
    · have sameId := (loc id member).idEq
      have hm := (loc id member).member
      have result := (matching v hv hz _ hm).trans (interval _ hm v hv hz)
      simpa only [sameId] using result
    · obtain ⟨chosen,hchosen,hvalue,hid⟩ := block_spec v hv hz
      have ne : block v ≠ id := by
        intro same
        apply member
        exact List.mem_map.mpr ⟨chosen,hchosen,hid.trans same⟩
      simp only [first,finish,dif_neg member]
      omega
  refine ⟨{
    block := block, base := base, first := first, finish := finish
    intervalBounds := ?_, intervalExact := ?_, initialBucket := ?_, baseFloor := ?_
  }, ?_, base_eq⟩
  · intro id
    simpa only [endEq] using bounds id
  · intro v hv hz id
    exact exactInterval v hv (by omega) id
  · intro v hv hz
    obtain ⟨b,hb,hvalue,hid⟩ := block_spec v hv (by omega)
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hvalue
    change initial (map v) = baseLabel (rank ∘ map) (base (block v)) v
    rw [←hid,base_eq b hb]
    simpa only [Function.comp_apply,baseLabel,heq] using buckets b hb e he
  · intro v hv hz
    obtain ⟨b,hb,hvalue,hid⟩ := block_spec v hv (by omega)
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hvalue
    change base (block v) ≤ rank (map v)
    rw [←hid,base_eq b hb]
    simpa only [heq] using floors b hb e he
  · intro v hv hz b hb
    exact matching v hv (by omega) b hb

end GreedyMerge.ActualBlockPartition

#print axioms GreedyMerge.ActualBlockPartition.Location.interval

#print axioms GreedyMerge.ActualBlockPartition.source_partition_of_blocks
