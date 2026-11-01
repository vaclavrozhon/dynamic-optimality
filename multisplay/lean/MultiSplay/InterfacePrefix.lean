import MultiSplay.InterfaceBlockIds

/-!
# Executing one component beside an unchanged passive history

The passive records may contain arbitrary prior work. Their assigned elements
and growing creators are outside the active component. Every active operation
is lifted with a fixed block-ID offset, retaining all passive records and
values. Appended records continue the same global history.
-/

namespace MultiSplay.InterfacePrefix

open Splay.Interface

variable {n m : Nat}

structure Passive (embedding : Element n → Element m) (frame : State m) : Prop where
  elements : ∀ x ∈ frame.allElements, ∀ old, x ≠ embedding old
  creators : ∀ block ∈ frame.blocks, block.mode = .growing → ∀ old, block.creator ≠ embedding old

noncomputable def state (embedding : Element n → Element m) (frame : State m) (source : State n) : State m :=
  ⟨frame.blocks ++ source.blocks.map (InterfaceEmbedding.block embedding), Function.extend embedding source.value frame.value⟩

def operation (embedding : Element n → Element m) (frame : State m) (op : Operation n) : Operation m :=
  InterfaceBlockIds.operation (frame.blocks.length + ·) (InterfaceEmbedding.operation embedding op)

@[simp] theorem value_image (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (source : State n) (x : Element n) :
    (state embedding frame source).value (embedding x) = source.value x := injective.extend_apply _ _ _

theorem value_outside (embedding : Element n → Element m) (frame : State m) (source : State n) (x : Element m)
    (outside : x ∉ Set.range embedding) : (state embedding frame source).value x = frame.value x :=
  Function.extend_apply' _ _ _ outside

@[simp] theorem allElements (embedding : Element n → Element m) (frame : State m) (source : State n) :
    (state embedding frame source).allElements = frame.allElements ++ source.allElements.map embedding := by
  simp [state, State.allElements, List.flatMap_append, List.flatMap_map, List.map_flatMap, InterfaceEmbedding.block]

@[simp] theorem found (embedding : Element n → Element m) (frame : State m) (source : State n) (id : BlockId) :
    (state embedding frame source).block? (frame.blocks.length + id) = (source.block? id).map (InterfaceEmbedding.block embedding) := by
  simp [state, State.block?]

theorem frame_growing_zero (embedding : Element n → Element m) (frame : State m) (passive : Passive embedding frame) (creator : Element n) :
    frame.growingCount (embedding creator) = 0 := by
  unfold State.growingCount
  rw [List.filter_eq_nil_iff.mpr ?_]
  · rfl
  intro block member
  simp only [decide_eq_true_eq]
  exact fun fields => passive.creators block member fields.1 creator fields.2

theorem growingCount (embedding : Element n → Element m) (frame : State m) (source : State n) (creator : Element m) :
    (state embedding frame source).growingCount creator =
      frame.growingCount creator + (InterfaceEmbedding.state embedding source).growingCount creator := by
  simp [state, State.growingCount, InterfaceEmbedding.state, List.filter_append]

@[simp] theorem growing_image (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (passive : Passive embedding frame) (source : State n) (creator : Element n) :
    (state embedding frame source).growingCount (embedding creator) = source.growingCount creator := by
  rw [growingCount, frame_growing_zero embedding frame passive, InterfaceEmbedding.growing_image embedding injective, Nat.zero_add]

theorem valid (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (passive : Passive embedding frame) {params : Parameters} (frameValid : frame.Valid params)
    {source : State n} (sourceValid : source.Valid params) : (state embedding frame source).Valid params := by
  refine ⟨?_, ?_, ?_⟩
  · rw [allElements]
    refine List.nodup_append.mpr ⟨frameValid.1, sourceValid.1.map injective, ?_⟩
    intro x frameMem y localMem same
    obtain ⟨old, _, eq⟩ := List.mem_map.mp localMem
    exact passive.elements x frameMem old (same.trans eq.symm)
  · intro x
    by_cases inside : x ∈ Set.range embedding
    · obtain ⟨old, rfl⟩ := inside
      simpa only [value_image embedding injective] using sourceValid.2.1 old
    · rw [value_outside embedding frame source x inside]
      exact frameValid.2.1 x
  · intro creator
    by_cases inside : creator ∈ Set.range embedding
    · obtain ⟨old, rfl⟩ := inside
      rw [growing_image embedding injective frame passive]
      exact sourceValid.2.2 old
    · rw [growingCount, InterfaceEmbedding.growing_outside embedding source creator inside, Nat.add_zero]
      exact frameValid.2.2 creator

theorem map_modify {α β : Type*} (f : α → β) (update : α → α) (mappedUpdate : β → β)
    (commutes : ∀ x, f (update x) = mappedUpdate (f x)) (values : List α) (id : Nat) :
    (values.modify id update).map f = (values.map f).modify id mappedUpdate := by
  induction values generalizing id with
  | nil => cases id <;> rfl
  | cons head tail ih => cases id <;> simp [commutes, ih]

theorem update_value (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (values : Element n → Nat) (fallback : Element m → Nat) (x : Element n) (value : Nat) :
    Function.extend embedding (Function.update values x value) fallback =
      Function.update (Function.extend embedding values fallback) (embedding x) value := by
  classical
  funext y
  by_cases inside : y ∈ Set.range embedding
  · obtain ⟨old, rfl⟩ := inside
    simp [injective.extend_apply, Function.update_apply, injective.eq_iff]
  · have different : y ≠ embedding x := fun eq => inside ⟨x, eq.symm⟩
    simp [Function.extend_apply' _ _ _ inside, different]

theorem pairing_valid (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (source : State n) (id : BlockId) (block : Block n) (pair : Pairing n)
    (legal : PairingValid source id block pair) :
    PairingValid (state embedding frame source) (frame.blocks.length + id) (InterfaceEmbedding.block embedding block)
      (InterfaceBlockIds.pairing (frame.blocks.length + ·) (InterfaceEmbedding.pairing embedding pair)) := by
  obtain ⟨adjacent, order, different, destination, lookup, growing, creator⟩ := legal
  refine ⟨InterfaceEmbedding.adjacent_map embedding adjacent, ?_, ?_, InterfaceEmbedding.block embedding destination, ?_, growing, ?_⟩
  · simpa only [InterfaceBlockIds.pairing, InterfaceEmbedding.pairing, value_image embedding injective] using order
  · exact fun eq => different (Nat.add_left_cancel eq)
  · simp only [InterfaceBlockIds.pairing, InterfaceEmbedding.pairing, found, lookup, Option.map_some]
  · change embedding destination.creator = embedding pair.winner
    rw [creator]

theorem matching_valid (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (params : Parameters) (source : State n) (id : BlockId) (block : Block n) (pairs : List (Pairing n))
    (legal : MatchingValid params source id block pairs) :
    MatchingValid params (state embedding frame source) (frame.blocks.length + id) (InterfaceEmbedding.block embedding block)
      ((pairs.map (InterfaceEmbedding.pairing embedding)).map (InterfaceBlockIds.pairing (frame.blocks.length + ·))) := by
  refine ⟨legal.1, ?_, ?_, ?_, ?_⟩
  · simpa [List.flatMap_map, List.map_flatMap, InterfaceBlockIds.pairing, InterfaceEmbedding.pairing] using legal.2.1.map injective
  · simpa [List.map_map, Function.comp_def, InterfaceBlockIds.pairing, InterfaceEmbedding.pairing] using
      legal.2.2.1.map (fun _ _ eq => Nat.add_left_cancel eq)
  · intro pair member
    obtain ⟨mapped, mappedMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp mappedMem
    exact pairing_valid embedding injective frame source id block old (legal.2.2.2.1 old oldMem)
  · simpa [InterfaceEmbedding.block] using legal.2.2.2.2

end MultiSplay.InterfacePrefix
