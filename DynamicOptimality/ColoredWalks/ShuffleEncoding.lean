import DynamicOptimality.ColoredWalks.ShuffleEncodingInterface

/-!
# Dense encoding of observed colored keys

The tag `key * k + color` orders copies primarily by their original key.
Only tags and colors occurring in the word receive ranks. Both resulting
universes therefore have at most as many elements as there are events,
and the number of active colors is also at most the supplied color count.
-/

namespace DynamicOptimality.ColoredWalks

namespace DenseRanks

variable {α : Type*} [LinearOrder α]

noncomputable def encode (observed : Finset α) (positive : observed.Nonempty)
    (key : α) : Fin observed.card :=
  if member : key ∈ observed then
    (observed.orderIsoOfFin rfl).symm ⟨key, member⟩
  else ⟨0, Finset.card_pos.mpr positive⟩

def decode (observed : Finset α) : Fin observed.card ↪o α :=
  observed.orderEmbOfFin rfl

theorem decode_mem (observed : Finset α) (rank : Fin observed.card) :
    decode observed rank ∈ observed := observed.orderEmbOfFin_mem rfl rank

theorem decode_encode (observed : Finset α) (positive : observed.Nonempty)
    {key : α} (member : key ∈ observed) :
    decode observed (encode observed positive key) = key := by
  simp only [encode, dif_pos member]
  exact congrArg Subtype.val ((observed.orderIsoOfFin rfl).apply_symm_apply ⟨key, member⟩)

theorem encode_decode (observed : Finset α) (positive : observed.Nonempty)
    (rank : Fin observed.card) :
    encode observed positive (decode observed rank) = rank := by
  apply (decode observed).injective
  exact decode_encode observed positive (decode_mem observed rank)

theorem encode_injective_on (observed : Finset α) (positive : observed.Nonempty)
    {first last : α} (firstMem : first ∈ observed) (lastMem : last ∈ observed)
    (same : encode observed positive first = encode observed positive last) : first = last := by
  have values := congrArg (decode observed) same
  simpa only [decode_encode observed positive firstMem,
    decode_encode observed positive lastMem] using values

end DenseRanks

namespace ObservedTags

variable {n k : Nat}

def tag (event : Fin k × Fin n) : Nat := event.2.val * k + event.1.val

theorem key_le_of_tag_le {first last : Fin k × Fin n}
    (ordered : tag first ≤ tag last) : first.2 ≤ last.2 := by
  by_contra contrary
  have step : last.2.val + 1 ≤ first.2.val := by
    have reversed : last.2 < first.2 := not_le.mp contrary
    exact reversed
  have product := Nat.mul_le_mul_right k step
  rw [Nat.add_mul, Nat.one_mul] at product
  have lastBound := last.1.isLt
  change first.2.val * k + first.1.val ≤ last.2.val * k + last.1.val at ordered
  omega

theorem tag_injective : Function.Injective (tag (n := n) (k := k)) := by
  intro first last same
  have keys : first.2 = last.2 := le_antisymm
    (key_le_of_tag_le (Nat.le_of_eq same)) (key_le_of_tag_le (Nat.le_of_eq same.symm))
  have colors : first.1 = last.1 := by
    apply Fin.ext
    dsimp only [tag] at same
    rw [keys] at same
    omega
  exact Prod.ext colors keys

theorem tag_lt_iff_of_same_color {first last : Fin k × Fin n}
    (same : first.1 = last.1) : tag first < tag last ↔ first.2 < last.2 := by
  have positive : 0 < k := Nat.zero_lt_of_lt first.1.isLt
  simp only [tag, same, Nat.add_lt_add_iff_right]
  exact Nat.mul_lt_mul_right positive

def tags (events : List (Fin k × Fin n)) : Finset Nat := events.toFinset.image tag

def colors (events : List (Fin k × Fin n)) : Finset (Fin k) := events.toFinset.image Prod.fst

theorem mem_tags {events : List (Fin k × Fin n)} {value : Nat} :
    value ∈ tags events ↔ ∃ event ∈ events, tag event = value := by
  simp only [tags, Finset.mem_image, List.mem_toFinset]

theorem tag_mem {events : List (Fin k × Fin n)} {event : Fin k × Fin n}
    (member : event ∈ events) : tag event ∈ tags events := mem_tags.mpr ⟨event, member, rfl⟩

theorem color_mem {events : List (Fin k × Fin n)} {event : Fin k × Fin n}
    (member : event ∈ events) : event.1 ∈ colors events := by
  exact Finset.mem_image.mpr ⟨event, List.mem_toFinset.mpr member, rfl⟩

theorem tags_positive (events : List (Fin k × Fin n)) (nonempty : events ≠ []) :
    (tags events).Nonempty := by
  obtain ⟨event, member⟩ := List.exists_mem_of_ne_nil events nonempty
  exact ⟨tag event, tag_mem member⟩

theorem colors_positive (events : List (Fin k × Fin n)) (nonempty : events ≠ []) :
    (colors events).Nonempty := by
  obtain ⟨event, member⟩ := List.exists_mem_of_ne_nil events nonempty
  exact ⟨event.1, color_mem member⟩

noncomputable def eventOfTag (events : List (Fin k × Fin n))
    (value : {value // value ∈ tags events}) : Fin k × Fin n :=
  Classical.choose (mem_tags.mp value.property)

theorem eventOfTag_mem (events : List (Fin k × Fin n))
    (value : {value // value ∈ tags events}) : eventOfTag events value ∈ events :=
  (Classical.choose_spec (mem_tags.mp value.property)).1

theorem tag_eventOfTag (events : List (Fin k × Fin n))
    (value : {value // value ∈ tags events}) : tag (eventOfTag events value) = value.val :=
  (Classical.choose_spec (mem_tags.mp value.property)).2

noncomputable def decode (events : List (Fin k × Fin n)) (rank : Fin (tags events).card) :
    Fin k × Fin n :=
  eventOfTag events ⟨DenseRanks.decode (tags events) rank,
    DenseRanks.decode_mem (tags events) rank⟩

theorem decode_mem (events : List (Fin k × Fin n)) (rank : Fin (tags events).card) :
    decode events rank ∈ events := eventOfTag_mem events _

theorem tag_decode (events : List (Fin k × Fin n)) (rank : Fin (tags events).card) :
    tag (decode events rank) = DenseRanks.decode (tags events) rank := tag_eventOfTag events _

theorem decode_encode (events : List (Fin k × Fin n)) (nonempty : events ≠ [])
    {event : Fin k × Fin n} (member : event ∈ events) :
    decode events (DenseRanks.encode (tags events) (tags_positive events nonempty) (tag event)) = event := by
  apply tag_injective
  rw [tag_decode, DenseRanks.decode_encode _ _ (tag_mem member)]

theorem encode_decode (events : List (Fin k × Fin n)) (nonempty : events ≠ [])
    (rank : Fin (tags events).card) :
    DenseRanks.encode (tags events) (tags_positive events nonempty) (tag (decode events rank)) = rank := by
  rw [tag_decode, DenseRanks.encode_decode]

theorem monotone_key (events : List (Fin k × Fin n)) :
    Monotone (fun rank => (decode events rank).2) := by
  intro first last ordered
  apply key_le_of_tag_le
  rw [tag_decode, tag_decode]
  exact (DenseRanks.decode (tags events)).monotone ordered

theorem same_color (events : List (Fin k × Fin n)) (nonempty : events ≠ [])
    (first last : Fin (tags events).card) :
    DenseRanks.encode (colors events) (colors_positive events nonempty) (decode events first).1 =
      DenseRanks.encode (colors events) (colors_positive events nonempty) (decode events last).1 ↔
        (decode events first).1 = (decode events last).1 := by
  constructor
  · exact DenseRanks.encode_injective_on _ _
      (color_mem (decode_mem events first)) (color_mem (decode_mem events last))
  · exact congrArg _

theorem order_same_color (events : List (Fin k × Fin n))
    (first last : Fin (tags events).card)
    (same : (decode events first).1 = (decode events last).1) :
    first < last ↔ (decode events first).2 < (decode events last).2 := by
  rw [← tag_lt_iff_of_same_color same, tag_decode, tag_decode]
  exact (DenseRanks.decode (tags events)).lt_iff_lt.symm

end ObservedTags

/-- Rank exactly the observed colored keys and the observed colors. The
empty word needs no encoding and is handled separately by the execution. -/
noncomputable def observedEncoding {n k : Nat} (events : List (Fin k × Fin n))
    (nonempty : events ≠ []) : Encoding events where
  size := (ObservedTags.tags events).card
  count := (ObservedTags.colors events).card
  size_pos := Finset.card_pos.mpr (ObservedTags.tags_positive events nonempty)
  count_pos := Finset.card_pos.mpr (ObservedTags.colors_positive events nonempty)
  size_le_length := Finset.card_image_le.trans events.toFinset_card_le
  count_le_length := Finset.card_image_le.trans events.toFinset_card_le
  count_le_colors := by
    have bound := Finset.card_le_univ (ObservedTags.colors events)
    simpa only [Fintype.card_fin] using bound
  encode event := DenseRanks.encode (ObservedTags.tags events)
    (ObservedTags.tags_positive events nonempty) (ObservedTags.tag event)
  decode := ObservedTags.decode events
  color := DenseRanks.encode (ObservedTags.colors events) (ObservedTags.colors_positive events nonempty)
  decode_mem := ObservedTags.decode_mem events
  decode_encode _ member := ObservedTags.decode_encode events nonempty member
  encode_decode := ObservedTags.encode_decode events nonempty
  monotone_key := ObservedTags.monotone_key events
  same_color := ObservedTags.same_color events nonempty
  order_same_color := ObservedTags.order_same_color events

theorem exists_encoding {n k : Nat} (events : List (Fin k × Fin n))
    (nonempty : events ≠ []) : Nonempty (Encoding events) := ⟨observedEncoding events nonempty⟩

end DynamicOptimality.ColoredWalks
