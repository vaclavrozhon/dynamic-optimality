import Splay.Interface.Model

namespace Splay.Interface

/--
All elements whose clock is at or above `cutoff` precede all elements whose
clock is below `cutoff`.

The implication form is convenient for histories: a later element above the
cut forces every earlier element to be above it as well.
-/
def ClockCutOrderedAt {α : Type*} (clock : α → ℕ) (cutoff : ℕ)
    (xs : List α) : Prop :=
  xs.Pairwise fun earlier later =>
    cutoff ≤ clock later → cutoff ≤ clock earlier

/-- Two endpoint clocks lie on opposite sides of `cutoff`. -/
def ClockStraddlesAt {α : Type*} (clock : α → ℕ) (cutoff : ℕ)
    (first second : α) : Prop :=
  (cutoff ≤ clock first ∧ clock second < cutoff) ∨
    (cutoff ≤ clock second ∧ clock first < cutoff)

instance decidableClockStraddlesAt {α : Type*}
    (clock : α → ℕ) (cutoff : ℕ) (first second : α) :
    Decidable (ClockStraddlesAt clock cutoff first second) := by
  unfold ClockStraddlesAt
  infer_instance

/-- Consecutive directed edges of a list, in list order. -/
private def adjacentEdges {α : Type*} : List α → List (α × α)
  | first :: second :: rest =>
      (first, second) :: adjacentEdges (second :: rest)
  | _ => []

private theorem mem_adjacentEdges_iff {α : Type*} {xs : List α}
    {first second : α} :
    (first, second) ∈ adjacentEdges xs ↔
      ∃ front back, xs = front ++ first :: second :: back := by
  induction xs generalizing first second with
  | nil =>
      simp [adjacentEdges]
  | cons head tail ih =>
      cases tail with
      | nil =>
          constructor
          · simp [adjacentEdges]
          · rintro ⟨front, back, listEq⟩
            have lengthEq := congrArg List.length listEq
            simp at lengthEq
            omega
      | cons next rest =>
          simp only [adjacentEdges, List.mem_cons]
          constructor
          · intro member
            rcases member with edgeEq | tailMember
            · cases edgeEq
              exact ⟨[], rest, by simp⟩
            · obtain ⟨front, back, tailEq⟩ :=
                ih.mp tailMember
              exact ⟨head :: front, back, by simp [tailEq]⟩
          · rintro ⟨front, back, listEq⟩
            cases front with
            | nil =>
                simp at listEq
                cases listEq.1
                cases listEq.2.1
                exact Or.inl rfl
            | cons frontHead frontTail =>
                have headEq : frontHead = head := by
                  simpa using (congrArg List.head? listEq).symm
                subst frontHead
                have tailEq :
                    next :: rest =
                      frontTail ++ first :: second :: back := by
                  simpa using congrArg List.tail listEq
                exact Or.inr <|
                  ih.mpr ⟨frontTail, back, tailEq⟩

private theorem adjacent_iff_mem_adjacentEdges_or_swap
    {α : Type*} {xs : List α} {first second : α} :
    Adjacent xs first second ↔
      (first, second) ∈ adjacentEdges xs ∨
        (second, first) ∈ adjacentEdges xs := by
  constructor
  · rintro ⟨front, back, ordered | reversed⟩
    · exact Or.inl <| mem_adjacentEdges_iff.mpr ⟨front, back, ordered⟩
    · exact Or.inr <| mem_adjacentEdges_iff.mpr ⟨front, back, reversed⟩
  · rintro (ordered | reversed)
    · obtain ⟨front, back, listEq⟩ :=
        mem_adjacentEdges_iff.mp ordered
      exact ⟨front, back, Or.inl listEq⟩
    · obtain ⟨front, back, listEq⟩ :=
        mem_adjacentEdges_iff.mp reversed
      exact ⟨front, back, Or.inr listEq⟩

private theorem adjacentEdges_straddler_unique
    {α : Type*} (clock : α → ℕ) (cutoff : ℕ) :
    ∀ {xs : List α}, ClockCutOrderedAt clock cutoff xs →
      ∀ {firstLow firstHigh secondLow secondHigh : α},
        (firstHigh, firstLow) ∈ adjacentEdges xs →
        ClockStraddlesAt clock cutoff firstHigh firstLow →
        (secondHigh, secondLow) ∈ adjacentEdges xs →
        ClockStraddlesAt clock cutoff secondHigh secondLow →
        firstHigh = secondHigh ∧ firstLow = secondLow := by
  intro xs ordered
  induction xs with
  | nil =>
      simp [adjacentEdges]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp [adjacentEdges]
      | cons next rest =>
          rw [ClockCutOrderedAt] at ordered
          have orderedParts := List.pairwise_cons.mp ordered
          have tailOrdered :
              ClockCutOrderedAt clock cutoff (next :: rest) :=
            orderedParts.2
          intro firstLow firstHigh secondLow secondHigh
          simp only [adjacentEdges, List.mem_cons]
          intro firstMem firstStraddles secondMem secondStraddles
          by_cases headHigh : cutoff ≤ clock head
          · by_cases nextHigh : cutoff ≤ clock next
            · have headNotStraddles :
                  ¬ ClockStraddlesAt clock cutoff head next := by
                simp [ClockStraddlesAt, headHigh, nextHigh]
              rcases firstMem with firstHead | firstTail
              · cases firstHead
                exact False.elim (headNotStraddles firstStraddles)
              · rcases secondMem with secondHead | secondTail
                · cases secondHead
                  exact False.elim (headNotStraddles secondStraddles)
                · exact
                    ih tailOrdered firstTail firstStraddles
                      secondTail secondStraddles
            · have nextLow : clock next < cutoff :=
                Nat.lt_of_not_ge nextHigh
              have allLaterLow :
                  ∀ later ∈ rest, clock later < cutoff := by
                intro later laterMem
                apply Nat.lt_of_not_ge
                intro laterHigh
                have relation :
                    cutoff ≤ clock later → cutoff ≤ clock next :=
                  (List.pairwise_cons.mp tailOrdered).1 later laterMem
                exact nextHigh (relation laterHigh)
              have noTailStraddler :
                  ∀ {high low : α},
                    (high, low) ∈ adjacentEdges (next :: rest) →
                    ¬ ClockStraddlesAt clock cutoff high low := by
                intro high low edgeMem straddles
                have highMem : high ∈ next :: rest := by
                  obtain ⟨front, back, listEq⟩ :=
                    mem_adjacentEdges_iff.mp edgeMem
                  rw [listEq]
                  simp
                have lowMem : low ∈ next :: rest := by
                  obtain ⟨front, back, listEq⟩ :=
                    mem_adjacentEdges_iff.mp edgeMem
                  rw [listEq]
                  simp
                have highLow : clock high < cutoff := by
                  rcases List.mem_cons.mp highMem with highEq | highRest
                  · simpa [highEq] using nextLow
                  · exact allLaterLow high highRest
                have lowLow : clock low < cutoff := by
                  rcases List.mem_cons.mp lowMem with lowEq | lowRest
                  · simpa [lowEq] using nextLow
                  · exact allLaterLow low lowRest
                rcases straddles with highSide | lowSide
                · exact
                    (Nat.not_le_of_lt highLow) highSide.1
                · exact
                    (Nat.not_le_of_lt lowLow) lowSide.1
              rcases firstMem with firstHead | firstTail
              · rcases secondMem with secondHead | secondTail
                · cases firstHead
                  cases secondHead
                  exact ⟨rfl, rfl⟩
                · exact False.elim <|
                    noTailStraddler secondTail secondStraddles
              · exact False.elim <|
                  noTailStraddler firstTail firstStraddles
          · have headLow : clock head < cutoff :=
              Nat.lt_of_not_ge headHigh
            have allTailLow :
                ∀ later ∈ next :: rest, clock later < cutoff := by
              intro later laterMem
              apply Nat.lt_of_not_ge
              intro laterHigh
              exact headHigh (orderedParts.1 later laterMem laterHigh)
            have noStraddler :
                ∀ {high low : α},
                  (high, low) ∈
                      adjacentEdges (head :: next :: rest) →
                  ¬ ClockStraddlesAt clock cutoff high low := by
              intro high low edgeMem straddles
              have highMem : high ∈ head :: next :: rest := by
                obtain ⟨front, back, listEq⟩ :=
                  mem_adjacentEdges_iff.mp edgeMem
                rw [listEq]
                simp
              have lowMem : low ∈ head :: next :: rest := by
                obtain ⟨front, back, listEq⟩ :=
                  mem_adjacentEdges_iff.mp edgeMem
                rw [listEq]
                simp
              have endpointLow :
                  ∀ endpoint ∈ head :: next :: rest,
                    clock endpoint < cutoff := by
                intro endpoint endpointMem
                rcases List.mem_cons.mp endpointMem with endpointEq | tailMem
                · simpa [endpointEq] using headLow
                · exact allTailLow endpoint tailMem
              have highLow := endpointLow high highMem
              have lowLow := endpointLow low lowMem
              rcases straddles with highSide | lowSide
              · exact
                  (Nat.not_le_of_lt highLow) highSide.1
              · exact
                  (Nat.not_le_of_lt lowLow) lowSide.1
            have firstEdge :
                (firstHigh, firstLow) ∈
                  adjacentEdges (head :: next :: rest) := by
              simp only [adjacentEdges, List.mem_cons]
              exact firstMem
            exact False.elim <|
              noStraddler firstEdge firstStraddles

/--
There is a unique unordered adjacent endpoint pair that crosses a monotone
clock cut.

No `Nodup` assumption on `xs` is needed: cut ordering itself ensures that a
high-to-low transition can occur at only one list position.
-/
theorem adjacent_clockStraddles_unique
    {α : Type*} {clock : α → ℕ} {cutoff : ℕ} {xs : List α}
    (ordered : ClockCutOrderedAt clock cutoff xs)
    {first second third fourth : α}
    (firstAdjacent : Adjacent xs first second)
    (firstStraddles : ClockStraddlesAt clock cutoff first second)
    (secondAdjacent : Adjacent xs third fourth)
    (secondStraddles : ClockStraddlesAt clock cutoff third fourth) :
    (first = third ∧ second = fourth) ∨
      (first = fourth ∧ second = third) := by
  rcases adjacent_iff_mem_adjacentEdges_or_swap.mp firstAdjacent with
    firstForward | firstBackward
  · rcases adjacent_iff_mem_adjacentEdges_or_swap.mp secondAdjacent with
      secondForward | secondBackward
    · have endpointEq :=
        adjacentEdges_straddler_unique clock cutoff ordered
          firstForward firstStraddles secondForward secondStraddles
      exact Or.inl endpointEq
    · have endpointEq :=
        adjacentEdges_straddler_unique clock cutoff ordered
          firstForward firstStraddles secondBackward
          (by
            simpa [ClockStraddlesAt, and_comm, or_comm] using
              secondStraddles)
      exact Or.inr endpointEq
  · rcases adjacent_iff_mem_adjacentEdges_or_swap.mp secondAdjacent with
      secondForward | secondBackward
    · have endpointEq :=
        adjacentEdges_straddler_unique clock cutoff ordered
          firstBackward
          (by
            simpa [ClockStraddlesAt, and_comm, or_comm] using
              firstStraddles)
          secondForward secondStraddles
      exact Or.inr ⟨endpointEq.2, endpointEq.1⟩
    · have endpointEq :=
        adjacentEdges_straddler_unique clock cutoff ordered
          firstBackward
          (by
            simpa [ClockStraddlesAt, and_comm, or_comm] using
              firstStraddles)
          secondBackward
          (by
            simpa [ClockStraddlesAt, and_comm, or_comm] using
              secondStraddles)
      exact Or.inl ⟨endpointEq.2, endpointEq.1⟩

private theorem pairwise_rel_of_mem_of_mem_of_ne
    {α : Type*} {relation : α → α → Prop}
    (symmetric :
      ∀ {first second : α},
        relation first second → relation second first) :
    ∀ {xs : List α}, xs.Pairwise relation →
      ∀ {first second : α},
        first ∈ xs → second ∈ xs → first ≠ second →
          relation first second := by
  intro xs pairwise
  induction xs with
  | nil =>
      simp
  | cons head tail ih =>
      have pairwiseParts := List.pairwise_cons.mp pairwise
      intro first second firstMem secondMem distinct
      rcases List.mem_cons.mp firstMem with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondMem with secondHead | secondTail
        · exact False.elim (distinct secondHead.symm)
        · exact pairwiseParts.1 second secondTail
      · rcases List.mem_cons.mp secondMem with secondHead | secondTail
        · subst second
          exact symmetric (pairwiseParts.1 first firstTail)
        · exact ih pairwiseParts.2 firstTail secondTail distinct

private theorem pairing_chunks_disjoint_of_ne
    {n : ℕ} {matching : List (Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    {first second : Pairing n}
    (firstMem : first ∈ matching) (secondMem : second ∈ matching)
    (distinct : first ≠ second) :
    List.Disjoint [first.winner, first.loser]
      [second.winner, second.loser] := by
  have chunksPairwise :
      matching.Pairwise
        (Function.onFun List.Disjoint fun pairing : Pairing n =>
          [pairing.winner, pairing.loser]) :=
    (List.nodup_flatMap.mp endpointsNodup).2
  exact
    pairwise_rel_of_mem_of_mem_of_ne
      (fun {_ _} disjoint => List.disjoint_comm.mp disjoint)
      chunksPairwise firstMem secondMem distinct

/--
Endpoint-disjoint adjacent pairing tuples cannot both cross the same monotone
clock cut unless they are the same tuple.

This is the matching-independent list bridge: its hypotheses are exactly the
endpoint `Nodup`, adjacency, and clock-cut order components later supplied by
`MatchingValid` and the episode clock invariant.
-/
theorem pairings_eq_of_mem_of_clockStraddles
    {n : ℕ} {clock : Element n → ℕ} {cutoff : ℕ}
    {elements : List (Element n)} {matching : List (Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    (ordered : ClockCutOrderedAt clock cutoff elements)
    {first second : Pairing n}
    (firstMem : first ∈ matching) (secondMem : second ∈ matching)
    (firstAdjacent :
      Adjacent elements first.winner first.loser)
    (firstStraddles :
      ClockStraddlesAt clock cutoff first.winner first.loser)
    (secondAdjacent :
      Adjacent elements second.winner second.loser)
    (secondStraddles :
      ClockStraddlesAt clock cutoff second.winner second.loser) :
    first = second := by
  by_contra distinct
  have chunksDisjoint :=
    pairing_chunks_disjoint_of_ne endpointsNodup
      firstMem secondMem distinct
  have boundaryEq :=
    adjacent_clockStraddles_unique ordered
      firstAdjacent firstStraddles secondAdjacent secondStraddles
  rw [List.disjoint_left] at chunksDisjoint
  rcases boundaryEq with direct | swapped
  · exact
      chunksDisjoint (a := first.winner) (by simp)
        (by simp [direct.1])
  · exact
      chunksDisjoint (a := first.winner) (by simp)
        (by simp [swapped.1])

/-- Pairing tuples in a matching whose endpoint clocks cross `cutoff`. -/
def clockStraddlingPairings {n : ℕ} (clock : Element n → ℕ)
    (cutoff : ℕ) (matching : List (Pairing n)) : List (Pairing n) :=
  matching.filter fun pairing =>
    decide
      (ClockStraddlesAt clock cutoff pairing.winner pairing.loser)

private theorem pairingWinners_sublist
    {n : ℕ} (matching : List (Pairing n)) :
    (matching.map Pairing.winner).Sublist
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]) := by
  induction matching with
  | nil =>
      exact .slnil
  | cons pairing matching ih =>
      exact (ih.cons pairing.loser).cons_cons pairing.winner

private theorem matching_nodup_of_endpoints_nodup
    {n : ℕ} {matching : List (Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup) :
    matching.Nodup := by
  have winnersNodup :
      (matching.map Pairing.winner).Nodup :=
    (pairingWinners_sublist matching).nodup endpointsNodup
  exact winnersNodup.of_map Pairing.winner

/--
At most one tuple of an endpoint-disjoint adjacent matching crosses a monotone
clock cut.
-/
theorem length_clockStraddlingPairings_le_one
    {n : ℕ} {clock : Element n → ℕ} {cutoff : ℕ}
    {elements : List (Element n)} {matching : List (Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    (adjacent :
      ∀ pairing ∈ matching,
        Adjacent elements pairing.winner pairing.loser)
    (ordered : ClockCutOrderedAt clock cutoff elements) :
    (clockStraddlingPairings clock cutoff matching).length ≤ 1 := by
  generalize selectedEq :
    clockStraddlingPairings clock cutoff matching = selected
  have selectedNodup : selected.Nodup := by
    rw [← selectedEq]
    apply List.Nodup.filter
    exact matching_nodup_of_endpoints_nodup endpointsNodup
  cases selected with
  | nil =>
      simp
  | cons first tail =>
      cases tail with
      | nil =>
          simp
      | cons second rest =>
          have firstSelected :
              first ∈
                clockStraddlingPairings clock cutoff matching := by
            rw [selectedEq]
            simp
          have secondSelected :
              second ∈
                clockStraddlingPairings clock cutoff matching := by
            rw [selectedEq]
            simp
          have firstInfo := List.mem_filter.mp firstSelected
          have secondInfo := List.mem_filter.mp secondSelected
          have firstStraddles :
              ClockStraddlesAt clock cutoff
                first.winner first.loser := by
            simpa [clockStraddlingPairings] using firstInfo.2
          have secondStraddles :
              ClockStraddlesAt clock cutoff
                second.winner second.loser := by
            simpa [clockStraddlingPairings] using secondInfo.2
          have pairingEq :
              first = second :=
            pairings_eq_of_mem_of_clockStraddles
              endpointsNodup ordered
              firstInfo.1 secondInfo.1
              (adjacent first firstInfo.1) firstStraddles
              (adjacent second secondInfo.1) secondStraddles
          subst second
          simp at selectedNodup

/--
Concrete `MatchingValid` specialization of the one-pass unique-cut lemma.
-/
theorem MatchingValid.length_clockStraddlingPairings_le_one
    {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid :
      MatchingValid params state sourceId source matching)
    (clock : Element n → ℕ) (cutoff : ℕ)
    (ordered :
      ClockCutOrderedAt clock cutoff source.elements) :
    (clockStraddlingPairings clock cutoff matching).length ≤ 1 := by
  exact
    Splay.Interface.length_clockStraddlingPairings_le_one
      (clock := clock) (cutoff := cutoff)
      (elements := source.elements) (matching := matching)
      valid.2.1
      (fun (pairing : Pairing n) pairingMem =>
        (valid.2.2.2.1 pairing pairingMem).1)
      ordered

end Splay.Interface
