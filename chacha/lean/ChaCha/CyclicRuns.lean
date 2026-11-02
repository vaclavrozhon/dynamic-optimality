import ChaCha.TurnAccounting
import ChaCha.Demands

/-!
# Concrete ordered query words and cyclic run directions

This file constructs direction words from actual ordered labels. Consecutive
equal labels emit no direction. The run identities here therefore connect the
direction accounting to key/cell words, rather than postulating turn counts.
-/

namespace ChaCha.CyclicRuns

open TurnAccounting

variable {α : Type*} [LinearOrder α]

/-- The signed nonzero edge between two ordered labels. -/
def edgeDirection (a b : α) : List Bool :=
  if a = b then [] else [decide (a < b)]

@[simp] theorem edgeDirection_self (a : α) : edgeDirection a a = [] := by
  simp [edgeDirection]

def directionsFrom : α → List α → List Bool
  | _, [] => []
  | a, b :: bs => edgeDirection a b ++ directionsFrom b bs

def directions : List α → List Bool
  | [] => []
  | a :: as => directionsFrom a as

/-- The wrap edge is placed first; turn counts are independent of this choice. -/
def cyclicDirections : List α → List Bool
  | [] => []
  | a :: as => directionsFrom (as.getLastD a) (a :: as)

def wordTurns (xs : List α) : ℕ := TurnAccounting.cyclicTurns (cyclicDirections xs)

theorem cyclicDirections_eq_from (fallback : α) (xs : List α) :
    cyclicDirections xs = directionsFrom (xs.getLastD fallback) xs := by
  cases xs with
  | nil => rfl
  | cons a as => simp only [cyclicDirections, List.getLastD_cons]

omit [LinearOrder α] in
theorem lastD_append (xs ys : List α) (fallback : α) :
    (xs ++ ys).getLastD fallback = ys.getLastD (xs.getLastD fallback) := by
  induction xs generalizing fallback with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.getLastD_cons]
    exact ih x

theorem directionsFrom_append (a : α) (xs ys : List α) :
    directionsFrom a (xs ++ ys) =
      directionsFrom a xs ++ directionsFrom (xs.getLastD a) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, directionsFrom, ih, List.getLastD_cons,
      List.append_assoc]

@[simp] theorem directionsFrom_cons_self (a : α) (xs : List α) :
    directionsFrom a (a :: xs) = directionsFrom a xs := by simp [directionsFrom]

theorem directionsFrom_cons (a b : α) (bs : List α) :
    directionsFrom a (b :: bs) = edgeDirection a b ++ directions (b :: bs) := rfl

/-- Joining two nonempty key blocks at an equal endpoint introduces no extra
direction. This is exactly the use made of the normalized first-return rule. -/
theorem directions_join_matching (a b : α) (xs ys : List α)
    (matching : xs.getLastD a = b) :
    directions ((a :: xs) ++ b :: ys) =
      directions (a :: xs) ++ directions (b :: ys) := by
  simp only [List.cons_append, directions, directionsFrom_append, matching,
    directionsFrom_cons_self]

/-- Two unequal endpoints introduce their actual signed macro edge. -/
theorem directions_join (a b : α) (xs ys : List α) :
    directions ((a :: xs) ++ b :: ys) =
      directions (a :: xs) ++ edgeDirection (xs.getLastD a) b ++ directions (b :: ys) := by
  simp [directions, directionsFrom_append, directionsFrom, List.append_assoc]

theorem cyclicTurns_move_head (b : Bool) (bs : List Bool) :
    TurnAccounting.cyclicTurns (b :: bs) = TurnAccounting.cyclicTurns (bs ++ [b]) := by
  unfold TurnAccounting.cyclicTurns
  rw [TurnAccounting.getLastD_append]
  simp only [List.getLastD_cons, List.getLastD_nil]
  rw [TurnAccounting.changesFrom_append]
  simp only [TurnAccounting.changesFrom]
  omega

/-- Cyclic direction-turn counts are invariant under any change of starting edge. -/
theorem cyclicTurns_swap_append (as bs : List Bool) :
    TurnAccounting.cyclicTurns (as ++ bs) = TurnAccounting.cyclicTurns (bs ++ as) := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    calc
      _ = TurnAccounting.cyclicTurns ((as ++ bs) ++ [a]) := cyclicTurns_move_head _ _
      _ = TurnAccounting.cyclicTurns (as ++ (bs ++ [a])) := by rw [List.append_assoc]
      _ = TurnAccounting.cyclicTurns ((bs ++ [a]) ++ as) := ih _
      _ = TurnAccounting.cyclicTurns (bs ++ a :: as) := by simp [List.append_assoc]

/-- The same cyclic key-turn count, placing the wrap edge last. -/
theorem wordTurns_close_last (a : α) (as : List α) :
    wordTurns (a :: as) = TurnAccounting.cyclicTurns (directions ((a :: as) ++ [a])) := by
  unfold wordTurns cyclicDirections
  simp only [directionsFrom, List.cons_append, directions, directionsFrom_append]
  simp only [List.append_nil]
  exact cyclicTurns_swap_append _ _

/-- A nonempty block of actual ordered fine labels, with no quotienting of
occurrences. Repeated labels remain in the block and emit no direction. -/
structure Block (α : Type*) where
  first : α
  rest : List α
  deriving DecidableEq

def Block.word (b : Block α) : List α := b.first :: b.rest
def Block.last (b : Block α) : α := b.rest.getLastD b.first
def Block.micro (b : Block α) : List Bool := directions b.word

/-- Encode each actual block's micro steps, followed by its outgoing macro step.
`closing` is the first label following the last block. -/
def encode (closing : α) : List (Block α) → List Run
  | [] => []
  | b :: bs =>
      { micro := b.micro,
        exit := decide (b.last < ((bs.head?).map Block.first).getD closing) } :: encode closing bs

/-- Every boundary, including the final closing boundary, crosses fine labels. -/
def DistinctBoundaries (closing : α) : List (Block α) → Prop
  | [] => True
  | b :: bs =>
      b.last ≠ ((bs.head?).map Block.first).getD closing ∧ DistinctBoundaries closing bs

/-- Every boundary is instead an equal endpoint, as in one normalized micro
subsequence. This includes the closing join. -/
def MatchingBoundaries (closing : α) : List (Block α) → Prop
  | [] => True
  | b :: bs =>
      b.last = ((bs.head?).map Block.first).getD closing ∧ MatchingBoundaries closing bs

theorem directions_blocks_distinct (closing : α) (b : Block α) (bs : List (Block α))
    (boundary : DistinctBoundaries closing (b :: bs)) :
    directions (((b :: bs).map Block.word).flatten ++ [closing]) =
      ((encode closing (b :: bs)).map Run.parentBlock).flatten := by
  induction bs generalizing b with
  | nil =>
    have hb : b.last ≠ closing := boundary.1
    simpa [Block.word, Block.micro, Block.last, encode, directions,
      directionsFrom_append, directionsFrom, edgeDirection, Run.parentBlock] using
      congrArg (fun ds => directionsFrom b.first b.rest ++ ds)
        (show edgeDirection b.last closing = [decide (b.last < closing)] from
          by simp [edgeDirection, hb])
  | cons c cs ih =>
    have hbc : b.last ≠ c.first := boundary.1
    have hrest := ih c boundary.2
    have htail : directions (((c :: cs).map Block.word).flatten ++ [closing]) =
        directionsFrom c.first
          (c.rest ++ ((cs.map Block.word).flatten ++ [closing])) := by
      simp [Block.word, directions, List.append_assoc]
    rw [htail] at hrest
    simp only [List.map_cons, List.flatten_cons, Block.word, List.cons_append, directions]
    simp only [List.append_assoc, List.cons_append]
    rw [directionsFrom_append]
    simp only [directionsFrom]
    rw [hrest]
    simp [Block.last] at hbc
    simp [encode, Block.micro, Block.word, Block.last, directions,
      Run.parentBlock, edgeDirection, hbc, List.append_assoc]

/-- Concrete parent-word bridge: direction accounting on the encoded runs is
exactly the turn count of the flattened actual fine-label query word. -/
theorem parentTurns_encode (b : Block α) (bs : List (Block α))
    (boundary : DistinctBoundaries b.first (b :: bs)) :
    parentTurns (encode b.first (b :: bs)) = wordTurns ((b :: bs).map Block.word).flatten := by
  have hc := directions_blocks_distinct b.first b bs boundary
  have hw : wordTurns ((b :: bs).map Block.word).flatten =
      TurnAccounting.cyclicTurns
        (directions (((b :: bs).map Block.word).flatten ++ [b.first])) := by
    simpa [Block.word, List.append_assoc] using
      wordTurns_close_last b.first (b.rest ++ (bs.map Block.word).flatten)
  rw [hw, hc]
  rfl

/-- A chain of matching run endpoints contributes no directions at its joins. -/
theorem directions_blocks_matching (closing : α) (b : Block α) (bs : List (Block α))
    (boundary : MatchingBoundaries closing (b :: bs)) :
    directions (((b :: bs).map Block.word).flatten ++ [closing]) =
      ((b :: bs).map Block.micro).flatten := by
  induction bs generalizing b with
  | nil =>
    have hb : b.last = closing := boundary.1
    simp [Block.word, Block.micro, Block.last, directions, directionsFrom_append,
      directionsFrom, ← hb]
  | cons c cs ih =>
    have hbc : b.last = c.first := boundary.1
    have hrest := ih c boundary.2
    have htail : directions (((c :: cs).map Block.word).flatten ++ [closing]) =
        directionsFrom c.first
          (c.rest ++ ((cs.map Block.word).flatten ++ [closing])) := by
      simp [Block.word, directions, List.append_assoc]
    rw [htail] at hrest
    simp only [List.map_cons, List.flatten_cons, Block.word, List.cons_append, directions]
    simp only [List.append_assoc, List.cons_append]
    rw [directionsFrom_append]
    change directionsFrom b.first b.rest ++
      directionsFrom b.last (c.first :: (c.rest ++ ((cs.map Block.word).flatten ++ [closing]))) = _
    rw [hbc, directionsFrom_cons_self, hrest]
    rfl

/-- Concrete micro-word bridge under the normalized endpoint-matching rule. -/
theorem microTurns_matching (b : Block α) (bs : List (Block α))
    (boundary : MatchingBoundaries b.first (b :: bs)) :
    wordTurns ((b :: bs).map Block.word).flatten =
      TurnAccounting.cyclicTurns (((b :: bs).map Block.micro).flatten) := by
  have hc := directions_blocks_matching b.first b bs boundary
  have hw : wordTurns ((b :: bs).map Block.word).flatten =
      TurnAccounting.cyclicTurns
        (directions (((b :: bs).map Block.word).flatten ++ [b.first])) := by
    simpa [Block.word, List.append_assoc] using
      wordTurns_close_last b.first (b.rest ++ (bs.map Block.word).flatten)
  rw [hw, hc]

variable {C : Type*} [LinearOrder C]

def Block.Homogeneous (coarse : α → C) (b : Block α) : Prop :=
  ∀ x ∈ b.word, coarse x = coarse b.first

def Block.coarseSingleton (coarse : α → C) (b : Block α) : Block C :=
  ⟨coarse b.first, []⟩

omit [LinearOrder α] [LinearOrder C] in
theorem Block.homogeneous_last (coarse : α → C) (b : Block α)
    (h : b.Homogeneous coarse) : coarse b.last = coarse b.first :=
  h _ List.getLastD_mem_cons

/-- Disjoint convex coarse cells have the same left/right order as their fine
labels. Monotonicity of the coarse projection expresses exactly that convexity. -/
theorem direction_coarse (coarse : α → C) (ordered : Monotone coarse) (a b : α)
    (different : coarse a ≠ coarse b) : decide (a < b) = decide (coarse a < coarse b) := by
  have hiff : a < b ↔ coarse a < coarse b := by
    constructor
    · intro h
      exact lt_of_le_of_ne (ordered (le_of_lt h)) different
    · intro h
      by_contra hn
      exact (not_le_of_gt h) (ordered (le_of_not_gt hn))
  by_cases h : a < b
  · simp [h, hiff.mp h]
  · have hn : ¬ coarse a < coarse b := fun hc => h (hiff.mpr hc)
    simp [h, hn]

/-- The encoded macro directions equal the directions between coarse cell names,
for any homogeneous runs in an ordered interval partition. -/
theorem encode_coarse_directions (coarse : α → C) (ordered : Monotone coarse)
    (closing : α) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse closing) (blocks.map (Block.coarseSingleton coarse))) :
    (encode closing blocks).map Run.exit =
      (encode (coarse closing) (blocks.map (Block.coarseSingleton coarse))).map Run.exit := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    have hb := homogeneous b (by simp)
    have hbs : ∀ c ∈ bs, c.Homogeneous coarse := fun c hc => homogeneous c (by simp [hc])
    have htail := ih hbs boundary.2
    have hlast := Block.homogeneous_last coarse b hb
    cases bs with
    | nil =>
      have hne : coarse b.first ≠ coarse closing := boundary.1
      have hdir := direction_coarse coarse ordered b.last closing (hlast ▸ hne)
      change [decide (b.last < closing)] = [decide (coarse b.first < coarse closing)]
      rw [hdir, hlast]
    | cons c cs =>
      have hne : coarse b.first ≠ coarse c.first := boundary.1
      have hdir := direction_coarse coarse ordered b.last c.first (hlast ▸ hne)
      change decide (b.last < c.first) :: (encode closing (c :: cs)).map Run.exit =
        decide (coarse b.first < coarse c.first) ::
          (encode (coarse closing) ((c :: cs).map (Block.coarseSingleton coarse))).map Run.exit
      rw [hdir, hlast, htail]

theorem parent_eq_macro_of_empty_micros (rs : List Run)
    (empty : ∀ r ∈ rs, r.micro = []) : parentTurns rs = macroTurns rs := by
  have h : (rs.map Run.parentBlock).flatten = rs.map Run.exit := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      have hr := empty r (by simp)
      have hrs : ∀ s ∈ rs, s.micro = [] := fun s hs => empty s (by simp [hs])
      simp [Run.parentBlock, hr, ih hrs]
  exact congrArg TurnAccounting.cyclicTurns h

omit [LinearOrder α] in
theorem encode_singleton_micros (coarse : α → C) (closing : C) (blocks : List (Block α)) :
    ∀ r ∈ encode closing (blocks.map (Block.coarseSingleton coarse)), r.micro = [] := by
  induction blocks with
  | nil => simp [encode]
  | cons b bs ih =>
    intro r hr
    simp only [List.map_cons, encode, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rfl
    · exact ih r hr

omit [LinearOrder α] [LinearOrder C] in
theorem flatten_singletons (f : α → C) (xs : List α) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Concrete macro-word bridge. The run encoding's macro turn count is exactly
the cyclic turn count of the actual coarse cell word. -/
theorem macroTurns_encode (coarse : α → C) (ordered : Monotone coarse)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    macroTurns (encode b.first (b :: bs)) = wordTurns ((b :: bs).map (fun c => coarse c.first)) := by
  have he := encode_coarse_directions coarse ordered b.first (b :: bs) homogeneous boundary
  have hp := parentTurns_encode (b.coarseSingleton coarse)
    (bs.map (Block.coarseSingleton coarse)) boundary
  change parentTurns (encode (coarse b.first) ((b :: bs).map (Block.coarseSingleton coarse))) =
    wordTurns (((b :: bs).map (Block.coarseSingleton coarse)).map Block.word).flatten at hp
  rw [parent_eq_macro_of_empty_micros _ (encode_singleton_micros coarse (coarse b.first) (b :: bs))] at hp
  change TurnAccounting.cyclicTurns ((encode b.first (b :: bs)).map Run.exit) = _
  rw [he]
  change macroTurns (encode (coarse b.first) ((b :: bs).map (Block.coarseSingleton coarse))) = _
  rw [hp]
  congr 1
  simp [Block.coarseSingleton, Block.word, List.map_map, Function.comp_def, flatten_singletons]

theorem transitionsFrom_append (coarse : α → C) (a : α) (xs ys : List α) :
    ChaCha.transitionsFrom coarse id a (xs ++ ys) =
      ChaCha.transitionsFrom coarse id a xs ++
        ChaCha.transitionsFrom coarse id (xs.getLastD a) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, ChaCha.transitionsFrom, ih, List.getLastD_cons,
      List.append_assoc]

/-- A homogeneous coarse run emits exactly one `R` for each nonzero fine step. -/
theorem homogeneous_transitions (coarse : α → C) (a : α) (xs : List α)
    (homogeneous : ∀ x ∈ xs, coarse x = coarse a) :
    ChaCha.transitionsFrom coarse id a xs =
      (directionsFrom a xs).map (fun _ => true) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hax : coarse a = coarse x := (homogeneous x (by simp)).symm
    have hxs : ∀ z ∈ xs, coarse z = coarse x := by
      intro z hz
      exact (homogeneous z (by simp [hz])).trans hax
    have htail := ih x hxs
    by_cases h : a = x
    · simp [ChaCha.transitionsFrom, transitionLabel, h, directionsFrom,
        edgeDirection, htail]
    · simp [ChaCha.transitionsFrom, transitionLabel, hax, h, directionsFrom,
        edgeDirection, htail]

def Block.letters (b : Block α) : List Bool := b.micro.map (fun _ => true) ++ [false]

/-- Exact RL-word decomposition from actual coarse runs, with the final closing
query included. No run count or secondary transition equality is assumed. -/
theorem transitionWord_blocks (coarse : α → C) (closing : α)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse closing)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    transitionWord coarse id (((b :: bs).map Block.word).flatten ++ [closing]) =
      ((b :: bs).map Block.letters).flatten := by
  induction bs generalizing b with
  | nil =>
    have hb := homogeneous b (by simp)
    have hlast := Block.homogeneous_last coarse b hb
    have hdiff : coarse b.first ≠ coarse closing := boundary.1
    have hdiff' : coarse b.last ≠ coarse closing := hlast ▸ hdiff
    have hi := homogeneous_transitions coarse b.first b.rest (fun x hx => hb x (by simp [Block.word, hx]))
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Block.word, List.cons_append, transitionWord, transitionsFrom_append]
    simp only [ChaCha.transitionsFrom, List.append_nil]
    change ChaCha.transitionsFrom coarse id b.first b.rest ++
      (transitionLabel coarse id b.last closing).toList = b.letters
    rw [hi]
    simp [Block.letters, Block.micro, Block.word, directions, transitionLabel, hdiff']
  | cons c cs ih =>
    have hb := homogeneous b (by simp)
    have hlast := Block.homogeneous_last coarse b hb
    have hdiff : coarse b.first ≠ coarse c.first := boundary.1
    have hdiff' : coarse b.last ≠ coarse c.first := hlast ▸ hdiff
    have hi := homogeneous_transitions coarse b.first b.rest (fun x hx => hb x (by simp [Block.word, hx]))
    have htail := ih c (fun z hz => homogeneous z (by simp [hz])) boundary.2
    have htail' : ChaCha.transitionsFrom coarse id c.first
        (c.rest ++ ((cs.map Block.word).flatten ++ [closing])) =
        ((c :: cs).map Block.letters).flatten := by
      simpa [Block.word, transitionWord, List.append_assoc] using htail
    simp only [List.map_cons, List.flatten_cons, Block.word, List.cons_append, transitionWord]
    simp only [List.append_assoc, List.cons_append]
    rw [transitionsFrom_append]
    simp only [ChaCha.transitionsFrom]
    rw [hi, htail']
    simp [Block.last] at hdiff'
    simp [Block.letters, Block.micro, Block.word, directions,
      transitionLabel, hdiff', List.append_assoc]

theorem rlFrom_true_map_true (ds suffix : List Bool) :
    rlFrom true (ds.map (fun _ => true) ++ false :: suffix) = 1 + rlFrom false suffix := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simpa [rlFrom, rlCharge] using ih

theorem rlFrom_false_map_true (ds suffix : List Bool) :
    rlFrom false (ds.map (fun _ => true) ++ false :: suffix) =
      (if ds = [] then 0 else 1) + rlFrom false suffix := by
  cases ds with
  | nil => rfl
  | cons d ds => simpa [rlFrom, rlCharge] using rlFrom_true_map_true ds suffix

/-- One unit for each fine-nontrivial run, counting run occurrences. -/
def nontrivialRuns (blocks : List (Block α)) : ℕ :=
  (blocks.map fun b => if b.micro = [] then 0 else 1).sum

theorem rlCount_block_letters (blocks : List (Block α)) :
    rlCount (blocks.map Block.letters).flatten = nontrivialRuns blocks := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [rlCount, List.map_cons, List.flatten_cons, Block.letters, List.append_assoc,
      List.singleton_append]
    rw [rlFrom_false_map_true]
    simpa only [rlCount, nontrivialRuns, List.map_cons, List.sum_cons] using
      congrArg (fun k => (if b.micro = [] then 0 else 1) + k) ih

/-- The manuscript's actual finite RL-demand count becomes exactly the number
of nontrivial coarse runs when the last run is explicitly completed. -/
theorem demands_closed_blocks (coarse : α → C) (closing : α)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse closing)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    demands coarse id (((b :: bs).map Block.word).flatten ++ [closing]) =
      nontrivialRuns (b :: bs) := by
  unfold demands
  rw [transitionWord_blocks coarse closing b bs homogeneous boundary, rlCount_block_letters]

/-- Consequently every finite demand in the unclosed word is included. -/
theorem demands_blocks_le_nontrivial (coarse : α → C)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    demands coarse id ((b :: bs).map Block.word).flatten ≤ nontrivialRuns (b :: bs) := by
  have h := demands_le_append coarse id ((b :: bs).map Block.word).flatten [b.first]
  rw [demands_closed_blocks coarse b.first b bs homogeneous boundary] at h
  exact h

/-- Canonical finite coarse runs, retaining every actual fine-label occurrence. -/
def coarseRuns (coarse : α → C) : List α → List (Block α)
  | [] => []
  | x :: xs =>
      match coarseRuns coarse xs with
      | [] => [⟨x, []⟩]
      | b :: bs =>
          if coarse x = coarse b.first then ⟨x, b.word⟩ :: bs
          else ⟨x, []⟩ :: b :: bs

/-- Consecutive blocks are distinct coarse runs. The final wrap is separate. -/
def AdjacentDistinct (coarse : α → C) : List (Block α) → Prop
  | [] => True
  | [_] => True
  | b :: c :: cs => coarse b.first ≠ coarse c.first ∧ AdjacentDistinct coarse (c :: cs)

omit [LinearOrder α] in
theorem coarseRuns_flatten (coarse : α → C) (xs : List α) :
    ((coarseRuns coarse xs).map Block.word).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [coarseRuns]
    cases hr : coarseRuns coarse xs with
    | nil => simpa [hr, Block.word] using congrArg (List.cons x) ih
    | cons b bs =>
      by_cases h : coarse x = coarse b.first
      · simp only [h, ↓reduceIte, List.map_cons, List.flatten_cons, Block.word,
          List.cons_append]
        simpa [hr, Block.word] using congrArg (List.cons x) ih
      · simp only [h, ↓reduceIte, List.map_cons, List.flatten_cons, Block.word,
          List.nil_append, List.cons_append]
        simpa [hr, Block.word] using congrArg (List.cons x) ih

omit [LinearOrder α] in
theorem coarseRuns_homogeneous (coarse : α → C) (xs : List α) :
    ∀ b ∈ coarseRuns coarse xs, b.Homogeneous coarse := by
  induction xs with
  | nil => simp [coarseRuns]
  | cons x xs ih =>
    simp only [coarseRuns]
    cases hr : coarseRuns coarse xs with
    | nil => simp [Block.Homogeneous, Block.word]
    | cons b bs =>
      have hb := ih b (by simp [hr])
      by_cases h : coarse x = coarse b.first
      · simp only [h, ↓reduceIte, List.mem_cons]
        intro c hc
        rcases hc with rfl | hc
        · intro z hz
          simp only [Block.word, List.mem_cons] at hz
          rcases hz with rfl | hz
          · rfl
          · exact (hb z (List.mem_cons.mpr hz)).trans h.symm
        · exact ih c (by simp [hr, hc])
      · simp only [h, ↓reduceIte, List.mem_cons]
        intro c hc
        rcases hc with rfl | rfl | hc
        · simp [Block.Homogeneous, Block.word]
        · exact hb
        · exact ih c (by simp [hr, hc])

omit [LinearOrder α] in
theorem coarseRuns_adjacent (coarse : α → C) (xs : List α) :
    AdjacentDistinct coarse (coarseRuns coarse xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    simp only [coarseRuns]
    cases hr : coarseRuns coarse xs with
    | nil => trivial
    | cons b bs =>
      rw [hr] at ih
      by_cases h : coarse x = coarse b.first
      · simp only [h, ↓reduceIte]
        cases bs with
        | nil => trivial
        | cons c cs =>
          exact ⟨by simpa only [h] using ih.1, ih.2⟩
      · simp only [h, ↓reduceIte]
        exact ⟨h, ih⟩

omit [LinearOrder α] in
/-- Every finite word has an explicitly computed faithful homogeneous run
decomposition with all adjacent coarse cells distinct. -/
theorem coarseRuns_spec (coarse : α → C) (xs : List α) :
    ((coarseRuns coarse xs).map Block.word).flatten = xs ∧
    (∀ b ∈ coarseRuns coarse xs, b.Homogeneous coarse) ∧
    AdjacentDistinct coarse (coarseRuns coarse xs) :=
  ⟨coarseRuns_flatten coarse xs, coarseRuns_homogeneous coarse xs, coarseRuns_adjacent coarse xs⟩

theorem cyclicDirections_append (a b : α) (as bs : List α) :
    cyclicDirections ((a :: as) ++ b :: bs) =
      edgeDirection (bs.getLastD b) a ++ directions (a :: as) ++
        edgeDirection (as.getLastD a) b ++ directions (b :: bs) := by
  simp only [List.cons_append, cyclicDirections, lastD_append, List.getLastD_cons,
    directionsFrom, directionsFrom_append, directions, List.append_assoc]

/-- Actual ordered key-word turns are invariant under a cyclic change of origin. -/
theorem wordTurns_swap_append (xs ys : List α) : wordTurns (xs ++ ys) = wordTurns (ys ++ xs) := by
  cases xs with
  | nil => simp
  | cons a as =>
    cases ys with
    | nil => simp
    | cons b bs =>
      unfold wordTurns
      rw [cyclicDirections_append, cyclicDirections_append]
      have h := cyclicTurns_swap_append
        (edgeDirection (bs.getLastD b) a ++ directions (a :: as))
        (edgeDirection (as.getLastD a) b ++ directions (b :: bs))
      simpa only [List.append_assoc] using h

/-- Join two nonempty actual blocks without dropping their equal or repeated
endpoint occurrences. -/
def Block.append (a b : Block α) : Block α := ⟨a.first, a.rest ++ b.word⟩

omit [LinearOrder α] in
@[simp] theorem Block.word_append (a b : Block α) : (a.append b).word = a.word ++ b.word := rfl

omit [LinearOrder α] in
@[simp] theorem Block.last_append (a b : Block α) : (a.append b).last = b.last := by
  simp only [Block.append, Block.last, Block.word, lastD_append, List.getLastD_cons]

omit [LinearOrder α] [LinearOrder C] in
theorem Block.homogeneous_append (coarse : α → C) (a b : Block α)
    (ha : a.Homogeneous coarse) (hb : b.Homogeneous coarse)
    (same : coarse a.first = coarse b.first) : (a.append b).Homogeneous coarse := by
  intro x hx
  rw [Block.word_append] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact (hb x h).trans same.symm

/-- Merging the last and first coarse runs preserves every actual cyclic turn. -/
theorem wordTurns_merge_ends (a b : Block α) (middle : List (Block α)) :
    wordTurns ((a :: (middle ++ [b])).map Block.word).flatten =
      wordTurns (((b.append a) :: middle).map Block.word).flatten := by
  have h := wordTurns_swap_append (a.word ++ (middle.map Block.word).flatten) b.word
  simpa [List.map_append, List.flatten_append, Block.word_append, List.append_assoc] using h

theorem rlFrom_map_true (state : Bool) (ds : List Bool) :
    rlFrom state (ds.map (fun _ => true)) = 0 := by
  induction ds generalizing state with
  | nil => rfl
  | cons d ds ih =>
    cases state <;>
      simpa only [List.map_cons, rlFrom, rlCharge, Nat.zero_add] using ih true

theorem demands_one_block (coarse : α → C) (b : Block α) (hb : b.Homogeneous coarse) :
    demands coarse id b.word = 0 := by
  have h := homogeneous_transitions coarse b.first b.rest
    (fun x hx => hb x (by simp [Block.word, hx]))
  unfold demands rlCount
  change rlFrom false (ChaCha.transitionsFrom coarse id b.first b.rest) = 0
  rw [h, rlFrom_map_true]

/-- Completing the first homogeneous run adds exactly one demand when it had a
nonzero fine step; the remaining query word is left completely unrestricted. -/
theorem demands_block_cons (coarse : α → C) (b c : Block α) (cs : List (Block α))
    (hb : b.Homogeneous coarse) (different : coarse b.first ≠ coarse c.first) :
    demands coarse id (((b :: c :: cs).map Block.word).flatten) =
      (if b.micro = [] then 0 else 1) +
        demands coarse id (((c :: cs).map Block.word).flatten) := by
  have hlast := Block.homogeneous_last coarse b hb
  have hd : coarse b.last ≠ coarse c.first := hlast ▸ different
  have h := homogeneous_transitions coarse b.first b.rest
    (fun x hx => hb x (by simp [Block.word, hx]))
  unfold demands rlCount
  simp only [List.map_cons, List.flatten_cons, Block.word, List.cons_append, transitionWord]
  rw [transitionsFrom_append]
  simp only [ChaCha.transitionsFrom]
  rw [h]
  have hedge : transitionLabel coarse id b.last c.first = some false := by
    simp [transitionLabel, hd]
  change rlFrom false
    (((directionsFrom b.first b.rest).map (fun _ => true)) ++
      ((transitionLabel coarse id b.last c.first).toList ++
      ChaCha.transitionsFrom coarse id c.first (c.rest ++ (cs.map Block.word).flatten))) = _
  rw [hedge]
  have hm : b.micro = directionsFrom b.first b.rest := rfl
  rw [hm]
  exact rlFrom_false_map_true (directionsFrom b.first b.rest)
    (ChaCha.transitionsFrom coarse id c.first (c.rest ++ (cs.map Block.word).flatten))

/-- Exact finite completed-run semantics of the original `demands` definition.
The final run is not completed and is therefore excluded by `dropLast`. -/
theorem demands_eq_completed_runs (coarse : α → C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse)
    (separated : AdjacentDistinct coarse blocks) :
    demands coarse id ((blocks.map Block.word).flatten) = nontrivialRuns blocks.dropLast := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    have hb := homogeneous b (by simp)
    cases bs with
    | nil => simpa [nontrivialRuns] using demands_one_block coarse b hb
    | cons c cs =>
      rw [demands_block_cons coarse b c cs hb separated.1]
      rw [ih (fun z hz => homogeneous z (by simp [hz])) separated.2]
      simp [nontrivialRuns]

/-- The canonical run construction computes the manuscript's actual finite D,
for every word and every coarse projection. -/
theorem demands_coarseRuns (coarse : α → C) (xs : List α) :
    demands coarse id xs = nontrivialRuns (coarseRuns coarse xs).dropLast := by
  have h := demands_eq_completed_runs coarse (coarseRuns coarse xs)
    (coarseRuns_homogeneous coarse xs) (coarseRuns_adjacent coarse xs)
  simpa only [coarseRuns_flatten] using h

/-- Coarse names actually visited by the run list. -/
def cells (coarse : α → C) (blocks : List (Block α)) : Finset C :=
  (blocks.map (fun b => coarse b.first)).toFinset

def cellBlocks (coarse : α → C) (blocks : List (Block α)) (c : C) : List (Block α) :=
  blocks.filter (fun b => coarse b.first = c)

def cellWord (coarse : α → C) (xs : List α) (c : C) : List α :=
  xs.filter (fun x => coarse x = c)

omit [LinearOrder α] in
theorem filter_block (coarse : α → C) (b : Block α) (c : C)
    (homogeneous : b.Homogeneous coarse) :
    cellWord coarse b.word c = if coarse b.first = c then b.word else [] := by
  by_cases h : coarse b.first = c
  · simp only [h, ↓reduceIte, cellWord]
    apply List.filter_eq_self.mpr
    intro x hx
    simpa using (homogeneous x hx).trans h
  · simp only [h, ↓reduceIte, cellWord]
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simpa using (show ¬ coarse x = c from fun heq => h ((homogeneous x hx).symm.trans heq))

omit [LinearOrder α] in
/-- Grouping whole homogeneous runs is exactly restriction of the actual query
word to that coarse cell; no occurrence is discarded or reordered within it. -/
theorem cellWord_blocks (coarse : α → C) (blocks : List (Block α)) (c : C)
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse) :
    cellWord coarse (blocks.map Block.word).flatten c =
      ((cellBlocks coarse blocks c).map Block.word).flatten := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    have hb := homogeneous b (by simp)
    have hbs : ∀ z ∈ bs, z.Homogeneous coarse := fun z hz => homogeneous z (by simp [hz])
    have htail := ih hbs
    have hhead := filter_block coarse b c hb
    change cellWord coarse (b.word ++ (bs.map Block.word).flatten) c = _
    have hsplit : cellWord coarse (b.word ++ (bs.map Block.word).flatten) c =
        cellWord coarse b.word c ++ cellWord coarse (bs.map Block.word).flatten c := by
      exact List.filter_append _ _
    rw [hsplit, hhead, htail]
    by_cases h : coarse b.first = c <;> simp [cellBlocks, h]

omit [LinearOrder α] in
theorem sum_cell_blocks (coarse : α → C) (blocks : List (Block α))
    (f : Block α → ℕ) (names : Finset C)
    (cover : ∀ b ∈ blocks, coarse b.first ∈ names) :
    ∑ c ∈ names, ((cellBlocks coarse blocks c).map f).sum = (blocks.map f).sum := by
  induction blocks with
  | nil => simp [cellBlocks]
  | cons b bs ih =>
    have hb := cover b (by simp)
    have hbs : ∀ z ∈ bs, coarse z.first ∈ names := fun z hz => cover z (by simp [hz])
    have hpoint (c : C) :
        ((cellBlocks coarse (b :: bs) c).map f).sum =
          (if coarse b.first = c then f b else 0) + ((cellBlocks coarse bs c).map f).sum := by
      by_cases h : coarse b.first = c <;> simp [cellBlocks, h]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hb, ih hbs]
    rfl

theorem sum_cells_internal (coarse : α → C) (blocks : List (Block α)) :
    ∑ c ∈ cells coarse blocks,
      (((cellBlocks coarse blocks c).map Block.micro).map linearTurns).sum =
        ((blocks.map Block.micro).map linearTurns).sum := by
  simp only [List.map_map]
  apply sum_cell_blocks
  intro b hb
  simp only [cells, List.mem_toFinset, List.mem_map]
  exact ⟨b, hb, rfl⟩

/-- The concrete cyclic endpoint condition supplied by normalized returns. -/
def ReturnsMatch (coarse : α → C) (blocks : List (Block α)) : Prop :=
  ∀ c ∈ cells coarse blocks, match cellBlocks coarse blocks c with
    | [] => True
    | b :: bs => MatchingBoundaries b.first (b :: bs)

def groupedJoins (coarse : α → C) (blocks : List (Block α)) : ℕ :=
  ∑ c ∈ cells coarse blocks, cyclicJoins ((cellBlocks coarse blocks c).map Block.micro)

/-- The exact micro counting equation for actual coarse-restricted query words.
Its return hypothesis concerns equal endpoint labels, not turn counts. -/
theorem actual_micro_decomposition (coarse : α → C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse)
    (returns : ReturnsMatch coarse blocks) :
    (∑ c ∈ cells coarse blocks, wordTurns (cellWord coarse (blocks.map Block.word).flatten c)) =
      ((blocks.map Block.micro).map linearTurns).sum + groupedJoins coarse blocks := by
  have hpoint (c : C) (hc : c ∈ cells coarse blocks) :
      wordTurns (cellWord coarse (blocks.map Block.word).flatten c) =
        (((cellBlocks coarse blocks c).map Block.micro).map linearTurns).sum +
          cyclicJoins ((cellBlocks coarse blocks c).map Block.micro) := by
    rw [cellWord_blocks coarse blocks c homogeneous]
    have hret := returns c hc
    cases hg : cellBlocks coarse blocks c with
    | nil => rfl
    | cons b bs =>
      simp only [hg] at hret
      rw [microTurns_matching b bs hret, cyclicTurns_flatten]
  calc
    _ = ∑ c ∈ cells coarse blocks,
        ((((cellBlocks coarse blocks c).map Block.micro).map linearTurns).sum +
          cyclicJoins ((cellBlocks coarse blocks c).map Block.micro)) :=
      Finset.sum_congr rfl hpoint
    _ = _ := by rw [Finset.sum_add_distrib, sum_cells_internal]; rfl

theorem encode_micro (closing : α) (blocks : List (Block α)) :
    (encode closing blocks).map Run.micro = blocks.map Block.micro := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simpa only [encode, List.map_cons] using congrArg (List.cons b.micro) ih

theorem runInternal_encode (closing : α) (blocks : List (Block α)) :
    runInternal (encode closing blocks) = ((blocks.map Block.micro).map linearTurns).sum := by
  have h := congrArg (fun xs => (xs.map linearTurns).sum) (encode_micro closing blocks)
  simpa only [runInternal, List.map_map, Function.comp_def] using h

/-- The local turn identity entirely in terms of actual ordered query words,
canonical direction events, and equal return endpoints. Grouping the micro words
is constructed by `filter`; its partition identity is proved above. -/
theorem actual_local_turn_identity (coarse : α → C) (ordered : Monotone coarse)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse)))
    (fine_boundary : DistinctBoundaries b.first (b :: bs))
    (returns : ReturnsMatch coarse (b :: bs)) :
    groupedJoins coarse (b :: bs) + wordTurns ((b :: bs).map Block.word).flatten +
        nontrivialMacroTurns (encode b.first (b :: bs)) =
      wordTurns ((b :: bs).map (fun c => coarse c.first)) +
        (∑ c ∈ cells coarse (b :: bs),
          wordTurns (cellWord coarse ((b :: bs).map Block.word).flatten c)) +
        entryTurns (encode b.first (b :: bs)) + exitTurns (encode b.first (b :: bs)) := by
  have hp := parent_decomposition (encode b.first (b :: bs))
  rw [parentTurns_encode b bs fine_boundary, runInternal_encode] at hp
  have hm := macro_decomposition (encode b.first (b :: bs))
  rw [macroTurns_encode coarse ordered b bs homogeneous boundary] at hm
  have hμ := actual_micro_decomposition coarse (b :: bs) homogeneous returns
  omega

omit [LinearOrder α] [LinearOrder C] in
theorem fine_boundaries_of_coarse (coarse : α → C) (closing : α) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse closing) (blocks.map (Block.coarseSingleton coarse))) :
    DistinctBoundaries closing blocks := by
  induction blocks with
  | nil => trivial
  | cons b bs ih =>
    have hb := homogeneous b (by simp)
    have hbs : ∀ z ∈ bs, z.Homogeneous coarse := fun z hz => homogeneous z (by simp [hz])
    have htail := ih hbs boundary.2
    have hlast := Block.homogeneous_last coarse b hb
    refine ⟨?_, htail⟩
    cases bs with
    | nil =>
      have hne : coarse b.first ≠ coarse closing := boundary.1
      intro heq
      exact hne (hlast.symm.trans (congrArg coarse heq))
    | cons c cs =>
      have hne : coarse b.first ≠ coarse c.first := boundary.1
      intro heq
      exact hne (hlast.symm.trans (congrArg coarse heq))

omit [LinearOrder α] [LinearOrder C] in
theorem adjacent_append_singleton (coarse : α → C) (blocks : List (Block α)) (last : Block α) :
    AdjacentDistinct coarse (blocks ++ [last]) ↔
      DistinctBoundaries (coarse last.first) (blocks.map (Block.coarseSingleton coarse)) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => simp [AdjacentDistinct, DistinctBoundaries, Block.coarseSingleton, Block.last]
    | cons c cs =>
      change (coarse b.first ≠ coarse c.first ∧ AdjacentDistinct coarse ((c :: cs) ++ [last])) ↔ _
      rw [ih]
      rfl

omit [LinearOrder α] [LinearOrder C] in
theorem adjacent_init (coarse : α → C) (blocks : List (Block α)) (last : Block α)
    (h : AdjacentDistinct coarse (blocks ++ [last])) : AdjacentDistinct coarse blocks := by
  induction blocks with
  | nil => trivial
  | cons b bs ih =>
    cases bs with
    | nil => trivial
    | cons c cs => exact ⟨h.1, ih h.2⟩

omit [LinearOrder α] [LinearOrder C] in
/-- The standard cyclic wrap repair: if the first and last coarse runs have the
same name, merge them and change the origin. The repaired boundaries are proved
distinct directly from the original maximal-run boundaries. -/
theorem merge_ends_boundaries (coarse : α → C) (a b : Block α) (middle : List (Block α))
    (separated : AdjacentDistinct coarse (a :: (middle ++ [b])))
    (same : coarse b.first = coarse a.first) :
    DistinctBoundaries (coarse (b.append a).first)
      (((b.append a) :: middle).map (Block.coarseSingleton coarse)) := by
  cases middle with
  | nil => exact False.elim (separated.1 same.symm)
  | cons c cs =>
    have hfirst : coarse b.first ≠ coarse c.first := by simpa [same] using separated.1
    have htail := (adjacent_append_singleton coarse (c :: cs) b).mp separated.2
    exact ⟨hfirst, htail⟩

theorem append_micro_contains_right (a b : Block α) : b.micro.Sublist (a.append b).micro := by
  have h : (a.append b).micro =
      a.micro ++ edgeDirection a.last b.first ++ b.micro := by
    exact directions_join a.first b.first a.rest b.rest
  rw [h]
  exact List.sublist_append_right _ _

theorem append_nontrivial_right (a b : Block α) :
    (if b.micro = [] then 0 else 1) ≤ (if (a.append b).micro = [] then 0 else 1) := by
  have h := append_micro_contains_right a b
  by_cases hb : b.micro = []
  · simp [hb]
  · have ha : (a.append b).micro ≠ [] := by
      intro he
      rw [he] at h
      exact hb (List.sublist_nil.mp h)
    simp [hb, ha]

/-- The wrap merge retains every completed finite demand; the old final run was
uncompleted, while the merged run contains every micro step of the old first run. -/
theorem demands_merge_ends_le (coarse : α → C) (a b : Block α) (middle : List (Block α))
    (homogeneous : ∀ c ∈ a :: (middle ++ [b]), c.Homogeneous coarse)
    (separated : AdjacentDistinct coarse (a :: (middle ++ [b]))) :
    demands coarse id ((a :: (middle ++ [b])).map Block.word).flatten ≤
      nontrivialRuns ((b.append a) :: middle) := by
  rw [demands_eq_completed_runs coarse _ homogeneous separated]
  have h := append_nontrivial_right b a
  have hd : (a :: (middle ++ [b])).dropLast = a :: middle := by
    change ((a :: middle) ++ [b]).dropLast = a :: middle
    exact List.dropLast_concat
  rw [hd]
  simpa only [nontrivialRuns, List.map_cons, List.sum_cons] using
    Nat.add_le_add_right h (nontrivialRuns middle)

omit [LinearOrder α] [LinearOrder C] in
theorem distinct_boundaries_of_adjacent (coarse : α → C) (closing : C)
    (blocks : List (Block α)) (adjacent : AdjacentDistinct coarse blocks)
    (last_distinct : ∀ b, blocks.getLast? = some b → coarse b.first ≠ closing) :
    DistinctBoundaries closing (blocks.map (Block.coarseSingleton coarse)) := by
  induction blocks with
  | nil => trivial
  | cons b bs ih =>
    cases bs with
    | nil => exact ⟨last_distinct b rfl, trivial⟩
    | cons c cs =>
      refine ⟨adjacent.1, ih adjacent.2 ?_⟩
      intro z hz
      exact last_distinct z (by simpa only [List.getLast?_cons_cons] using hz)

/-- A concrete cyclic run layout obtained by rotating a finite query word. The
rotation is recorded by an actual split, allowing its occurrences to be located
in two consecutive copies of that word. -/
structure CyclicLayout (coarse : α → C) (xs : List α) where
  first : Block α
  rest : List (Block α)
  cutBefore : List α
  suffix : List α
  split : xs = cutBefore ++ suffix
  rotation : ((first :: rest).map Block.word).flatten = suffix ++ cutBefore
  homogeneous : ∀ b ∈ first :: rest, b.Homogeneous coarse
  boundaries : DistinctBoundaries (coarse first.first)
    ((first :: rest).map (Block.coarseSingleton coarse))
  demands_le : demands coarse id xs ≤ nontrivialRuns (first :: rest)

def CoarseConstant (coarse : α → C) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, coarse x = coarse y

theorem demands_of_coarseConstant (coarse : α → C) (xs : List α)
    (constant : CoarseConstant coarse xs) : demands coarse id xs = 0 := by
  cases xs with
  | nil => rfl
  | cons a as =>
    apply rlFrom_transitionsFrom_of_same_coarse coarse id a as false
    intro y hy
    exact constant y (by simp [hy]) a (by simp)

/-- Every actual finite word either stays in one coarse cell, or admits a genuine
cyclic layout. The construction uses maximal coarse runs and merges only the
first/last pair when their names agree. -/
theorem exists_cyclicLayout_or_constant (coarse : α → C) (xs : List α) :
    CoarseConstant coarse xs ∨ Nonempty (CyclicLayout coarse xs) := by
  have hflat := coarseRuns_flatten coarse xs
  have hhom := coarseRuns_homogeneous coarse xs
  have hadj := coarseRuns_adjacent coarse xs
  cases hr : coarseRuns coarse xs with
  | nil =>
    have hx : xs = [] := by simpa [hr] using hflat.symm
    left
    simp [CoarseConstant, hx]
  | cons a rest =>
    rw [hr] at hflat hhom hadj
    cases rest with
    | nil =>
      left
      have hh := hhom a (by simp)
      have hx : xs = a.word := by simpa using hflat.symm
      intro x hxm y hym
      rw [hx] at hxm hym
      exact (hh x hxm).trans (hh y hym).symm
    | cons c cs =>
      obtain hempty | ⟨middle, b, hlast⟩ := List.eq_nil_or_concat' (c :: cs)
      · simp at hempty
      · have hflat' : ((a :: (middle ++ [b])).map Block.word).flatten = xs := by
          simpa only [hlast] using hflat
        have hhom' : ∀ z ∈ a :: (middle ++ [b]), z.Homogeneous coarse := by
          simpa only [hlast] using hhom
        have hadj' : AdjacentDistinct coarse (a :: (middle ++ [b])) := by
          simpa only [hlast] using hadj
        by_cases same : coarse b.first = coarse a.first
        · right
          refine ⟨{
            first := b.append a
            rest := middle
            cutBefore := a.word ++ (middle.map Block.word).flatten
            suffix := b.word
            split := ?_
            rotation := ?_
            homogeneous := ?_
            boundaries := merge_ends_boundaries coarse a b middle hadj' same
            demands_le := ?_ }⟩
          · simpa [List.map_append, List.flatten_append, List.append_assoc] using hflat'.symm
          · simp [Block.word_append, List.append_assoc]
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact Block.homogeneous_append coarse b a
                (hhom' b (by simp)) (hhom' a (by simp)) same
            · exact hhom' z (by simp [hz])
          · rw [← hflat']
            exact demands_merge_ends_le coarse a b middle hhom' hadj'
        · right
          have hboundary : DistinctBoundaries (coarse a.first)
              ((a :: (middle ++ [b])).map (Block.coarseSingleton coarse)) := by
            apply distinct_boundaries_of_adjacent coarse (coarse a.first) _ hadj'
            intro z hz
            have hz' : b = z := by
              change ((a :: middle) ++ [b]).getLast? = some z at hz
              rw [List.getLast?_append] at hz
              simpa only [List.getLast?_singleton, Option.some_or, Option.some.injEq] using hz
            simpa only [← hz'] using same
          refine ⟨{
            first := a
            rest := middle ++ [b]
            cutBefore := []
            suffix := xs
            split := rfl
            rotation := by simpa using hflat'
            homogeneous := hhom'
            boundaries := hboundary
            demands_le := ?_ }⟩
          rw [← hflat']
          exact demands_blocks_le_nontrivial coarse a (middle ++ [b]) hhom' hboundary

theorem exists_cyclicLayout (coarse : α → C) (xs : List α) :
    demands coarse id xs = 0 ∨ Nonempty (CyclicLayout coarse xs) := by
  rcases exists_cyclicLayout_or_constant coarse xs with h | h
  · exact Or.inl (demands_of_coarseConstant coarse xs h)
  · exact Or.inr h

omit [LinearOrder α] in
theorem directionsFrom_homogeneous_map (coarse : α → C) (a : α) (xs : List α)
    (same : ∀ x ∈ xs, coarse x = coarse a) :
    directionsFrom (coarse a) (xs.map coarse) = [] := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hx := same x (by simp)
    have htail := ih x (fun z hz => (same z (by simp [hz])).trans hx.symm)
    simp only [List.map_cons, directionsFrom, hx, edgeDirection_self, List.nil_append]
    simpa only [hx] using htail

omit [LinearOrder α] in
theorem directionsFrom_block_map (coarse : α → C) (incoming : C) (b : Block α)
    (homogeneous : b.Homogeneous coarse) :
    directionsFrom incoming (b.word.map coarse) = edgeDirection incoming (coarse b.first) := by
  have h := directionsFrom_homogeneous_map coarse b.first b.rest
    (fun x hx => homogeneous x (by simp [Block.word, hx]))
  simp only [Block.word, List.map_cons, directionsFrom, h, List.append_nil]

omit [LinearOrder α] [LinearOrder C] in
theorem lastD_block_map (coarse : α → C) (fallback : C) (b : Block α)
    (homogeneous : b.Homogeneous coarse) :
    (b.word.map coarse).getLastD fallback = coarse b.first := by
  simp only [Block.word, List.map_cons, List.getLastD_cons, List.getLastD_map]
  exact Block.homogeneous_last coarse b homogeneous

omit [LinearOrder α] in
theorem directionsFrom_blocks_coarse (coarse : α → C) (incoming : C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse) :
    directionsFrom incoming ((blocks.map Block.word).flatten.map coarse) =
      directionsFrom incoming (blocks.map (fun b => coarse b.first)) := by
  induction blocks generalizing incoming with
  | nil => rfl
  | cons b bs ih =>
    have hb := homogeneous b (by simp)
    have hbs : ∀ z ∈ bs, z.Homogeneous coarse := fun z hz => homogeneous z (by simp [hz])
    simp only [List.map_cons, List.flatten_cons, List.map_append, directionsFrom_append]
    rw [directionsFrom_block_map coarse incoming b hb, lastD_block_map coarse incoming b hb,
      ih (coarse b.first) hbs]
    rfl

omit [LinearOrder α] [LinearOrder C] in
theorem lastD_blocks_coarse (coarse : α → C) (fallback : C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse) :
    ((blocks.map Block.word).flatten.map coarse).getLastD fallback =
      (blocks.map (fun b => coarse b.first)).getLastD fallback := by
  induction blocks generalizing fallback with
  | nil => rfl
  | cons b bs ih =>
    have hb := homogeneous b (by simp)
    have hbs : ∀ z ∈ bs, z.Homogeneous coarse := fun z hz => homogeneous z (by simp [hz])
    simp only [List.map_cons, List.flatten_cons, List.map_append, lastD_append,
      List.getLastD_cons]
    rw [lastD_block_map coarse fallback b hb]
    exact ih (coarse b.first) hbs

omit [LinearOrder α] in
/-- Removing repeated coarse labels within each run preserves the entire cyclic
direction word, and therefore its turns. This links the compressed macro word
to the uncompressed projection used by the concrete fragment hierarchy. -/
theorem cyclicDirections_blocks_coarse (coarse : α → C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse) :
    cyclicDirections ((blocks.map Block.word).flatten.map coarse) =
      cyclicDirections (blocks.map (fun b => coarse b.first)) := by
  cases blocks with
  | nil => rfl
  | cons b bs =>
    rw [cyclicDirections_eq_from (coarse b.first), cyclicDirections_eq_from (coarse b.first)]
    rw [lastD_blocks_coarse coarse (coarse b.first) (b :: bs) homogeneous]
    exact directionsFrom_blocks_coarse coarse _ (b :: bs) homogeneous

omit [LinearOrder α] in
theorem wordTurns_blocks_coarse (coarse : α → C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse) :
    wordTurns ((blocks.map Block.word).flatten.map coarse) =
      wordTurns (blocks.map (fun b => coarse b.first)) :=
  congrArg TurnAccounting.cyclicTurns (cyclicDirections_blocks_coarse coarse blocks homogeneous)

end ChaCha.CyclicRuns
