import Splay.Lazy.CanonicalInitializationTrace

namespace Splay.Accounting

open Splay.Lazy

/-- Reversing both lists preserves contiguous segments. -/
theorem _root_.Splay.Lazy.IsSegment.reverse {α : Type*}
    {inside whole : List α} (segment : IsSegment inside whole) :
    IsSegment inside.reverse whole.reverse := by
  obtain ⟨front, back, decomposition⟩ := segment
  refine ⟨back.reverse, front.reverse, ?_⟩
  rw [decomposition]
  simp only [List.reverse_append]
  simp only [List.append_assoc]

/-- Adjacency inside a contiguous segment is adjacency in the ambient list. -/
theorem _root_.Splay.Interface.Adjacent.of_isSegment {alpha : Type*}
    {inside whole : List alpha} {first second : alpha}
    (adjacent : Interface.Adjacent inside first second)
    (segment : IsSegment inside whole) :
    Interface.Adjacent whole first second := by
  obtain ⟨insideFront, insideBack, direct | reverse⟩ := adjacent
  · obtain ⟨wholeFront, wholeBack, rfl⟩ := segment
    refine ⟨wholeFront ++ insideFront, insideBack ++ wholeBack, Or.inl ?_⟩
    rw [direct]
    simp [List.append_assoc]
  · obtain ⟨wholeFront, wholeBack, rfl⟩ := segment
    refine ⟨wholeFront ++ insideFront, insideBack ++ wholeBack, Or.inr ?_⟩
    rw [reverse]
    simp [List.append_assoc]

/-- Reversing the ambient order preserves undirected adjacency. -/
theorem _root_.Splay.Interface.Adjacent.reverse {alpha : Type*}
    {elements : List alpha} {first second : alpha}
    (adjacent : Interface.Adjacent elements first second) :
    Interface.Adjacent elements.reverse first second := by
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · refine ⟨back.reverse, front.reverse, Or.inr ?_⟩
    rw [direct, List.reverse_append]
    simp [List.append_assoc]
  · refine ⟨back.reverse, front.reverse, Or.inl ?_⟩
    rw [reverse, List.reverse_append]
    simp [List.append_assoc]

/-- Adjacent entries of a duplicate-free list are distinct. -/
theorem _root_.Splay.Interface.Adjacent.ne_of_nodup {alpha : Type*}
    {elements : List alpha} {first second : alpha}
    (adjacent : Interface.Adjacent elements first second)
    (nodup : elements.Nodup) : first ≠ second := by
  intro equal
  subst second
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · rw [direct] at nodup
    have tailNodup := (List.nodup_append.mp nodup).2.1
    exact (List.nodup_cons.mp tailNodup).1 (by simp)
  · rw [reverse] at nodup
    have tailNodup := (List.nodup_append.mp nodup).2.1
    exact (List.nodup_cons.mp tailNodup).1 (by simp)

/-- Erasing an unrelated element cannot destroy an adjacent pair. -/
theorem _root_.Splay.Interface.Adjacent.erase_of_ne
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {elements : List alpha} {first second removed : alpha}
    (adjacent : Interface.Adjacent elements first second)
    (removedFirst : removed ≠ first) (removedSecond : removed ≠ second) :
    Interface.Adjacent (elements.erase removed) first second := by
  have firstRemoved : first ≠ removed := removedFirst.symm
  have secondRemoved : second ≠ removed := removedSecond.symm
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · by_cases inFront : removed ∈ front
    · refine ⟨front.erase removed, back, Or.inl ?_⟩
      rw [direct, List.erase_append_left _ inFront]
    · refine ⟨front, back.erase removed, Or.inl ?_⟩
      rw [direct, List.erase_append_right _ inFront]
      simp [firstRemoved, secondRemoved]
  · by_cases inFront : removed ∈ front
    · refine ⟨front.erase removed, back, Or.inr ?_⟩
      rw [reverse, List.erase_append_left _ inFront]
    · refine ⟨front, back.erase removed, Or.inr ?_⟩
      rw [reverse, List.erase_append_right _ inFront]
      simp [firstRemoved, secondRemoved]

/-- Repeatedly erasing elements distinct from both endpoints preserves
adjacency. -/
theorem _root_.Splay.Interface.Adjacent.foldl_erase_of_fresh
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {elements removals : List alpha} {first second : alpha}
    (adjacent : Interface.Adjacent elements first second)
    (fresh : ∀ removed ∈ removals,
      removed ≠ first ∧ removed ≠ second) :
    Interface.Adjacent (removals.foldl List.erase elements) first second := by
  induction removals generalizing elements with
  | nil => simpa using adjacent
  | cons head tail ih =>
      simp only [List.foldl_cons]
      apply ih (adjacent.erase_of_ne (fresh head (by simp)).1
        (fresh head (by simp)).2)
      intro removed member
      exact fresh removed (by simp [member])

/-- Erasing one occurrence of each of two values commutes. -/
theorem _root_.List.erase_comm_of_lawful
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    (elements : List alpha) (first second : alpha) :
    (elements.erase first).erase second =
      (elements.erase second).erase first := by
  induction elements with
  | nil => simp
  | cons head tail ih =>
      by_cases headFirst : head = first
      · subst first
        by_cases headSecond : head = second
        · subst second
          rfl
        · simp [headSecond]
      · by_cases headSecond : head = second
        · subst second
          simp [headFirst]
        · simp [headFirst, headSecond, ih]

/--
If one distinguished removal creates an adjacent pair, then a batch
containing that removal preserves the pair provided every removed element
is different from both endpoints.  The distinguished removal may occur
anywhere in the batch.
-/
theorem _root_.Splay.Interface.Adjacent.foldl_erase_of_mem
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {elements removals : List alpha} {distinguished first second : alpha}
    (adjacent :
      Interface.Adjacent (elements.erase distinguished) first second)
    (distinguishedMember : distinguished ∈ removals)
    (fresh : ∀ removed ∈ removals,
      removed ≠ first ∧ removed ≠ second) :
    Interface.Adjacent (removals.foldl List.erase elements) first second := by
  induction removals generalizing elements with
  | nil => simp at distinguishedMember
  | cons head tail ih =>
      simp only [List.foldl_cons]
      by_cases headEq : head = distinguished
      · subst head
        apply adjacent.foldl_erase_of_fresh
        intro removed member
        exact fresh removed (by simp [member])
      · have distinguishedTail : distinguished ∈ tail := by
          rcases List.mem_cons.mp distinguishedMember with equal | member
          · exact (headEq equal.symm).elim
          · exact member
        apply ih (elements := elements.erase head)
        · rw [List.erase_comm_of_lawful]
          exact adjacent.erase_of_ne
            (fresh head (by simp)).1 (fresh head (by simp)).2
        · exact distinguishedTail
        · intro removed member
          exact fresh removed (List.mem_cons_of_mem head member)

/-- Erasing an element of a segment preserves the segment when the ambient
list has no duplicate occurrence that could be erased first. -/
theorem _root_.Splay.Lazy.IsSegment.erase
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {inside whole : List alpha} {element : alpha}
    (segment : IsSegment inside whole) (wholeNodup : whole.Nodup)
    (member : element ∈ inside) :
    IsSegment (inside.erase element) (whole.erase element) := by
  obtain ⟨front, back, decomposition⟩ := segment
  have normalized : (front ++ (inside ++ back)).Nodup := by
    rw [decomposition] at wholeNodup
    simpa only [List.append_assoc] using wholeNodup
  have notFront : element ∉ front := by
    intro frontMember
    have disjoint := (List.nodup_append.mp normalized).2.2
    exact disjoint element frontMember element (by simp [member]) rfl
  refine ⟨front, back, ?_⟩
  rw [decomposition]
  rw [show front ++ inside ++ back = front ++ (inside ++ back) by
    simp [List.append_assoc]]
  rw [List.erase_append_right (inside ++ back) notFront]
  rw [List.erase_append_left back member]
  simp [List.append_assoc]

/-- Erasing a duplicate-free family contained in a segment, in order,
preserves the segment relation against the same erasures of the ambient
list. -/
theorem _root_.Splay.Lazy.IsSegment.foldl_erase
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {inside whole : List alpha}
    (segment : IsSegment inside whole) (wholeNodup : whole.Nodup)
    (removed : List alpha) (removedNodup : removed.Nodup)
    (removedInside : ∀ element ∈ removed, element ∈ inside) :
    IsSegment (removed.foldl List.erase inside)
      (removed.foldl List.erase whole) := by
  induction removed generalizing inside whole with
  | nil => simpa using segment
  | cons head tail ih =>
      have nodupFacts := List.nodup_cons.mp removedNodup
      have headInside := removedInside head (by simp)
      have erasedSegment := segment.erase wholeNodup headInside
      have tailInside : ∀ element ∈ tail,
          element ∈ inside.erase head := by
        intro element elementMember
        have different : element ≠ head := by
          intro equal
          subst element
          exact nodupFacts.1 elementMember
        simpa [different] using
          removedInside element (by simp [elementMember])
      simpa using ih erasedSegment (wholeNodup.erase head)
        nodupFacts.2 tailInside

/-- Removing an element outside a segment from the ambient list leaves the
segment itself consecutive. -/
theorem _root_.Splay.Lazy.IsSegment.erase_ambient_of_not_mem
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {inside whole : List alpha} {element : alpha}
    (segment : IsSegment inside whole) (outside : element ∉ inside) :
    IsSegment inside (whole.erase element) := by
  obtain ⟨front, back, decomposition⟩ := segment
  by_cases inFront : element ∈ front
  · refine ⟨front.erase element, back, ?_⟩
    rw [decomposition]
    rw [show front ++ inside ++ back = front ++ (inside ++ back) by
      simp [List.append_assoc]]
    rw [List.erase_append_left (inside ++ back) inFront]
    simp [List.append_assoc]
  · refine ⟨front, back.erase element, ?_⟩
    rw [decomposition]
    rw [show front ++ inside ++ back = front ++ (inside ++ back) by
      simp [List.append_assoc]]
    rw [List.erase_append_right (inside ++ back) inFront]
    rw [List.erase_append_right back outside]
    simp [List.append_assoc]

/-- Repeatedly removing elements outside a segment from the ambient list
cannot split the segment. -/
theorem _root_.Splay.Lazy.IsSegment.foldl_erase_ambient_of_fresh
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {inside whole removed : List alpha}
    (segment : IsSegment inside whole)
    (fresh : ∀ element ∈ removed, element ∉ inside) :
    IsSegment inside (removed.foldl List.erase whole) := by
  induction removed generalizing whole with
  | nil => simpa using segment
  | cons head tail ih =>
      apply ih (segment.erase_ambient_of_not_mem (fresh head (by simp)))
      intro element member
      exact fresh element (by simp [member])

/-- Repeatedly erasing elements fresh for a prefix changes only the suffix. -/
theorem _root_.List.foldl_erase_append_of_fresh
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    (removed fixedPrefix suffix : List alpha)
    (fresh : ∀ element ∈ removed, element ∉ fixedPrefix) :
    removed.foldl List.erase (fixedPrefix ++ suffix) =
      fixedPrefix ++ removed.foldl List.erase suffix := by
  induction removed generalizing suffix with
  | nil => rfl
  | cons head tail ih =>
      rw [show (head :: tail).foldl List.erase (fixedPrefix ++ suffix) =
        tail.foldl List.erase ((fixedPrefix ++ suffix).erase head) by rfl]
      rw [List.erase_append_right suffix (fresh head (by simp))]
      have tailFresh : ∀ element ∈ tail, element ∉ fixedPrefix := by
        intro element member
        exact fresh element (by simp [member])
      rw [ih (suffix.erase head) tailFresh]
      rfl

/-- Prefixing the ambient list preserves an existing segment. -/
theorem _root_.Splay.Lazy.IsSegment.cons_ambient
    {alpha : Type*} {inside whole : List alpha} (head : alpha)
    (segment : IsSegment inside whole) :
    IsSegment inside (head :: whole) := by
  obtain ⟨front, back, decomposition⟩ := segment
  exact ⟨head :: front, back, by simp [decomposition]⟩

/-- Prefixing both lists preserves a prefix segment. -/
theorem _root_.Splay.Lazy.IsSegment.cons_of_eq_append
    {alpha : Type*} {inside whole back : List alpha} (head : alpha)
    (decomposition : whole = inside ++ back) :
    IsSegment (head :: inside) (head :: whole) := by
  exact ⟨[], back, by simp [decomposition]⟩

/-- Membership after ordered erasures from a duplicate-free list is set
difference by the erased family. -/
theorem _root_.List.mem_foldl_erase_iff
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {element : alpha} {whole removed : List alpha}
    (wholeNodup : whole.Nodup) :
    element ∈ removed.foldl List.erase whole ↔
      element ∈ whole ∧ element ∉ removed := by
  induction removed generalizing whole with
  | nil => simp
  | cons head tail ih =>
      rw [show (head :: tail).foldl List.erase whole =
        tail.foldl List.erase (whole.erase head) by rfl]
      rw [ih (wholeNodup.erase head)]
      rw [wholeNodup.mem_erase_iff]
      simp [and_assoc, and_left_comm, and_comm]

/-- Repeated erasure preserves every pairwise ordering relation. -/
theorem _root_.List.Pairwise.foldl_erase
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {relation : alpha → alpha → Prop} {whole : List alpha}
    (ordered : whole.Pairwise relation) (removed : List alpha) :
    (removed.foldl List.erase whole).Pairwise relation := by
  induction removed generalizing whole with
  | nil => exact ordered
  | cons head tail ih =>
      exact ih (ordered.erase head)

/-- In a duplicate-free list, erasing one element commutes with reversal. -/
theorem _root_.List.reverse_erase_of_nodup
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {elements : List alpha} {element : alpha}
    (nodup : elements.Nodup) (member : element ∈ elements) :
    (elements.erase element).reverse = elements.reverse.erase element := by
  induction elements with
  | nil => simp at member
  | cons head tail ih =>
      have facts := List.nodup_cons.mp nodup
      by_cases equal : element = head
      · subst head
        have notReverse : element ∉ tail.reverse := by simpa using facts.1
        simp [notReverse, List.erase_append_right]
      · have tailMember : element ∈ tail := by simpa [equal] using member
        have reverseMember : element ∈ tail.reverse := by simpa using tailMember
        have headNe : head ≠ element := by exact fun h => equal h.symm
        have eraseEq : (head :: tail).erase element =
            head :: tail.erase element := by simp [headNe]
        rw [eraseEq]
        rw [List.reverse_cons]
        rw [List.reverse_cons]
        rw [List.erase_append_left [head] reverseMember]
        rw [ih facts.2 tailMember]

/--
`middle` occurs strictly between `first` and `last` in one directed list
order.  The manuscript's full top-down order uses the symmetric closure of
this relation; keeping the directed version here makes the list argument
independent of the splay geometry.
-/
def ListBetween {α : Type*} (whole : List α)
    (first middle last : α) : Prop :=
  ∃ front between back,
    whole = front ++ first :: between ++ last :: back ∧
      middle ∈ between

/-- One element occurs strictly before another in a list. -/
def ListBefore {α : Type*} (whole : List α) (first last : α) : Prop :=
  ∃ front between back,
    whole = front ++ first :: between ++ last :: back

namespace ListBefore

/-- A pairwise relation holds between two elements occurring in list order. -/
theorem rel_of_pairwise {α : Type*} {R : α → α → Prop}
    {whole : List α} {first last : α}
    (pairwise : whole.Pairwise R)
    (before : ListBefore whole first last) :
    R first last := by
  obtain ⟨front, between, back, decomposition⟩ := before
  rw [decomposition] at pairwise
  have across := (List.pairwise_append.mp pairwise).2.2
  exact across first (by simp) last (by simp)

/-- Strict list order is strict numerical `idxOf` order in a nodup list. -/
theorem idxOf_lt {α : Type*} [BEq α] [LawfulBEq α]
    {whole : List α} {first last : α}
    (nodup : whole.Nodup)
    (before : ListBefore whole first last) :
    whole.idxOf first < whole.idxOf last := by
  obtain ⟨front, between, back, decomposition⟩ := before
  have normalized :
      (front ++ first :: between ++ last :: back).Nodup := by
    simpa only [decomposition] using nodup
  have frontFacts := List.nodup_append.mp
    (show (front ++ (first :: between ++ last :: back)).Nodup by
      simpa only [List.append_assoc] using normalized)
  have facts := List.nodup_append.mp normalized
  have firstFresh : first ∉ front := by
    intro member
    exact frontFacts.2.2 first member first (by simp) rfl
  have lastFresh : last ∉ front := by
    intro member
    exact frontFacts.2.2 last member last (by simp) rfl
  have firstNeLast : first ≠ last := by
    intro equal
    subst last
    exact facts.2.2 first (by simp) first (by simp) rfl
  have lastNotBetween : last ∉ between := by
    have tailNodup := frontFacts.2.1
    have firstTail := (List.nodup_cons.mp tailNodup).2
    have betweenFacts := List.nodup_append.mp firstTail
    intro member
    exact betweenFacts.2.2 last member last (by simp) rfl
  rw [decomposition]
  simp only [List.append_assoc]
  rw [List.idxOf_append_of_notMem firstFresh,
    List.idxOf_append_of_notMem lastFresh]
  simp [List.idxOf_append_of_notMem lastNotBetween, firstNeLast]

/-- Strict list order is asymmetric in a duplicate-free list. -/
theorem asymm {α : Type*} [BEq α] [LawfulBEq α]
    {whole : List α} {first last : α}
    (nodup : whole.Nodup)
    (before : ListBefore whole first last) :
    ¬ ListBefore whole last first := by
  intro reverse
  have forwardLt := before.idxOf_lt nodup
  have reverseLt := reverse.idxOf_lt nodup
  omega

end ListBefore

namespace ListBetween

/-- Adding a prefix does not change which old elements lie between two others. -/
theorem prepend {α : Type*} {whole : List α}
    {first middle last : α}
    (between : ListBetween whole first middle last)
    (prefixList : List α) :
    ListBetween (prefixList ++ whole) first middle last := by
  obtain ⟨front, inside, back, decomposition, member⟩ := between
  refine ⟨prefixList ++ front, inside, back, ?_, member⟩
  rw [decomposition]
  simp only [List.append_assoc]

/-- The element between the endpoints is an ambient-list member. -/
theorem middle_mem {α : Type*} {whole : List α}
    {first middle last : α}
    (between : ListBetween whole first middle last) :
    middle ∈ whole := by
  obtain ⟨front, inside, back, decomposition, member⟩ := between
  rw [decomposition]
  simp [member]

/-- The first endpoint occurs before the selected middle element. -/
theorem first_before_middle {α : Type*} {whole : List α}
    {first middle last : α}
    (between : ListBetween whole first middle last) :
    ListBefore whole first middle := by
  obtain ⟨front, inside, back, decomposition, member⟩ := between
  obtain ⟨beforeMiddle, afterMiddle, insideEq⟩ :=
    List.mem_iff_append.mp member
  refine ⟨front, beforeMiddle, afterMiddle ++ last :: back, ?_⟩
  rw [decomposition, insideEq]
  simp only [List.append_assoc, List.cons_append]

/-- The selected middle element occurs before the last endpoint. -/
theorem middle_before_last {α : Type*} {whole : List α}
    {first middle last : α}
    (between : ListBetween whole first middle last) :
    ListBefore whole middle last := by
  obtain ⟨front, inside, back, decomposition, member⟩ := between
  obtain ⟨beforeMiddle, afterMiddle, insideEq⟩ :=
    List.mem_iff_append.mp member
  refine ⟨front ++ first :: beforeMiddle, afterMiddle, back, ?_⟩
  rw [decomposition, insideEq]
  simp only [List.append_assoc, List.cons_append]

/-- Filtering preserves a between-relation when all three named elements pass. -/
theorem filter {α : Type*} {whole : List α}
    {first middle last : α} {predicate : α → Bool}
    (between : ListBetween whole first middle last)
    (firstPasses : predicate first = true)
    (middlePasses : predicate middle = true)
    (lastPasses : predicate last = true) :
    ListBetween (whole.filter predicate) first middle last := by
  obtain ⟨front, inside, back, decomposition, member⟩ := between
  refine
    ⟨front.filter predicate, inside.filter predicate,
      back.filter predicate, ?_, ?_⟩
  · rw [decomposition]
    simp [List.filter_append, firstPasses, lastPasses,
      List.append_assoc]
  · exact List.mem_filter.mpr ⟨member, middlePasses⟩

end ListBetween

/--
A selected sublist is convex in an ambient order when it contains every
ambient element lying between two selected elements.
-/
def ListConvex {α : Type*} (inside whole : List α) : Prop :=
  ∀ first middle last,
    first ∈ inside →
      last ∈ inside →
        ListBetween whole first middle last →
          middle ∈ inside

namespace ListConvex

/-- Convexity restricts from a cons list to its tail. -/
theorem tail {α : Type*} {inside whole : List α} {head : α}
    (convex : ListConvex inside (head :: whole)) :
    ListConvex inside whole := by
  intro first middle last firstMember lastMember between
  apply convex first middle last firstMember lastMember
  simpa only [List.singleton_append] using
    between.prepend [head]

/-- Convexity of a selected cons list restricts to both tails. -/
theorem cons_tail {α : Type*} {inside whole : List α} {head : α}
    (convex : ListConvex (head :: inside) (head :: whole))
    (nodup : (head :: whole).Nodup) :
    ListConvex inside whole := by
  intro first middle last firstMember lastMember between
  have selected := convex first middle last
    (by simp [firstMember]) (by simp [lastMember])
    (by
      simpa only [List.singleton_append] using
        between.prepend [head])
  rcases List.mem_cons.mp selected with middleEq | middleMember
  · subst middle
    exact ((List.nodup_cons.mp nodup).1 between.middle_mem).elim
  · exact middleMember

end ListConvex

/-- Every actual contiguous segment is convex in a duplicate-free list. -/
theorem listConvex_of_isSegment
    {α : Type*} [BEq α] [LawfulBEq α]
    {inside whole : List α}
    (segment : IsSegment inside whole)
    (wholeNodup : whole.Nodup) :
    ListConvex inside whole := by
  obtain ⟨front, back, decomposition⟩ := segment
  intro first middle last firstMember lastMember between
  have middleMember := between.middle_mem
  rw [decomposition] at middleMember
  simp only [List.mem_append] at middleMember
  rcases middleMember with (middleFront | middleInside) | middleBack
  · obtain ⟨frontBefore, frontAfter, frontEq⟩ :=
      List.mem_iff_append.mp middleFront
    obtain ⟨insideBefore, insideAfter, insideEq⟩ :=
      List.mem_iff_append.mp firstMember
    have reverse : ListBefore whole middle first := by
      refine
        ⟨frontBefore,
          frontAfter ++ insideBefore,
          insideAfter ++ back, ?_⟩
      rw [decomposition, frontEq, insideEq]
      simp only [List.append_assoc, List.cons_append]
    exact
      ((between.first_before_middle.asymm wholeNodup) reverse).elim
  · exact middleInside
  · obtain ⟨insideBefore, insideAfter, insideEq⟩ :=
      List.mem_iff_append.mp lastMember
    obtain ⟨backBefore, backAfter, backEq⟩ :=
      List.mem_iff_append.mp middleBack
    have reverse : ListBefore whole last middle := by
      refine
        ⟨front ++ insideBefore,
          insideAfter ++ backBefore,
          backAfter, ?_⟩
      rw [decomposition, insideEq, backEq]
      simp only [List.append_assoc, List.cons_append]
    exact
      ((between.middle_before_last.asymm wholeNodup) reverse).elim

/--
Order-theoretic segment bridge.

In a duplicate-free ambient order, a convex sublist is a contiguous segment.
This is the abstract combinatorial step used in the manuscript when a lazy
interval that is consecutive on one side and unbroken across the other side
is promoted to an interval in the full interleaved top-down order.
-/
theorem isSegment_of_sublist_of_convex
    {α : Type*} {inside whole : List α}
    (sublist : inside.Sublist whole)
    (wholeNodup : whole.Nodup)
    (convex : ListConvex inside whole) :
    IsSegment inside whole := by
  induction sublist with
  | slnil =>
      exact ⟨[], [], rfl⟩
  | @cons firstList ambientList head sublist ih =>
      have tailNodup := (List.nodup_cons.mp wholeNodup).2
      obtain ⟨front, back, decomposition⟩ :=
        ih tailNodup convex.tail
      exact ⟨head :: front, back, by simp [decomposition]⟩
  | @cons_cons firstList ambientList head sublist ih =>
      cases firstList with
      | nil =>
          exact ⟨[], ambientList, by simp⟩
      | cons first rest =>
          have tailNodup := (List.nodup_cons.mp wholeNodup).2
          obtain ⟨front, back, decomposition⟩ :=
            ih tailNodup (convex.cons_tail wholeNodup)
          cases front with
          | nil =>
              exact ⟨[], back, by simp [decomposition]⟩
          | cons skipped prefixList =>
              have normalizedNodup :
                  (head :: skipped ::
                    (prefixList ++ first :: rest ++ back)).Nodup := by
                rw [decomposition] at wholeNodup
                simpa [List.append_assoc] using wholeNodup
              have skippedNotSelected :
                  skipped ∉ head :: first :: rest := by
                have headFresh :=
                  (List.nodup_cons.mp normalizedNodup).1
                have skippedFresh :=
                  (List.nodup_cons.mp
                    (List.nodup_cons.mp normalizedNodup).2).1
                simp only [List.mem_cons, not_or]
                refine ⟨?_, ?_, ?_⟩
                · exact fun equal => headFresh (by simp [equal])
                · intro equal
                  apply skippedFresh
                  simp [equal]
                · intro selected
                  apply skippedFresh
                  simp [selected]
              have skippedBetween :
                  ListBetween
                    (head :: ambientList) head skipped first := by
                refine ⟨[], skipped :: prefixList, rest ++ back, ?_, by simp⟩
                rw [decomposition]
                simp [List.append_assoc]
              exact (skippedNotSelected
                (convex head skipped first (by simp) (by simp)
                  skippedBetween)).elim

/--
The exact abstract form of the article's side-order/unbroken bridge.

`inside` is consecutive after restricting the full order to one side.  If a
rejected (opposite-side) element never lies between two interval elements,
then the interval is consecutive in the full order itself.
-/
theorem isSegment_of_filter_segment_of_unbroken
    {α : Type*} [BEq α] [LawfulBEq α]
    {inside whole : List α} {predicate : α → Bool}
    (sideSegment : IsSegment inside (whole.filter predicate))
    (wholeNodup : whole.Nodup)
    (unbroken :
      ∀ first ∈ inside, ∀ last ∈ inside, ∀ middle,
        predicate middle = false →
          ListBetween whole first middle last → False) :
    IsSegment inside whole := by
  apply isSegment_of_sublist_of_convex
    ((Splay.Lazy.Canonical.IsSegment.sublist sideSegment).trans
      List.filter_sublist) wholeNodup
  intro first middle last firstMember lastMember between
  have firstFiltered := sideSegment.mem firstMember
  have lastFiltered := sideSegment.mem lastMember
  have firstPasses : predicate first = true :=
    (List.mem_filter.mp firstFiltered).2
  have lastPasses : predicate last = true :=
    (List.mem_filter.mp lastFiltered).2
  cases middlePasses : predicate middle with
  | false =>
      exact
        (unbroken first firstMember last lastMember middle
          middlePasses between).elim
  | true =>
      have filteredBetween :=
        between.filter firstPasses middlePasses lastPasses
      exact
        (listConvex_of_isSegment sideSegment
          (wholeNodup.filter predicate))
          first middle last firstMember lastMember filteredBetween

end Splay.Accounting
