import TangoSquared.BSTExecution

/-!
# Ordinary root-starting pointer executions

A cursor is an actual tree zipper. Moving to a child or parent and rotating the
cursor's root costs one. Serving the cursor key costs one. Marked trees track
the distinct touched nodes; their holes contain untouched actual subtrees.
The conversion to a rooted-hull access must be proved from these operations.
-/

namespace TangoSquared.MTR.Pointer

open Tree

variable {α : Type*}

/-- An ancestor frame; the focus occupies the missing left or right child. -/
inductive Frame (α : Type*) where
  | left (parent : α) (right : Tree α)
  | right (left : Tree α) (parent : α)

/-- Reassemble the actual tree above the cursor. -/
def plug (focus : Tree α) : List (Frame α) → Tree α
  | [] => focus
  | .left a r :: rest => plug (.node focus a r) rest
  | .right l a :: rest => plug (.node l a focus) rest

structure Cursor (α : Type*) where
  focus : Tree α
  ancestors : List (Frame α)

def Cursor.tree (c : Cursor α) : Tree α := plug c.focus c.ancestors

def Cursor.atRoot (t : Tree α) : Cursor α := ⟨t, []⟩

/-- Ordinary pointer operations on actual keys. Rotations retain the cursor at
the promoted root; other cursor conventions differ by at most one adjacent move. -/
inductive Step : Cursor α → Cursor α → Prop
  | left (A B C : Tree α) (x y : α) (rest : List (Frame α)) :
      Step ⟨.node (.node A x B) y C, rest⟩ ⟨.node A x B, .left y C :: rest⟩
  | right (A B C : Tree α) (x y : α) (rest : List (Frame α)) :
      Step ⟨.node A x (.node B y C), rest⟩ ⟨.node B y C, .right A x :: rest⟩
  | upLeft (A B : Tree α) (x : α) (rest : List (Frame α)) :
      Step ⟨A, .left x B :: rest⟩ ⟨.node A x B, rest⟩
  | upRight (A B : Tree α) (x : α) (rest : List (Frame α)) :
      Step ⟨B, .right A x :: rest⟩ ⟨.node A x B, rest⟩
  | rotateRight (A B C : Tree α) (x y : α) (rest : List (Frame α)) :
      Step ⟨.node (.node A x B) y C, rest⟩ ⟨.node A x (.node B y C), rest⟩
  | rotateLeft (A B C : Tree α) (x y : α) (rest : List (Frame α)) :
      Step ⟨.node A x (.node B y C), rest⟩ ⟨.node (.node A x B) y C, rest⟩

/-- A finite pointer trace, retaining the served word and charging both pointer
operations and the visits that serve requests. -/
inductive Trace : Cursor α → List α → Cursor α → Nat → Prop
  | nil (c : Cursor α) : Trace c [] c 0
  | step {c d e : Cursor α} {xs : List α} {cost : Nat}
      (move : Step c d) (rest : Trace d xs e cost) : Trace c xs e (cost + 1)
  | serve {c d : Cursor α} {x : α} {xs : List α} {cost : Nat}
      (at_key : rootKey c.focus = some x) (rest : Trace c xs d cost) :
      Trace c (x :: xs) d (cost + 1)

/-- One root-starting access, with no restriction on the final cursor or tree root. -/
def Access (x : α) (before after : Tree α) (cost : Nat) : Prop :=
  ∃ final : Cursor α, final.tree = after ∧ Trace (Cursor.atRoot before) [x] final cost

/-- A rooted partial tree whose gaps are actual untouched subtrees. -/
inductive MarkedTree (α : Type*) where
  | hole (untouched : Tree α)
  | node (left : MarkedTree α) (key : α) (right : MarkedTree α)

namespace MarkedTree

/-- Forget the visitation marks. -/
def erase : MarkedTree α → Tree α
  | .hole t => t
  | .node l a r => .node l.erase a r.erase

/-- The actual touched skeleton. -/
def skeleton : MarkedTree α → Tree α
  | .hole _ => .empty
  | .node l a r => .node l.skeleton a r.skeleton

/-- Untouched subtrees in inorder gap order. -/
def holes : MarkedTree α → List (Tree α)
  | .hole t => [t]
  | .node l _ r => l.holes ++ r.holes

/-- Initially only the root is visited. -/
def rootMark : Tree α → MarkedTree α
  | .empty => .hole .empty
  | .node l a r => .node (.hole l) a (.hole r)

@[simp] theorem erase_rootMark (t : Tree α) : (rootMark t).erase = t := by
  cases t <;> rfl

theorem rootMark_size_le (t : Tree α) : size (rootMark t).skeleton ≤ 1 := by
  cases t <;> simp [rootMark, skeleton, size]

/-- Every finite binary skeleton has exactly one more gap than touched keys. -/
theorem holes_length (m : MarkedTree α) : m.holes.length = size m.skeleton + 1 := by
  induction m with
  | hole t => rfl
  | node l a r ihl ihr => simp [holes, skeleton, size, ihl, ihr]; omega

/-- Reconstruct a marked tree from its skeleton and its actual inorder holes. -/
theorem graft_skeleton (m : MarkedTree α) (gaps : Nat → Tree α) (start : Nat)
    (hgap : ∀ i (hi : i < m.holes.length), gaps (start + i) = m.holes[i]) :
    graft m.skeleton gaps start = m.erase := by
  induction m generalizing start with
  | hole t =>
    have h := hgap 0 (by simp [holes])
    simpa [holes, skeleton, erase, graft] using h
  | node l a r ihl ihr =>
    have hl : graft l.skeleton gaps start = l.erase := by
      apply ihl
      intro i hi
      have h := hgap i (by simp only [holes, List.length_append]; omega)
      simpa only [holes, List.getElem_append_left hi] using h
    have hr : graft r.skeleton gaps (start + size l.skeleton + 1) = r.erase := by
      apply ihr
      intro i hi
      have hg := hgap (l.holes.length + i) (by simp only [holes, List.length_append]; omega)
      have hid : start + (l.holes.length + i) = start + size l.skeleton + 1 + i := by
        rw [holes_length]
        omega
      rw [hid] at hg
      simp only [holes] at hg
      rw [List.getElem_append_right (by omega : l.holes.length ≤ l.holes.length + i)] at hg
      simpa only [Nat.add_sub_cancel_left] using hg
    simp only [skeleton, erase, graft, hl, hr]

/-- The canonical natural-number gap array associated with a marked tree. -/
def gapArray (m : MarkedTree α) (i : Nat) : Tree α := m.holes[i]?.getD .empty

theorem graft_gapArray (m : MarkedTree α) :
    graft m.skeleton m.gapArray 0 = m.erase := by
  apply graft_skeleton
  intro i hi
  simp [gapArray, List.getElem?_eq_getElem hi]

/-- Shared holes and touched-key order give a genuine rooted-hull access. -/
def toHullAccess (source target : MarkedTree α) (x : α)
    (same_holes : source.holes = target.holes)
    (same_keys : inorder source.skeleton = inorder target.skeleton)
    (requested : x ∈ inorder source.skeleton) : HullAccess x source.erase target.erase where
  source := source.skeleton
  target := target.skeleton
  gaps := source.gapArray
  source_tree := source.graft_gapArray
  target_tree := by
    have hg : source.gapArray = target.gapArray := by funext i; simp [gapArray, same_holes]
    rw [hg]
    exact target.graft_gapArray
  same_keys := same_keys
  requested := requested

/-- A tree context whose one missing subtree is at a specified root-to-focus path. -/
inductive Context (α : Type*) where
  | top
  | left (parent : α) (right : MarkedTree α) (inside : Context α)
  | right (left : MarkedTree α) (parent : α) (inside : Context α)

namespace Context

def plug (focus : MarkedTree α) : Context α → MarkedTree α
  | .top => focus
  | .left a r inside => .node (plug focus inside) a r
  | .right l a inside => .node l a (plug focus inside)

def holesBefore : Context α → List (Tree α)
  | .top => []
  | .left _ _ inside => inside.holesBefore
  | .right l _ inside => l.holes ++ inside.holesBefore

def holesAfter : Context α → List (Tree α)
  | .top => []
  | .left _ r inside => inside.holesAfter ++ r.holes
  | .right _ _ inside => inside.holesAfter

def keysBefore : Context α → List α
  | .top => []
  | .left _ _ inside => inside.keysBefore
  | .right l a inside => inorder l.skeleton ++ [a] ++ inside.keysBefore

def keysAfter : Context α → List α
  | .top => []
  | .left a r inside => inside.keysAfter ++ a :: inorder r.skeleton
  | .right _ _ inside => inside.keysAfter

theorem holes_plug (focus : MarkedTree α) (c : Context α) :
    (c.plug focus).holes = c.holesBefore ++ focus.holes ++ c.holesAfter := by
  induction c with
  | top => simp [plug, holesBefore, holesAfter]
  | left a r c ih => simp [plug, holes, holesBefore, holesAfter, ih, List.append_assoc]
  | right l a c ih => simp [plug, holes, holesBefore, holesAfter, ih, List.append_assoc]

theorem keys_plug (focus : MarkedTree α) (c : Context α) :
    inorder (c.plug focus).skeleton = c.keysBefore ++ inorder focus.skeleton ++ c.keysAfter := by
  induction c with
  | top => simp [plug, keysBefore, keysAfter]
  | left a r c ih => simp [plug, skeleton, inorder, keysBefore, keysAfter, ih, List.append_assoc]
  | right l a c ih => simp [plug, skeleton, inorder, keysBefore, keysAfter, ih, List.append_assoc]

/-- The i-th gap sits immediately after the i-th touched inorder key. -/
theorem before_lengths (c : Context α) : c.holesBefore.length = c.keysBefore.length := by
  induction c with
  | top => rfl
  | left a r c ih => exact ih
  | right l a c ih =>
    simp only [holesBefore, keysBefore, List.length_append, List.length_singleton,
      holes_length, length_inorder]
    omega

theorem erase_congr (c : Context α) {m n : MarkedTree α} (h : m.erase = n.erase) :
    (c.plug m).erase = (c.plug n).erase := by
  induction c with
  | top => exact h
  | left a r c ih => simp [plug, erase, ih]
  | right l a c ih => simp [plug, erase, ih]

theorem skeleton_size_plug (c : Context α) (m : MarkedTree α) :
    size (c.plug m).skeleton = c.keysBefore.length + size m.skeleton + c.keysAfter.length := by
  rw [← length_inorder, keys_plug]
  simp [length_inorder, Nat.add_assoc]

end Context

/-- Every inorder gap index identifies a concrete hole context, not an assumed
correspondence between the initial and current tree shapes. -/
theorem hole_context (m : MarkedTree α) (i : Nat) (hi : i < m.holes.length) :
    ∃ (c : Context α) (t : Tree α), m = c.plug (.hole t) ∧
      c.holesBefore.length = i ∧ t = m.holes[i] := by
  induction m generalizing i with
  | hole t =>
    have hi0 : i = 0 := by simp only [holes, List.length_singleton] at hi; omega
    subst i
    exact ⟨.top, t, rfl, rfl, rfl⟩
  | node l a r ihl ihr =>
    by_cases hleft : i < l.holes.length
    · obtain ⟨c, t, hm, hlen, ht⟩ := ihl i hleft
      refine ⟨.left a r c, t, ?_, hlen, ?_⟩
      · simp only [Context.plug, ← hm]
      · simpa only [holes, List.getElem_append_left hleft] using ht
    · have hright : i - l.holes.length < r.holes.length := by
        simp only [holes, List.length_append] at hi
        omega
      obtain ⟨c, t, hm, hlen, ht⟩ := ihr (i - l.holes.length) hright
      refine ⟨.right l a c, t, ?_, ?_, ?_⟩
      · simp only [Context.plug, ← hm]
      · simp only [Context.holesBefore, List.length_append, hlen]
        omega
      · simpa only [holes, List.getElem_append_right (by omega : l.holes.length ≤ i)] using ht

/-- Revealing an untouched node is the only way a visited skeleton grows. -/
inductive Reveal : MarkedTree α → MarkedTree α → Prop
  | root (l r : Tree α) (a : α) :
      Reveal (.hole (.node l a r)) (.node (.hole l) a (.hole r))
  | left {l l' : MarkedTree α} (h : Reveal l l') (a : α) (r : MarkedTree α) :
      Reveal (.node l a r) (.node l' a r)
  | right (l : MarkedTree α) (a : α) {r r' : MarkedTree α} (h : Reveal r r') :
      Reveal (.node l a r) (.node l a r')

/-- A reveal operation has a concrete root-to-hole context. -/
theorem Reveal.context {m n : MarkedTree α} (h : Reveal m n) :
    ∃ (c : Context α) (l r : Tree α) (a : α),
      m = c.plug (.hole (.node l a r)) ∧ n = c.plug (.node (.hole l) a (.hole r)) := by
  induction h with
  | root l r a => exact ⟨.top, l, r, a, rfl, rfl⟩
  | left h a r ih =>
    obtain ⟨c, L, R, b, hm, hn⟩ := ih
    exact ⟨.left a r c, L, R, b, by simp [Context.plug, hm], by simp [Context.plug, hn]⟩
  | right l a h ih =>
    obtain ⟨c, L, R, b, hm, hn⟩ := ih
    exact ⟨.right l a c, L, R, b, by simp [Context.plug, hm], by simp [Context.plug, hn]⟩

theorem Reveal.erase_eq {m n : MarkedTree α} (h : Reveal m n) : m.erase = n.erase := by
  obtain ⟨c, l, r, a, rfl, rfl⟩ := h.context
  exact c.erase_congr rfl

theorem Reveal.size_add_one {m n : MarkedTree α} (h : Reveal m n) :
    size n.skeleton = size m.skeleton + 1 := by
  obtain ⟨c, l, r, a, rfl, rfl⟩ := h.context
  rw [Context.skeleton_size_plug, Context.skeleton_size_plug]
  simp [skeleton, size]
  omega

theorem Context.reveal (c : Context α) {m n : MarkedTree α} (h : Reveal m n) :
    Reveal (c.plug m) (c.plug n) := by
  induction c with
  | top => exact h
  | left a r c ih => exact .left ih a r
  | right l a c ih => exact .right l a ih

/-- Reveal the corresponding actual untouched node in the initial hull.
The correspondence is constructed from the common inorder gap list. -/
theorem pullback_reveal (source current next : MarkedTree α)
    (same_holes : source.holes = current.holes)
    (same_keys : inorder source.skeleton = inorder current.skeleton)
    (revealed : Reveal current next) :
    ∃ source', Reveal source source' ∧ source'.holes = next.holes ∧
      inorder source'.skeleton = inorder next.skeleton := by
  obtain ⟨c, l, r, a, hcurrent, hnext⟩ := revealed.context
  let i := c.holesBefore.length
  have hi : i < source.holes.length := by
    rw [same_holes, hcurrent, Context.holes_plug]
    simp only [holes, List.length_append, List.length_singleton]
    omega
  obtain ⟨d, t, hsource, hlength, ht⟩ := hole_context source i hi
  have hlookup : source.holes[i]? = some (.node l a r) := by
    rw [same_holes, hcurrent, Context.holes_plug]
    simp [i, holes]
  have htnode : t = .node l a r := by
    rw [List.getElem?_eq_getElem hi, ← ht] at hlookup
    exact Option.some.inj hlookup
  rw [htnode] at hsource
  have hh : d.holesBefore ++ Tree.node l a r :: d.holesAfter =
      c.holesBefore ++ Tree.node l a r :: c.holesAfter := by
    simpa only [hsource, hcurrent, Context.holes_plug, holes, List.append_assoc,
      List.singleton_append] using same_holes
  obtain ⟨hbefore, hafter'⟩ := List.append_inj hh hlength
  have hafter := (List.cons.inj hafter').2
  have hk : d.keysBefore ++ d.keysAfter = c.keysBefore ++ c.keysAfter := by
    simpa only [hsource, hcurrent, Context.keys_plug, skeleton, inorder, List.append_nil] using same_keys
  have hklen : d.keysBefore.length = c.keysBefore.length := by
    rw [← Context.before_lengths, ← Context.before_lengths]
    exact hlength
  obtain ⟨hkeysbefore, hkeysafter⟩ := List.append_inj hk hklen
  let source' := d.plug (.node (.hole l) a (.hole r))
  refine ⟨source', ?_, ?_, ?_⟩
  · rw [hsource]
    exact d.reveal (.root l r a)
  · simp only [source', hnext, Context.holes_plug, hbefore, hafter]
  · simp only [source', hnext, Context.keys_plug, hkeysbefore, hkeysafter]

end MarkedTree
/-- Ancestor frames carrying the visited sibling hulls. -/
inductive MarkedFrame (α : Type*) where
  | left (parent : α) (right : MarkedTree α)
  | right (left : MarkedTree α) (parent : α)

namespace MarkedFrame

def erase : MarkedFrame α → Frame α
  | .left a r => .left a r.erase
  | .right l a => .right l.erase a

def plug (focus : MarkedTree α) : List (MarkedFrame α) → MarkedTree α
  | [] => focus
  | .left a r :: rest => plug (.node focus a r) rest
  | .right l a :: rest => plug (.node l a focus) rest

theorem erase_plug (m : MarkedTree α) (frames : List (MarkedFrame α)) :
    (plug m frames).erase = Pointer.plug m.erase (frames.map erase) := by
  induction frames generalizing m with
  | nil => rfl
  | cons f fs ih => cases f <;> simp only [plug, Pointer.plug, List.map_cons, erase, ih, MarkedTree.erase]

theorem reveal_plug {m n : MarkedTree α} (h : MarkedTree.Reveal m n)
    (frames : List (MarkedFrame α)) : MarkedTree.Reveal (plug m frames) (plug n frames) := by
  induction frames generalizing m n with
  | nil => exact h
  | cons f fs ih =>
    cases f with
    | left a r => exact ih (.left h a r)
    | right l a => exact ih (.right l a h)

theorem holes_plug_congr {m n : MarkedTree α} (h : m.holes = n.holes)
    (frames : List (MarkedFrame α)) : (plug m frames).holes = (plug n frames).holes := by
  induction frames generalizing m n with
  | nil => exact h
  | cons f fs ih =>
    cases f with
    | left a r => apply ih; simp [MarkedTree.holes, h]
    | right l a => apply ih; simp [MarkedTree.holes, h]

theorem keys_plug_congr {m n : MarkedTree α} (h : inorder m.skeleton = inorder n.skeleton)
    (frames : List (MarkedFrame α)) :
    inorder (plug m frames).skeleton = inorder (plug n frames).skeleton := by
  induction frames generalizing m n with
  | nil => exact h
  | cons f fs ih =>
    cases f with
    | left a r => apply ih; simp [MarkedTree.skeleton, inorder, h]
    | right l a => apply ih; simp [MarkedTree.skeleton, inorder, h]

end MarkedFrame

/-- A cursor whose current key has already been visited. -/
structure SeenCursor (α : Type*) where
  left : MarkedTree α
  key : α
  right : MarkedTree α
  ancestors : List (MarkedFrame α)

def SeenCursor.focus (c : SeenCursor α) : MarkedTree α := .node c.left c.key c.right

def SeenCursor.tree (c : SeenCursor α) : MarkedTree α := MarkedFrame.plug c.focus c.ancestors

def SeenCursor.erase (c : SeenCursor α) : Cursor α :=
  ⟨c.focus.erase, c.ancestors.map MarkedFrame.erase⟩

theorem SeenCursor.erase_tree (c : SeenCursor α) : c.tree.erase = c.erase.tree :=
  MarkedFrame.erase_plug c.focus c.ancestors

/-- Pointer steps with the deterministic visitation bookkeeping exposed. An
unseen child is marked exactly when first moved to or used in a rotation. -/
inductive SeenStep : SeenCursor α → SeenCursor α → Prop
  | leftSeen (A B C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨.node A x B, y, C, fs⟩ ⟨A, x, B, .left y C :: fs⟩
  | leftNew (A B : Tree α) (C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨.hole (.node A x B), y, C, fs⟩ ⟨.hole A, x, .hole B, .left y C :: fs⟩
  | rightSeen (A B C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨A, x, .node B y C, fs⟩ ⟨B, y, C, .right A x :: fs⟩
  | rightNew (A : MarkedTree α) (B C : Tree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨A, x, .hole (.node B y C), fs⟩ ⟨.hole B, y, .hole C, .right A x :: fs⟩
  | upLeft (A B C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨A, x, B, .left y C :: fs⟩ ⟨.node A x B, y, C, fs⟩
  | upRight (A B C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨B, y, C, .right A x :: fs⟩ ⟨A, x, .node B y C, fs⟩
  | rotateRightSeen (A B C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨.node A x B, y, C, fs⟩ ⟨A, x, .node B y C, fs⟩
  | rotateRightNew (A B : Tree α) (C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨.hole (.node A x B), y, C, fs⟩ ⟨.hole A, x, .node (.hole B) y C, fs⟩
  | rotateLeftSeen (A B C : MarkedTree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨A, x, .node B y C, fs⟩ ⟨.node A x B, y, C, fs⟩
  | rotateLeftNew (A : MarkedTree α) (B C : Tree α) (x y : α) (fs : List (MarkedFrame α)) :
      SeenStep ⟨A, x, .hole (.node B y C), fs⟩ ⟨.node A x (.hole B), y, .hole C, fs⟩

theorem SeenStep.erase {c d : SeenCursor α} (h : SeenStep c d) : Step c.erase d.erase := by
  cases h
  · exact .left _ _ _ _ _ _
  · exact .left _ _ _ _ _ _
  · exact .right _ _ _ _ _ _
  · exact .right _ _ _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _

/-- Every ordinary pointer operation admits the deterministic visited-node
bookkeeping above; no extra operational restriction is imposed. -/
theorem Step.lift {c d : Cursor α} (h : Step c d) (seen : SeenCursor α)
    (heq : seen.erase = c) :
    ∃ next : SeenCursor α, next.erase = d ∧ SeenStep seen next := by
  cases h with
  | left A B C x y rest =>
    rcases seen with ⟨L, k, R, ms⟩
    simp only [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase,
      Cursor.mk.injEq, Tree.node.injEq] at heq
    obtain ⟨⟨hL, hk, hR⟩, hms⟩ := heq
    cases L with
    | hole t =>
      change t = .node A x B at hL
      subst t
      refine ⟨⟨.hole A, x, .hole B, .left k R :: ms⟩, ?_, .leftNew _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, MarkedFrame.erase, hk, hR, hms]
    | node L a M =>
      simp only [MarkedTree.erase, Tree.node.injEq] at hL
      obtain ⟨hA, ha, hB⟩ := hL
      refine ⟨⟨L, a, M, .left k R :: ms⟩, ?_, .leftSeen _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, MarkedFrame.erase,
        hA, ha, hB, hk, hR, hms]
  | right A B C x y rest =>
    rcases seen with ⟨L, k, R, ms⟩
    simp only [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase,
      Cursor.mk.injEq, Tree.node.injEq] at heq
    obtain ⟨⟨hL, hk, hR⟩, hms⟩ := heq
    cases R with
    | hole t =>
      change t = .node B y C at hR
      subst t
      refine ⟨⟨.hole B, y, .hole C, .right L k :: ms⟩, ?_, .rightNew _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, MarkedFrame.erase, hk, hL, hms]
    | node M a R =>
      simp only [MarkedTree.erase, Tree.node.injEq] at hR
      obtain ⟨hB, ha, hC⟩ := hR
      refine ⟨⟨M, a, R, .right L k :: ms⟩, ?_, .rightSeen _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, MarkedFrame.erase,
        hB, ha, hC, hk, hL, hms]
  | upLeft A B x rest =>
    rcases seen with ⟨L, k, R, ms⟩
    simp only [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, Cursor.mk.injEq] at heq
    obtain ⟨hfocus, hms⟩ := heq
    cases ms with
    | nil => simp at hms
    | cons frame ms =>
      cases frame with
      | right S a => simp [MarkedFrame.erase] at hms
      | left a S =>
        simp only [List.map_cons, MarkedFrame.erase, List.cons.injEq, Frame.left.injEq] at hms
        obtain ⟨⟨ha, hS⟩, hms⟩ := hms
        refine ⟨⟨.node L k R, a, S, ms⟩, ?_, .upLeft _ _ _ _ _ _⟩
        simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, hfocus, ha, hS, hms]
  | upRight A B x rest =>
    rcases seen with ⟨L, k, R, ms⟩
    simp only [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, Cursor.mk.injEq] at heq
    obtain ⟨hfocus, hms⟩ := heq
    cases ms with
    | nil => simp at hms
    | cons frame ms =>
      cases frame with
      | left a S => simp [MarkedFrame.erase] at hms
      | right S a =>
        simp only [List.map_cons, MarkedFrame.erase, List.cons.injEq, Frame.right.injEq] at hms
        obtain ⟨⟨hS, ha⟩, hms⟩ := hms
        refine ⟨⟨S, a, .node L k R, ms⟩, ?_, .upRight _ _ _ _ _ _⟩
        simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, hfocus, ha, hS, hms]
  | rotateRight A B C x y rest =>
    rcases seen with ⟨L, k, R, ms⟩
    simp only [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase,
      Cursor.mk.injEq, Tree.node.injEq] at heq
    obtain ⟨⟨hL, hk, hR⟩, hms⟩ := heq
    cases L with
    | hole t =>
      change t = .node A x B at hL
      subst t
      refine ⟨⟨.hole A, x, .node (.hole B) k R, ms⟩, ?_, .rotateRightNew _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, hk, hR, hms]
    | node L a M =>
      simp only [MarkedTree.erase, Tree.node.injEq] at hL
      obtain ⟨hA, ha, hB⟩ := hL
      refine ⟨⟨L, a, .node M k R, ms⟩, ?_, .rotateRightSeen _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, hA, ha, hB, hk, hR, hms]
  | rotateLeft A B C x y rest =>
    rcases seen with ⟨L, k, R, ms⟩
    simp only [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase,
      Cursor.mk.injEq, Tree.node.injEq] at heq
    obtain ⟨⟨hL, hk, hR⟩, hms⟩ := heq
    cases R with
    | hole t =>
      change t = .node B y C at hR
      subst t
      refine ⟨⟨.node L k (.hole B), y, .hole C, ms⟩, ?_, .rotateLeftNew _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, hk, hL, hms]
    | node M a R =>
      simp only [MarkedTree.erase, Tree.node.injEq] at hR
      obtain ⟨hB, ha, hC⟩ := hR
      refine ⟨⟨.node L k M, a, R, ms⟩, ?_, .rotateLeftSeen _ _ _ _ _ _⟩
      simp [SeenCursor.erase, SeenCursor.focus, MarkedTree.erase, hB, ha, hC, hk, hL, hms]

/-- Each pointer primitive reveals at most one new node; all its remaining
changes preserve the touched inorder keys and untouched inorder gaps. -/
theorem SeenStep.expand {c d : SeenCursor α} (h : SeenStep c d) :
    ∃ exposed : MarkedTree α, (c.tree = exposed ∨ MarkedTree.Reveal c.tree exposed) ∧
      exposed.holes = d.tree.holes ∧ inorder exposed.skeleton = inorder d.tree.skeleton := by
  cases h with
  | leftSeen A B C x y fs => exact ⟨_, Or.inl rfl, rfl, rfl⟩
  | leftNew A B C x y fs =>
    refine ⟨_, Or.inr ?_, rfl, rfl⟩
    exact MarkedFrame.reveal_plug (.left (.root A B x) y C) fs
  | rightSeen A B C x y fs => exact ⟨_, Or.inl rfl, rfl, rfl⟩
  | rightNew A B C x y fs =>
    refine ⟨_, Or.inr ?_, rfl, rfl⟩
    exact MarkedFrame.reveal_plug (.right A x (.root B C y)) fs
  | upLeft A B C x y fs => exact ⟨_, Or.inl rfl, rfl, rfl⟩
  | upRight A B C x y fs => exact ⟨_, Or.inl rfl, rfl, rfl⟩
  | rotateRightSeen A B C x y fs =>
    refine ⟨_, Or.inl rfl, ?_, ?_⟩
    · apply MarkedFrame.holes_plug_congr
      simp [SeenCursor.focus, MarkedTree.holes, List.append_assoc]
    · apply MarkedFrame.keys_plug_congr
      simp [SeenCursor.focus, MarkedTree.skeleton, inorder, List.append_assoc]
  | rotateRightNew A B C x y fs =>
    refine ⟨MarkedFrame.plug (.node (.node (.hole A) x (.hole B)) y C) fs,
      Or.inr (MarkedFrame.reveal_plug (.left (.root A B x) y C) fs), ?_, ?_⟩
    · apply MarkedFrame.holes_plug_congr
      simp [SeenCursor.focus, MarkedTree.holes]
    · apply MarkedFrame.keys_plug_congr
      simp [SeenCursor.focus, MarkedTree.skeleton, inorder]
  | rotateLeftSeen A B C x y fs =>
    refine ⟨_, Or.inl rfl, ?_, ?_⟩
    · apply MarkedFrame.holes_plug_congr
      simp [SeenCursor.focus, MarkedTree.holes, List.append_assoc]
    · apply MarkedFrame.keys_plug_congr
      simp [SeenCursor.focus, MarkedTree.skeleton, inorder, List.append_assoc]
  | rotateLeftNew A B C x y fs =>
    refine ⟨MarkedFrame.plug (.node A x (.node (.hole B) y (.hole C))) fs,
      Or.inr (MarkedFrame.reveal_plug (.right A x (.root B C y)) fs), ?_, ?_⟩
    · apply MarkedFrame.holes_plug_congr
      simp [SeenCursor.focus, MarkedTree.holes, List.append_assoc]
    · apply MarkedFrame.keys_plug_congr
      simp [SeenCursor.focus, MarkedTree.skeleton, inorder, List.append_assoc]

/-- Already visited keys remain visited after revealing another node. -/
theorem MarkedTree.Reveal.keys_sublist {m n : MarkedTree α} (h : MarkedTree.Reveal m n) :
    (inorder m.skeleton).Sublist (inorder n.skeleton) := by
  induction h with
  | root l r a => exact List.nil_sublist _
  | left h a r ih => exact (ih.append (List.Sublist.refl [a])).append (List.Sublist.refl _)
  | right l a h ih => exact (List.Sublist.refl _).append ih

/-- Pull one pointer operation back to the original visited hull, preserving
all previously visited keys and adding at most one new key. -/
theorem SeenStep.pullback {c d : SeenCursor α} (h : SeenStep c d) (source : MarkedTree α)
    (same_holes : source.holes = c.tree.holes)
    (same_keys : inorder source.skeleton = inorder c.tree.skeleton) :
    ∃ source' : MarkedTree α, source'.erase = source.erase ∧
      source'.holes = d.tree.holes ∧ inorder source'.skeleton = inorder d.tree.skeleton ∧
      (inorder source.skeleton).Sublist (inorder source'.skeleton) ∧
      size source'.skeleton ≤ size source.skeleton + 1 := by
  obtain ⟨exposed, hexposed, hholes, hkeys⟩ := h.expand
  rcases hexposed with heq | hnew
  · subst exposed
    exact ⟨source, rfl, same_holes.trans hholes, same_keys.trans hkeys,
      List.Sublist.refl _, by omega⟩
  · obtain ⟨source', hs, hh, hk⟩ := MarkedTree.pullback_reveal source c.tree exposed
      same_holes same_keys hnew
    exact ⟨source', hs.erase_eq.symm, hh.trans hholes, hk.trans hkeys, hs.keys_sublist,
      Nat.le_of_eq hs.size_add_one⟩

/-- The visited cursor key belongs to the actual global touched skeleton. -/
theorem SeenCursor.key_mem (c : SeenCursor α) : c.key ∈ inorder c.tree.skeleton := by
  have aux (focus : MarkedTree α) (fs : List (MarkedFrame α)) {x : α}
      (hx : x ∈ inorder focus.skeleton) : x ∈ inorder (MarkedFrame.plug focus fs).skeleton := by
    induction fs generalizing focus with
    | nil => exact hx
    | cons f fs ih =>
      cases f with
      | left a r => apply ih; simp [MarkedTree.skeleton, inorder, hx]
      | right l a => apply ih; simp [MarkedTree.skeleton, inorder, hx]
  apply aux c.focus c.ancestors
  simp [SeenCursor.focus, MarkedTree.skeleton, inorder]

/-- Constructive tracking of an arbitrary actual pointer trace. -/
theorem Trace.tracked {c d : Cursor α} {xs : List α} {cost : Nat} (h : Trace c xs d cost)
    (seen : SeenCursor α) (hseen : seen.erase = c) (source : MarkedTree α)
    (same_holes : source.holes = seen.tree.holes)
    (same_keys : inorder source.skeleton = inorder seen.tree.skeleton) :
    ∃ (last : SeenCursor α) (source' : MarkedTree α), last.erase = d ∧
      source'.erase = source.erase ∧ source'.holes = last.tree.holes ∧
      inorder source'.skeleton = inorder last.tree.skeleton ∧
      (inorder source.skeleton).Sublist (inorder source'.skeleton) ∧
      size source'.skeleton + xs.length ≤ size source.skeleton + cost ∧
      ∀ x ∈ xs, x ∈ inorder source'.skeleton := by
  induction h generalizing seen source with
  | nil c =>
    exact ⟨seen, source, hseen, rfl, same_holes, same_keys, List.Sublist.refl _, by simp, by simp⟩
  | step move rest ih =>
    obtain ⟨next, hnext, hstep⟩ := move.lift seen hseen
    obtain ⟨newSource, he, hh, hk, hs, hsize⟩ := hstep.pullback source same_holes same_keys
    obtain ⟨last, source', hlast, he', hh', hk', hs', hsize', hrequests⟩ :=
      ih next hnext newSource hh hk
    refine ⟨last, source', hlast, he'.trans he, hh', hk', hs.trans hs', ?_, hrequests⟩
    omega
  | @serve c d x xs cost at_key rest ih =>
    obtain ⟨last, source', hlast, he, hh, hk, hs, hsize, hrequests⟩ :=
      ih seen hseen source same_holes same_keys
    refine ⟨last, source', hlast, he, hh, hk, hs, by simp only [List.length_cons]; omega, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with hyx | hyrest
    · subst y
      have hx : seen.key = x := by
        rw [← hseen] at at_key
        exact Option.some.inj at_key
      have hmem : x ∈ inorder source.skeleton := by
        rw [same_keys, ← hx]
        exact seen.key_mem
      exact hs.subset hmem
    · exact hrequests y hyrest

/-- Serving requests is itself charged, so their number never exceeds trace cost. -/
theorem Trace.length_le_cost {c d : Cursor α} {xs : List α} {cost : Nat}
    (h : Trace c xs d cost) : xs.length ≤ cost := by
  induction h with
  | nil => simp
  | step move rest ih => omega
  | serve at_key rest ih => simp only [List.length_cons]; omega

/-- An empty root has no legal nonempty root-starting access. -/
theorem Trace.empty_root_word {xs : List α} {d : Cursor α} {cost : Nat}
    (h : Trace (Cursor.atRoot (.empty : Tree α)) xs d cost) : xs = [] := by
  cases h with
  | nil => rfl
  | step move rest => cases move
  | serve at_key rest => simp [Cursor.atRoot, rootKey] at at_key

/-- Every ordinary root-starting pointer access has a concrete rooted-hull
realization whose number of touched keys is at most its actual pointer cost. -/
theorem Access.toHullAccess {x : α} {before after : Tree α} {cost : Nat}
    (h : Access x before after cost) :
    ∃ hull : HullAccess x before after, hull.cost ≤ cost := by
  obtain ⟨final, hfinal, htrace⟩ := h
  cases before with
  | empty => have hn := htrace.empty_root_word; simp at hn
  | node l a r =>
    let start : SeenCursor α := ⟨.hole l, a, .hole r, []⟩
    let source : MarkedTree α := .node (.hole l) a (.hole r)
    obtain ⟨last, source', hlast, he, hh, hk, _, hsize, hrequests⟩ :=
      htrace.tracked start rfl source rfl rfl
    have hbefore : source'.erase = Tree.node l a r := he
    have hafter : last.tree.erase = after := by
      rw [last.erase_tree, hlast, hfinal]
    let hull : HullAccess x (.node l a r) after := {
      source := source'.skeleton
      target := last.tree.skeleton
      gaps := source'.gapArray
      source_tree := source'.graft_gapArray.trans hbefore
      target_tree := by
        have hg : source'.gapArray = last.tree.gapArray := by
          funext i
          simp only [MarkedTree.gapArray, hh]
        rw [hg]
        exact last.tree.graft_gapArray.trans hafter
      same_keys := hk
      requested := hrequests x (by simp) }
    refine ⟨hull, ?_⟩
    change size source'.skeleton ≤ cost
    change size source'.skeleton + 1 ≤ 1 + cost at hsize
    omega

/-- An ordinary BST execution starts every new access at the current root. -/
inductive Execution : Tree α → List α → Tree α → Nat → Prop
  | nil (t : Tree α) : Execution t [] t 0
  | cons {t u v : Tree α} {x : α} {xs : List α} {cost restCost : Nat}
      (access : Access x t u cost) (rest : Execution u xs v restCost) :
      Execution t (x :: xs) v (cost + restCost)

/-- The standard pointer model embeds constructively in the rooted-hull model,
with no increase in cost and no final-root restriction. -/
theorem Execution.toAccessExecution {t u : Tree α} {xs : List α} {cost : Nat}
    (h : Execution t xs u cost) :
    ∃ hullCost ≤ cost, AccessExecution t xs u hullCost := by
  induction h with
  | nil t => exact ⟨0, by omega, .nil t⟩
  | cons access rest ih =>
    obtain ⟨hull, hhull⟩ := access.toHullAccess
    obtain ⟨restCost, hrestCost, hrest⟩ := ih
    exact ⟨hull.cost + restCost, by omega, .cons hull hrest⟩

end TangoSquared.MTR.Pointer
