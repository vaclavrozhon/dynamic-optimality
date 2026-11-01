import Mathlib
import FringeProjection

namespace GreedyMerge.Fringe.Schedule

open Splay.Tree Splay.Tree.BST
open GreedyMerge.Fringe

/-- A legal stable link takes adjacent roots, retains the smaller-rank
winner in their place, and permanently removes the loser. -/
inductive Link (rank : ℕ → ℕ) : (ℕ × ℕ) → List ℕ → List ℕ → Prop
  | left (pre post : List ℕ) {winner loser : ℕ}
      (h : rank winner < rank loser) :
      Link rank (winner,loser) (pre ++ winner::loser::post) (pre ++ winner::post)
  | right (pre post : List ℕ) {winner loser : ℕ}
      (h : rank winner < rank loser) :
      Link rank (winner,loser) (pre ++ loser::winner::post) (pre ++ winner::post)

inductive Run (rank : ℕ → ℕ) : List (ℕ × ℕ) → List ℕ → List ℕ → Prop
  | nil (roots : List ℕ) : Run rank [] roots roots
  | cons {event : ℕ × ℕ} {events : List (ℕ × ℕ)} {before middle after : List ℕ}
      (first : Link rank event before middle) (rest : Run rank events middle after) :
      Run rank (event::events) before after

theorem Link.frame {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) (pre post : List ℕ) :
    Link rank event (pre ++ before ++ post) (pre ++ after ++ post) := by
  cases h with
  | left innerPrefix innerSuffix h =>
      simpa [List.append_assoc] using Link.left (pre++innerPrefix) (innerSuffix++post) h
  | right innerPrefix innerSuffix h =>
      simpa [List.append_assoc] using Link.right (pre++innerPrefix) (innerSuffix++post) h

theorem Run.frame {rank : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (h : Run rank events before after) (pre post : List ℕ) :
    Run rank events (pre ++ before ++ post) (pre ++ after ++ post) := by
  induction h with
  | nil roots =>exact Run.nil _
  | cons first rest ih =>exact Run.cons (first.frame pre post) ih

theorem Run.append {rank : ℕ → ℕ} {first second : List (ℕ × ℕ)}
    {before middle after : List ℕ}
    (hfirst : Run rank first before middle) (hsecond : Run rank second middle after) :
    Run rank (first++second) before after := by
  induction hfirst with
  | nil roots =>exact hsecond
  | cons first rest ih =>exact Run.cons first (ih hsecond)

def atoms {lo hi : ℕ} : BST lo hi → List ℕ
  | .empty i => [2*i]
  | .node (root := q) left right => atoms left ++ [2*q+1] ++ atoms right

def localSchedule (owner : ℕ → ℕ) {lo q hi : ℕ}
    (left : BST lo q) (right : BST (q+1) hi) : List (ℕ × ℕ) :=
  if owner q=treeOwner owner left then
    [(owner q,2*q+1),(owner q,treeOwner owner right)]
  else if owner q=2*q+1 then
    [(owner q,treeOwner owner left),(owner q,treeOwner owner right)]
  else [(owner q,2*q+1),(owner q,treeOwner owner left)]

def schedule (owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → List (ℕ × ℕ)
  | .empty _ => []
  | .node left right => schedule owner left ++ schedule owner right ++ localSchedule owner left right

/-- Each local contraction is a two-link legal execution on its three
current roots. The inactive adjacent value is taken before the farther
subtree root whenever the winner is a gap. -/
theorem local_run {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    Run rank (localSchedule owner left right)
      [treeOwner owner left,2*q+1,treeOwner owner right] [owner q] := by
  have hl := left.lower_le_upper
  have hr := right.lower_le_upper
  have hleft := treeOwner_bounds rank owner left hproj.2.1
  have hright := treeOwner_bounds rank owner right hproj.2.2
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · have hvalue := hproj.1.2 (2*q+1) (by omega) (by omega) (by omega)
    have hother := hproj.1.2 (treeOwner owner right) (by omega) (by omega) (by omega)
    rw [h.1] at hvalue hother
    have hrun := Run.cons (Link.left [] [treeOwner owner right] hvalue)
      (Run.cons (Link.left [] [] hother) (Run.nil [2*q]))
    simpa [localSchedule,h.1,h.2.1] using hrun
  · have hvalue := hproj.1.2 (treeOwner owner left) (by omega) (by omega) (by omega)
    have hother := hproj.1.2 (treeOwner owner right) (by omega) (by omega) (by omega)
    have hn : 2*q+1 ≠ treeOwner owner left := by omega
    rw [h.1] at hvalue hother
    have hrun := Run.cons (Link.right [] [treeOwner owner right] hvalue)
      (Run.cons (Link.left [] [] hother) (Run.nil [2*q+1]))
    simpa [localSchedule,h.1,hn] using hrun
  · have hvalue := hproj.1.2 (2*q+1) (by omega) (by omega) (by omega)
    have hother := hproj.1.2 (treeOwner owner left) (by omega) (by omega) (by omega)
    have hn : 2*q+2 ≠ treeOwner owner left := by omega
    rw [h.1] at hvalue hother
    have hrun := Run.cons (Link.right [treeOwner owner left] [] hvalue)
      (Run.cons (Link.right [] [] hother) (Run.nil [2*q+2]))
    simpa [localSchedule,h.1,h.2.1,hn] using hrun

/-- The full canonical ternary contraction admits an explicit legal
bottom-up adjacent-root schedule. No Cartesian-forest or scheduling
hypothesis is an input to this theorem. -/
theorem schedule_run {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hproj : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) :
    Run rank (schedule owner tree) (atoms tree) [treeOwner owner tree] := by
  induction tree with
  | empty =>exact Run.nil _
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku)
      have hfirst := hleft.frame [] ([2*q+1]++atoms right)
      have hsecond := hright.frame [treeOwner owner left,2*q+1] []
      have hlocal := local_run rank owner left right hproj hloc
      have hsecond' : Run rank (schedule owner right)
          ([treeOwner owner left]++([2*q+1]++atoms right))
          [treeOwner owner left,2*q+1,treeOwner owner right] := by
        simpa using hsecond
      have hall := hfirst.append (hsecond'.append hlocal)
      simpa [atoms,schedule,treeOwner,List.append_assoc] using hall

theorem local_schedule_perm {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (localSchedule owner left right).Perm
      ((localChildren owner left right).map (fun child => (owner q,child))) := by
  have hleft := treeOwner_bounds rank owner left hproj.2.1
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · simp [localSchedule,h.1,h.2.1,h.2.2]
  · have hn : 2*q+1 ≠ treeOwner owner left := by omega
    simp [localSchedule,h.1,h.2,hn]
  · have hn : 2*q+2 ≠ treeOwner owner left := by omega
    simp only [localSchedule,h.1,h.2.2,if_neg hn]
    have hnvalue : ¬2*q+2=2*q+1 := by omega
    simp only [if_neg hnvalue,List.map_cons,List.map_nil]
    exact List.Perm.swap _ _ []

/-- Every final projection edge is installed exactly once. -/
theorem schedule_perm_edges {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hproj : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) :
    (schedule owner tree).Perm (edges owner tree) := by
  induction tree with
  | empty =>exact List.Perm.refl _
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku)
      exact (hleft.append hright).append (local_schedule_perm rank owner left right hproj hloc)

def arrivals (goLeft : Bool) (parent : ℕ) (events : List (ℕ × ℕ)) : List ℕ :=
  events.filterMap (fun event =>
    if event.1=parent ∧ (if goLeft then event.2<parent else parent<event.2)
      then some event.2 else none)

def arrivalOrder (goLeft : Bool) (first second : ℕ) : Prop :=
  if goLeft then second<first else first<second

def arrivalSeparator (goLeft : Bool) (parent : ℕ) : ℕ :=
  if goLeft then (parent-1)/2 else parent/2

@[simp] theorem arrivals_append (goLeft : Bool) (parent : ℕ)
    (first second : List (ℕ × ℕ)) :
    arrivals goLeft parent (first++second) =
      arrivals goLeft parent first ++ arrivals goLeft parent second := by
  simp [arrivals,List.filterMap_append]

theorem local_arrival_lists {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (owner q=2*q ∧ arrivals true (owner q) (localSchedule owner left right)=[] ∧
      arrivals false (owner q) (localSchedule owner left right)=[2*q+1,treeOwner owner right]) ∨
    (owner q=2*q+1 ∧ arrivals true (owner q) (localSchedule owner left right)=[treeOwner owner left] ∧
      arrivals false (owner q) (localSchedule owner left right)=[treeOwner owner right]) ∨
    (owner q=2*q+2 ∧ arrivals true (owner q) (localSchedule owner left right)=[2*q+1,treeOwner owner left] ∧
      arrivals false (owner q) (localSchedule owner left right)=[]) := by
  have hleft := treeOwner_bounds rank owner left hproj.2.1
  have hright := treeOwner_bounds rank owner right hproj.2.2
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · left
    refine ⟨h.1,?_,?_⟩
    · have hn1 : ¬2*q+1<2*q := by omega
      have hn2 : ¬treeOwner owner right<2*q := by omega
      simp [arrivals,localSchedule,h.1,h.2.1,hn1,hn2]
    · have hy1 : 2*q<2*q+1 := by omega
      have hy2 : 2*q<treeOwner owner right := by omega
      simp [arrivals,localSchedule,h.1,h.2.1,hy1,hy2]
  · right;left
    have hn : 2*q+1 ≠ treeOwner owner left := by omega
    refine ⟨h.1,?_,?_⟩
    · have hy1 : treeOwner owner left<2*q+1 := by omega
      have hn2 : ¬treeOwner owner right≤2*q := by omega
      simp [arrivals,localSchedule,h.1,hn,hleft.2,hn2]
    · have hn1 : ¬2*q+1<treeOwner owner left := by omega
      have hy2 : 2*q+1<treeOwner owner right := by omega
      simp [arrivals,localSchedule,h.1,hn,hn1,hy2]
  · right;right
    have hn : 2*q+2 ≠ treeOwner owner left := by omega
    have hnv : ¬2*q+2=2*q+1 := by omega
    refine ⟨h.1,?_,?_⟩
    · have hy1 : 2*q+1<2*q+2 := by omega
      have hy2 : treeOwner owner left<2*q+2 := by omega
      simp [arrivals,localSchedule,h.1,hn,hy1,hy2]
    · have hn1 : ¬2*q+2<2*q+1 := by omega
      have hn2 : ¬2*q+2<treeOwner owner left := by omega
      simp [arrivals,localSchedule,h.1,hn,hn1,hn2]

theorem local_arrivals_other_parent {lo q hi : ℕ} (owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi) (goLeft : Bool) (parent : ℕ)
    (hne : owner q≠parent) : arrivals goLeft parent (localSchedule owner left right)=[] := by
  unfold localSchedule
  split_ifs <;> simp [arrivals,hne]

/-- Each side has only one possible contributing separator, and its
local arrivals are already in the required inner-to-outer order. -/
theorem local_arrival_spec {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi) (goLeft : Bool) (parent : ℕ)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (arrivals goLeft parent (localSchedule owner left right)).Pairwise (arrivalOrder goLeft) ∧
    (q≠arrivalSeparator goLeft parent → arrivals goLeft parent (localSchedule owner left right)=[]) := by
  by_cases hp : owner q=parent
  · subst parent
    have hleft := treeOwner_bounds rank owner left hproj.2.1
    have hright := treeOwner_bounds rank owner right hproj.2.2
    rcases local_arrival_lists rank owner left right hproj hloc with h | h | h
    · cases goLeft
      · rw [h.2.2]
        simp only [arrivalOrder,arrivalSeparator,Bool.false_eq_true,if_false,List.pairwise_pair]
        constructor
        · omega
        · intro hne
          have heq : q=owner q/2 := by omega
          exact False.elim (hne heq)
      · rw [h.2.1];simp
    · cases goLeft
      · rw [h.2.2]
        simp only [arrivalSeparator,Bool.false_eq_true,if_false,List.pairwise_singleton,true_and]
        intro hne
        have heq : q=owner q/2 := by omega
        exact False.elim (hne heq)
      · rw [h.2.1]
        simp only [arrivalSeparator,if_true,List.pairwise_singleton,true_and]
        intro hne
        have heq : q=(owner q-1)/2 := by omega
        exact False.elim (hne heq)
    · cases goLeft
      · rw [h.2.2];simp
      · rw [h.2.1]
        simp only [arrivalOrder,arrivalSeparator,if_true,List.pairwise_pair]
        constructor
        · omega
        · intro hne
          have heq : q=(owner q-1)/2 := by omega
          exact False.elim (hne heq)
  · rw [local_arrivals_other_parent owner left right goLeft parent hp]
    simp

theorem arrivals_empty_if_separator_outside {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (goLeft : Bool) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (hout : arrivalSeparator goLeft parent<lo ∨ hi≤arrivalSeparator goLeft parent) :
    arrivals goLeft parent (schedule owner tree)=[] := by
  induction tree with
  | empty =>simp [schedule,arrivals]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega)) (by omega)
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku) (by omega)
      have hlocal := (local_arrival_spec rank owner left right goLeft parent hproj hloc).2 (by omega)
      simp [schedule,hleft,hright,hlocal]

/-- For every winner, all left arrivals are decreasing in key order and
all right arrivals are increasing. This includes inactive values and is
proved for the literal adjacent-link schedule. -/
theorem schedule_arrivals_inner_to_outer {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (goLeft : Bool) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (arrivals goLeft parent (schedule owner tree)).Pairwise (arrivalOrder goLeft) := by
  induction tree with
  | empty =>simp [schedule,arrivals]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hlocLeft : LocalOwners rank owner lo q := by intro k hkl hku;exact hloc k hkl (by omega)
      have hlocRight : LocalOwners rank owner (q+1) hi := by intro k hkl hku;exact hloc k (by omega) hku
      have hleft := ihLeft hproj.2.1 hlocLeft
      have hright := ihRight hproj.2.2 hlocRight
      have hlocal := local_arrival_spec rank owner left right goLeft parent hproj hloc
      by_cases hlt : arrivalSeparator goLeft parent < q
      · have hrightEmpty := arrivals_empty_if_separator_outside rank owner right goLeft parent hproj.2.2 hlocRight (by omega)
        have hlocalEmpty := hlocal.2 (by omega)
        simpa [schedule,hrightEmpty,hlocalEmpty] using hleft
      · by_cases hgt : q < arrivalSeparator goLeft parent
        · have hleftEmpty := arrivals_empty_if_separator_outside rank owner left goLeft parent hproj.2.1 hlocLeft (by omega)
          have hlocalEmpty := hlocal.2 (by omega)
          simpa [schedule,hleftEmpty,hlocalEmpty] using hright
        · have hleftEmpty := arrivals_empty_if_separator_outside rank owner left goLeft parent hproj.2.1 hlocLeft (by omega)
          have hrightEmpty := arrivals_empty_if_separator_outside rank owner right goLeft parent hproj.2.2 hlocRight (by omega)
          simpa [schedule,hleftEmpty,hrightEmpty] using hlocal.1

theorem atoms_mem_iff {lo hi : ℕ} (tree : BST lo hi) (atom : ℕ) :
    atom ∈ atoms tree ↔ 2*lo ≤ atom ∧ atom ≤ 2*hi := by
  induction tree with
  | empty =>simp only [atoms,List.mem_singleton];omega
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      simp only [atoms,List.mem_append,List.mem_singleton,ihLeft,ihRight]
      omega

theorem atoms_pairwise {lo hi : ℕ} (tree : BST lo hi) :
    (atoms tree).Pairwise (fun a b => a < b) := by
  induction tree with
  | empty =>simp [atoms]
  | @node lo q hi left right ihLeft ihRight =>
      have hp : (atoms left ++ (2*q+1)::atoms right).Pairwise (fun a b => a < b) := by
        apply List.pairwise_append.mpr
        refine ⟨ihLeft,?_,?_⟩
        · apply List.pairwise_cons.mpr
          refine ⟨?_,ihRight⟩
          intro b hb
          have h := (atoms_mem_iff right b).mp hb
          omega
        · intro a ha b hb
          have h := (atoms_mem_iff left a).mp ha
          rcases List.mem_cons.mp hb with heq | hmem
          · omega
          · have hh := (atoms_mem_iff right b).mp hmem
            omega
      simpa [atoms,List.append_assoc] using hp

theorem atoms_nodup {lo hi : ℕ} (tree : BST lo hi) : (atoms tree).Nodup := by
  exact (atoms_pairwise tree).imp (fun h => Nat.ne_of_lt h)

theorem Link.sublist {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) : after.Sublist before := by
  cases h with
  | left pre post h =>
      exact ((List.sublist_cons_self _ post).cons_cons _).append_left pre
  | right pre post h =>
      exact (List.sublist_cons_self _ (_::post)).append_left pre

theorem Run.sublist {rank : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (h : Run rank events before after) : after.Sublist before := by
  induction h with
  | nil roots =>exact List.Sublist.refl _
  | cons first rest ih =>exact ih.trans first.sublist

theorem Link.members {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) : event.1 ∈ before ∧ event.2 ∈ before := by
  cases h <;> simp

theorem Link.loser_count {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) :
    after.count event.2 + 1 = before.count event.2 := by
  cases h with
  | @left pre post winner loser h =>
      have hne : winner≠loser := by intro heq;subst loser;omega
      simp [List.count_append,hne];omega
  | @right pre post winner loser h =>
      have hne : winner≠loser := by intro heq;subst loser;omega
      simp [List.count_append,hne];omega

theorem Link.loser_absent {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) (hnodup : before.Nodup) : event.2 ∉ after := by
  have hle := List.nodup_iff_count_le_one.mp hnodup event.2
  have hcount := h.loser_count
  apply List.count_eq_zero.mp
  omega

theorem Run.event_members {rank : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (h : Run rank events before after) (event : ℕ × ℕ) (hmem : event ∈ events) :
    event.1 ∈ before ∧ event.2 ∈ before := by
  induction h with
  | nil roots =>simp at hmem
  | @cons firstEvent events before middle after first rest ih =>
      rcases List.mem_cons.mp hmem with heq | htail
      · subst event;exact first.members
      · have hm := ih htail
        exact ⟨first.sublist.subset hm.1,first.sublist.subset hm.2⟩

/-- Once a root loses, it cannot be used by any later event, as either
winner or loser. Together with the actual schedule theorem this is the
bottom-up condition needed by winner/loser history charges. -/
theorem loser_never_used_again {rank : ℕ → ℕ} {firstEvent : ℕ × ℕ}
    {events : List (ℕ × ℕ)} {before middle after : List ℕ}
    (first : Link rank firstEvent before middle) (rest : Run rank events middle after)
    (hnodup : before.Nodup) :
    ∀ event ∈ events, event.1≠firstEvent.2 ∧ event.2≠firstEvent.2 := by
  intro event hmem
  have hm := rest.event_members event hmem
  have hn := first.loser_absent hnodup
  constructor
  · intro heq;exact hn (heq ▸ hm.1)
  · intro heq;exact hn (heq ▸ hm.2)

theorem edges_winner_count {lo hi : ℕ} (owner : ℕ → ℕ)
    (tree : BST lo hi) (parent : ℕ) :
    (edges owner tree).countP (fun event => event.1 == parent) =
      (outgoing owner parent tree).length := by
  induction tree with
  | empty =>simp [edges,outgoing]
  | @node lo q hi left right ihLeft ihRight =>
      by_cases hp : owner q=parent
      · simp [edges,outgoing,List.countP_map,Function.comp_def,ihLeft,ihRight,hp]
      · simp [edges,outgoing,List.countP_map,Function.comp_def,ihLeft,ihRight,hp]

/-- A literal consolidation schedule has at most four wins by each record. -/
theorem schedule_winner_count_le_four {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (parent : ℕ) (hproj : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) :
    (schedule owner tree).countP (fun event => event.1 == parent) ≤ 4 := by
  rw [(schedule_perm_edges rank owner tree hproj hloc).countP_eq,
    edges_winner_count owner tree parent]
  exact outgoing_degree_le_four rank owner tree parent hproj hloc

#print axioms schedule_run
#print axioms schedule_perm_edges
#print axioms schedule_arrivals_inner_to_outer
#print axioms schedule_winner_count_le_four
#print axioms atoms_nodup
#print axioms loser_never_used_again

end GreedyMerge.Fringe.Schedule
