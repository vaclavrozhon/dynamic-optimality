import ChaCha.Paper20261030.LocalRecordActions

/-! Actual local programs for projected rotations. The finite action
list depends only on the presence of the three projected pieces and the
old/new pivot ownership bits. Pivot values have already been observed.
Every list edit reads its reached vertex; the program returns to the root
and costs at most thirteen commands, matching the earlier trace kernel.
-/

namespace ChaCha.Paper20261030.LocalProjectedRotation

open ColoredStorage SourcePointer ProjectionLocal
open LocalRecordActions (Action)

variable {α ρ : Type*}

def Transforms (actions : List (Action ρ)) : Projected α ρ → Projected α ρ → Nat → Prop
  | none,none,_ => True
  | some before,some after,budget => LocalRecordActions.Rearranges actions before after budget
  | _,_,_ => False

theorem refl (source : Projected α ρ) (budget : Nat) : Transforms [] source source budget := by
  cases source
  · trivial
  · exact LocalRecordActions.refl _ _

theorem Transforms.mono {actions : List (Action ρ)} {before after : Projected α ρ} {m n : Nat}
    (execution : Transforms actions before after m) (bound : m ≤ n) : Transforms actions before after n := by
  cases before <;> cases after
  all_goals first | trivial | exact False.elim execution | exact LocalRecordActions.Rearranges.mono execution bound

theorem Transforms.trans {first last : List (Action ρ)} {a b c : Projected α ρ} {m n : Nat}
    (front : Transforms first a b m) (back : Transforms last b c n) : Transforms (first++last) a c (m+n) := by
  cases a <;> cases b <;> cases c
  all_goals first | trivial | exact False.elim front | exact False.elim back | exact LocalRecordActions.Rearranges.trans front back

def pop (present : Bool) : List (Action ρ) := if present then [.pop] else []
def push (present : Bool) (record : ρ) : List (Action ρ) := if present then [.prepend [record]] else []

theorem remove (present : Bool) (record : ρ) (source : Projected α ρ) :
    Transforms (pop present) (attach present record source) source 2 := by
  cases present <;> cases source with
  | none => trivial
  | some source =>
    first
    | exact LocalRecordActions.refl _ _
    | intro outside
      have run := LocalRecordActions.pop (source.setRoot (record::source.rootRecord)) outside
      have target : (source.setRoot (record::source.rootRecord)).setRoot
          (source.setRoot (record::source.rootRecord)).rootRecord.tail = source := by cases source <;> rfl
      exact ⟨[(source.setRoot (record::source.rootRecord)).rootRecord],2,
        by simpa only [target,pop,ite_true] using run,le_rfl⟩

theorem insert (present : Bool) (record : ρ) (source : Projected α ρ) :
    Transforms (push present record) source (attach present record source) 2 := by
  cases present <;> cases source with
  | none => trivial
  | some source =>
    first
    | exact LocalRecordActions.refl _ _
    | exact fun outside => ⟨_,2,LocalRecordActions.prepend [record] source outside,le_rfl⟩

def liftLeft (a r : Bool) (actions : List (Action ρ)) : List (Action ρ) :=
  if a then if r then LocalRecordActions.left actions else actions else []

def liftRight (l a : Bool) (actions : List (Action ρ)) : List (Action ρ) :=
  if a then if l then LocalRecordActions.right actions else actions else []

theorem Transforms.join_left {actions : List (Action ρ)} {a b : Projected α ρ} {n : Nat}
    (body : Transforms actions a b n) (r : Projected α ρ) :
    Transforms (liftLeft a.isSome r.isSome actions) (join a r) (join b r) (n+2) := by
  cases a with
  | none => cases b with
    | none => exact refl _ _
    | some => exact False.elim body
  | some a => cases b with
    | none => exact False.elim body
    | some b => cases r with
      | none => exact LocalRecordActions.Rearranges.mono body (by omega)
      | some r => exact LocalRecordActions.Rearranges.left body

theorem Transforms.join_right {actions : List (Action ρ)} {a b : Projected α ρ} {n : Nat}
    (body : Transforms actions a b n) (l : Projected α ρ) :
    Transforms (liftRight l.isSome a.isSome actions) (join l a) (join l b) (n+2) := by
  cases a with
  | none => cases b with
    | none => exact refl _ _
    | some => exact False.elim body
  | some a => cases b with
    | none => exact False.elim body
    | some b => cases l with
      | none => exact LocalRecordActions.Rearranges.mono body (by omega)
      | some l => exact LocalRecordActions.Rearranges.right body

def route (a b c : Bool) : List (Action ρ) := if a && b && c then [.nav .rotateRight] else []

theorem associate (a b c : Projected α ρ) :
    Transforms (route a.isSome b.isSome c.isSome) (join (join a b) c) (join a (join b c)) 1 := by
  cases a <;> cases b <;> cases c
  all_goals first
    | exact refl _ _
    | exact fun outside => ⟨[],1,LocalRecordActions.nav .rotateRight rfl,le_rfl⟩

theorem join_isSome (a b : Projected α ρ) : (join a b).isSome = (a.isSome || b.isSome) := by
  cases a <;> cases b <;> rfl

theorem attach_isSome (present : Bool) (record : ρ) (source : Projected α ρ) :
    (attach present record source).isSome = source.isSome := by
  cases present <;> cases source <;> rfl

def actions (a b c : Bool) (p q : ρ) (oldP oldQ newP newQ : Bool) : List (Action ρ) :=
  (((pop oldQ ++ liftLeft (a || b) c (pop oldP)) ++ route a b c) ++
    liftRight a (b || c) (push newQ q)) ++ push newP p

theorem rotation (a b c : Projected α ρ) (p q : ρ) (oldP oldQ newP newQ : Bool) :
    Transforms (actions a.isSome b.isSome c.isSome p q oldP oldQ newP newQ)
      (attach oldQ q (join (attach oldP p (join a b)) c))
      (attach newP p (join a (attach newQ q (join b c)))) 13 := by
  have actual := ((((remove oldQ q _).trans ((remove oldP p _).join_left c)).trans
    (associate a b c)).trans ((insert newQ q _).join_right a)).trans (insert newP p _)
  simpa only [actions,attach_isSome,join_isSome] using actual

theorem actions_length (a b c : Bool) (p q : ρ) (oldP oldQ newP newQ : Bool) :
    (actions a b c p q oldP oldQ newP newQ).length ≤ 9 := by
  cases a <;> cases b <;> cases c <;> cases oldP <;> cases oldQ <;> cases newP <;> cases newQ <;>
    simp [actions,pop,push,route,liftLeft,liftRight,LocalRecordActions.left,LocalRecordActions.right]

def routeLeft (a b c : Bool) : List (Action ρ) := if a && b && c then [.nav .rotateLeft] else []

theorem associate_left (a b c : Projected α ρ) :
    Transforms (routeLeft a.isSome b.isSome c.isSome) (join a (join b c)) (join (join a b) c) 1 := by
  cases a <;> cases b <;> cases c
  all_goals first
    | exact refl _ _
    | exact fun outside => ⟨[],1,LocalRecordActions.nav .rotateLeft rfl,le_rfl⟩

def actionsLeft (a b c : Bool) (p q : ρ) (oldP oldQ newP newQ : Bool) : List (Action ρ) :=
  (((pop newP ++ liftRight a (b || c) (pop newQ)) ++ routeLeft a b c) ++
    liftLeft (a || b) c (push oldP p)) ++ push oldQ q

theorem rotation_left (a b c : Projected α ρ) (p q : ρ) (oldP oldQ newP newQ : Bool) :
    Transforms (actionsLeft a.isSome b.isSome c.isSome p q oldP oldQ newP newQ)
      (attach newP p (join a (attach newQ q (join b c))))
      (attach oldQ q (join (attach oldP p (join a b)) c)) 13 := by
  have actual := ((((remove newP p _).trans ((remove newQ q _).join_right a)).trans
    (associate_left a b c)).trans ((insert oldP p _).join_left c)).trans (insert oldQ q _)
  simpa only [actionsLeft,attach_isSome,join_isSome] using actual

theorem actionsLeft_length (a b c : Bool) (p q : ρ) (oldP oldQ newP newQ : Bool) :
    (actionsLeft a b c p q oldP oldQ newP newQ).length ≤ 9 := by
  cases a <;> cases b <;> cases c <;> cases oldP <;> cases oldQ <;> cases newP <;> cases newQ <;>
    simp [actionsLeft,pop,push,routeLeft,liftLeft,liftRight,LocalRecordActions.left,LocalRecordActions.right]

end ChaCha.Paper20261030.LocalProjectedRotation
