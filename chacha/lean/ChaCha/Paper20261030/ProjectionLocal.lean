import ChaCha.Paper20261030.SourcePointer

/-!
# Local projected rotation with explicit record updates

Assume the two pivot records have already been read. In one color, the
three unchanged pieces may be present or absent. Remove the old pivot
records at reached roots, perform the zero-or-one routing rotation, and
insert the pivot records at their new roots. This takes at most thirteen
actual source-pointer operations, independently of the piece sizes.

The record lists are single vertex payloads here. The colored packing
theorem bounds their lengths for the application with a fixed number of
colors. Locating the pivot records and maintaining other cursors remain
separate obligations.
-/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

def Rearranges (before after : Source α ρ) (budget : Nat) : Prop :=
  ∀ ancestors : List (Frame α ρ), ∃ reads cost,
    Trace ⟨before,ancestors⟩ reads ⟨after,ancestors⟩ cost ∧ cost ≤ budget

theorem rearranges_refl (t : Source α ρ) (budget : Nat) : Rearranges t t budget :=
  fun _ => ⟨[],0,.nil _,Nat.zero_le _⟩

theorem Rearranges.mono {a b : Source α ρ} {m n : Nat}
    (h : Rearranges a b m) (hmn : m ≤ n) : Rearranges a b n := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := h ancestors
  exact ⟨reads,cost,trace,hcost.trans hmn⟩

theorem Rearranges.trans {a b c : Source α ρ} {m n : Nat}
    (h : Rearranges a b m) (g : Rearranges b c n) : Rearranges a c (m + n) := by
  intro ancestors
  obtain ⟨hw,hc,ht,hb⟩ := h ancestors
  obtain ⟨gw,gc,gt,gb⟩ := g ancestors
  exact ⟨_,_,ht.append gt,Nat.add_le_add hb gb⟩

theorem Rearranges.left {a b r : Source α ρ} {record : ρ} {n : Nat}
    (h : Rearranges a b n) : Rearranges (.fork record a r) (.fork record b r) (n + 2) := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := h (.left record r :: ancestors)
  have up := Trace.step (Step.upLeft b r record ancestors) (Trace.nil _)
  have full := Trace.step (Step.left a r record ancestors) (trace.append up)
  exact ⟨_,_,full,by omega⟩

theorem Rearranges.right {l a b : Source α ρ} {record : ρ} {n : Nat}
    (h : Rearranges a b n) : Rearranges (.fork record l a) (.fork record l b) (n + 2) := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := h (.right l record :: ancestors)
  have up := Trace.step (Step.upRight l b record ancestors) (Trace.nil _)
  have full := Trace.step (Step.right l a record ancestors) (trace.append up)
  exact ⟨_,_,full,by omega⟩

theorem replace_root (t : Source α ρ) (fresh : ρ) : Rearranges t (t.setRoot fresh) 2 :=
  fun ancestors => ⟨_,2,write_charged t fresh ancestors,le_rfl⟩

end ChaCha.Paper20261030.SourcePointer

namespace ChaCha.Paper20261030.ProjectionLocal

open ColoredStorage SourcePointer

variable {α ρ : Type*}

abbrev Projected (α ρ : Type*) := Option (Source α (List ρ))

def Rearranges : Projected α ρ → Projected α ρ → Nat → Prop
  | none,none,_ => True
  | some a,some b,n => SourcePointer.Rearranges a b n
  | _,_,_ => False

theorem rearranges_refl (t : Projected α ρ) (budget : Nat) : Rearranges t t budget := by
  cases t
  · trivial
  · exact SourcePointer.rearranges_refl _ _

theorem Rearranges.trans {a b c : Projected α ρ} {m n : Nat}
    (h : Rearranges a b m) (g : Rearranges b c n) : Rearranges a c (m + n) := by
  cases a <;> cases b <;> cases c
  all_goals first | trivial | exact False.elim h | exact False.elim g | exact SourcePointer.Rearranges.trans h g

def join : Projected α ρ → Projected α ρ → Projected α ρ
  | none,r => r
  | l,none => l
  | some l,some r => some (.fork [] l r)

def attach (present : Bool) (record : ρ) (t : Projected α ρ) : Projected α ρ :=
  if present then t.map (fun s => s.setRoot (record :: s.rootRecord)) else t

theorem attach_forward (present : Bool) (record : ρ) (t : Projected α ρ) :
    Rearranges t (attach present record t) 2 := by
  cases present <;> cases t
  · trivial
  · exact SourcePointer.rearranges_refl _ _
  · trivial
  · exact SourcePointer.replace_root _ _

theorem attach_backward (present : Bool) (record : ρ) (t : Projected α ρ) :
    Rearranges (attach present record t) t 2 := by
  cases present <;> cases t with
  | none => trivial
  | some s =>
    first
    | exact SourcePointer.rearranges_refl _ _
    | cases s <;> exact SourcePointer.replace_root _ _

theorem Rearranges.join_left {a b r : Projected α ρ} {n : Nat}
    (h : Rearranges a b n) : Rearranges (join a r) (join b r) (n + 2) := by
  cases a with
  | none =>
    cases b with
    | none => exact rearranges_refl _ _
    | some => exact False.elim h
  | some a =>
    cases b with
    | none => exact False.elim h
    | some b =>
      cases r with
      | none => exact SourcePointer.Rearranges.mono h (by omega)
      | some r => exact SourcePointer.Rearranges.left h

theorem Rearranges.join_right {l a b : Projected α ρ} {n : Nat}
    (h : Rearranges a b n) : Rearranges (join l a) (join l b) (n + 2) := by
  cases a with
  | none =>
    cases b with
    | none => exact rearranges_refl _ _
    | some => exact False.elim h
  | some a =>
    cases b with
    | none => exact False.elim h
    | some b =>
      cases l with
      | none => exact SourcePointer.Rearranges.mono h (by omega)
      | some l => exact SourcePointer.Rearranges.right h

theorem join_associate (a b c : Projected α ρ) :
    Rearranges (join (join a b) c) (join a (join b c)) 1 := by
  cases a <;> cases b <;> cases c
  all_goals first
    | exact rearranges_refl _ _
    | exact fun ancestors => ⟨[],1,.step (.rotateRight _ _ _ _ _ ancestors) (.nil _),le_rfl⟩

theorem local_rotation (a b c : Projected α ρ) (p q : ρ)
    (oldP oldQ newP newQ : Bool) :
    Rearranges
      (attach oldQ q (join (attach oldP p (join a b)) c))
      (attach newP p (join a (attach newQ q (join b c)))) 13 := by
  exact ((((attach_backward oldQ q _).trans
    ((attach_backward oldP p _).join_left)).trans
      (join_associate a b c)).trans
        ((attach_forward newQ q _).join_right)).trans
          (attach_forward newP p _)

def decorate (extras : List ρ) (t : Projected α ρ) : Projected α ρ :=
  t.map (fun s => s.setRoot (extras ++ s.rootRecord))

theorem decorate_forward (extras : List ρ) (t : Projected α ρ) :
    Rearranges t (decorate extras t) 2 := by
  cases t
  · trivial
  · exact SourcePointer.replace_root _ _

theorem decorate_backward (extras : List ρ) (t : Projected α ρ) :
    Rearranges (decorate extras t) t 2 := by
  cases t with
  | none => trivial
  | some t => cases t <;> exact SourcePointer.replace_root _ _

theorem local_rotation_decorated (a b c : Projected α ρ) (p q : ρ)
    (oldP oldQ newP newQ : Bool) (extras : List ρ) :
    Rearranges
      (decorate extras (attach oldQ q (join (attach oldP p (join a b)) c)))
      (decorate extras (attach newP p (join a (attach newQ q (join b c))))) 17 :=
  ((decorate_backward extras _).trans
    (local_rotation a b c p q oldP oldQ newP newQ)).trans (decorate_forward extras _)

end ChaCha.Paper20261030.ProjectionLocal
