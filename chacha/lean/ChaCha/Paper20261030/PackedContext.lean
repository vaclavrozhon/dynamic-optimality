import ChaCha.Paper20261030.PackedRotation

/-!
# Locality of packed records inside an arbitrary source context

A source subtree contributes a nonempty tree to a color projection. All
records from suppressed ancestors that share its projected root form a
prefix of that root's record list. The remaining projected ancestors are
ordinary cursor frames. Replacing the subtree by another with the same
color support preserves this context, including the prefix.

This is a structural correspondence. The charged rotation theorem below
starts at the corresponding physical cursor; navigating to that cursor
and maintaining additional cursors are separate obligations.
-/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

theorem plug_append (t : Source α ρ) (inside outside : List (Frame α ρ)) :
    plug t (inside ++ outside) = plug (plug t inside) outside := by
  induction inside generalizing t with
  | nil => rfl
  | cons frame rest ih => cases frame <;> exact ih _

end ChaCha.Paper20261030.SourcePointer

namespace ChaCha.Paper20261030.ProjectionLocal

open ColoredStorage SourcePointer

variable {α ρ : Type*}

def prepend (extras : List ρ) (t : Source α (List ρ)) : Source α (List ρ) :=
  t.setRoot (extras ++ t.rootRecord)

theorem prepend_nil (t : Source α (List ρ)) : prepend [] t = t := by
  cases t <;> rfl

theorem prepend_prepend (xs ys : List ρ) (t : Source α (List ρ)) :
    prepend xs (prepend ys t) = prepend (xs ++ ys) t := by
  cases t <;> simp [prepend,Source.setRoot,Source.rootRecord,List.append_assoc]

/-- Modify the record of the outermost frame, where the whole-tree root lives. -/
def prependOutside (xs : List ρ) : List (Frame α (List ρ)) → List (Frame α (List ρ))
  | [] => []
  | [.left record r] => [.left (xs ++ record) r]
  | [.right l record] => [.right l (xs ++ record)]
  | frame :: next :: rest => frame :: prependOutside xs (next :: rest)

theorem prepend_plug (xs : List ρ) (t : Source α (List ρ))
    (rest : List (Frame α (List ρ))) (hne : rest ≠ []) :
    prepend xs (plug t rest) = plug t (prependOutside xs rest) := by
  induction rest generalizing t with
  | nil => exact False.elim (hne rfl)
  | cons frame rest ih =>
    cases rest with
    | nil => cases frame <;> rfl
    | cons next tail =>
      cases frame <;> exact ih _ (by simp)

/-- The same physical context, including root prefixes, around two pieces. -/
def Patch (a b : Source α (List ρ)) (before after : Projected α ρ) : Prop :=
  ∃ extras rest,
    before = some (plug (prepend extras a) rest) ∧
    after = some (plug (prepend extras b) rest)

theorem patch_root (a b : Source α (List ρ)) : Patch a b (some a) (some b) :=
  ⟨[],[],by simp [plug,prepend_nil],by simp [plug,prepend_nil]⟩

theorem Patch.join_left {a b : Source α (List ρ)} {before after : Projected α ρ}
    (h : Patch a b before after) (sibling : Projected α ρ) :
    Patch a b (join before sibling) (join after sibling) := by
  obtain ⟨extras,rest,rfl,rfl⟩ := h
  cases sibling with
  | none => exact ⟨extras,rest,rfl,rfl⟩
  | some sibling =>
    exact ⟨extras,rest ++ [.left [] sibling],by simp [join,plug_append,plug],
      by simp [join,plug_append,plug]⟩

theorem Patch.join_right {a b : Source α (List ρ)} {before after : Projected α ρ}
    (h : Patch a b before after) (sibling : Projected α ρ) :
    Patch a b (join sibling before) (join sibling after) := by
  obtain ⟨extras,rest,rfl,rfl⟩ := h
  cases sibling with
  | none => exact ⟨extras,rest,rfl,rfl⟩
  | some sibling =>
    exact ⟨extras,rest ++ [.right sibling []],by simp [join,plug_append,plug],
      by simp [join,plug_append,plug]⟩

theorem Patch.decorate {a b : Source α (List ρ)} {before after : Projected α ρ}
    (h : Patch a b before after) (xs : List ρ) :
    Patch a b (decorate xs before) (decorate xs after) := by
  obtain ⟨extras,rest,rfl,rfl⟩ := h
  cases rest with
  | nil =>
    refine ⟨xs ++ extras,[],?_,?_⟩
    all_goals simpa only [ProjectionLocal.decorate,Option.map_some,plug,prepend] using
      congrArg some (prepend_prepend xs extras _)
  | cons frame rest =>
    refine ⟨extras,prependOutside xs (frame :: rest),?_,?_⟩
    all_goals simpa only [ProjectionLocal.decorate,Option.map_some,prepend] using
      congrArg some (prepend_plug xs _ (frame :: rest) (by simp))

theorem Patch.attach {a b : Source α (List ρ)} {before after : Projected α ρ}
    (h : Patch a b before after) (present : Bool) (record : ρ) :
    Patch a b (attach present record before) (attach present record after) := by
  cases present
  · exact h
  · exact h.decorate [record]

end ChaCha.Paper20261030.ProjectionLocal

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer ProjectionLocal

variable {α ρ C : Type*} [LinearOrder C]

theorem owner_congr (color : α → C) {a b c d : Source α ρ}
    (hab : a.support color = b.support color) (hcd : c.support color = d.support color) :
    owner color a c = owner color b d := by
  simp only [owner,hab,hcd]

theorem packed_patch_context (color : α → C) (q : C)
    {s t : Source α ρ} (hs : s.support color = t.support color)
    {a b : Source α (List ρ)} (hp : Patch a b (packed color q s) (packed color q t))
    (ancestors : List (Frame α ρ)) :
    Patch a b (packed color q (plug s ancestors)) (packed color q (plug t ancestors)) := by
  induction ancestors generalizing s t with
  | nil => exact hp
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      apply ih (by simp only [Source.support,hs])
      simp only [packed_fork,owner_congr color hs rfl]
      exact (hp.join_left _).attach _ _
    | right sibling record =>
      apply ih (by simp only [Source.support,hs])
      simp only [packed_fork,owner_congr color rfl hs]
      exact (hp.join_right _).attach _ _

theorem packed_eq_context (color : α → C) (q : C)
    {s t : Source α ρ} (hs : s.support color = t.support color)
    (hp : packed color q s = packed color q t) (ancestors : List (Frame α ρ)) :
    packed color q (plug s ancestors) = packed color q (plug t ancestors) := by
  induction ancestors generalizing s t with
  | nil => exact hp
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      apply ih (by simp only [Source.support,hs])
      simp only [packed_fork,owner_congr color hs rfl,hp]
    | right sibling record =>
      apply ih (by simp only [Source.support,hs])
      simp only [packed_fork,owner_congr color rfl hs,hp]

/-- A rotation at any source depth costs at most seventeen operations at
the corresponding physical cursor, including all packed-record changes. -/
theorem packed_rotation_context (color : α → C) (q : C)
    (u v w : Source α ρ) (p r : ρ) (ancestors : List (Frame α ρ))
    (a b : Source α (List ρ))
    (ha : packed color q (.fork r (.fork p u v) w) = some a)
    (hb : packed color q (.fork p u (.fork r v w)) = some b) :
    ∃ (c d : Cursor α (List ρ)) (reads : List (List ρ)) (cost : Nat),
      packed color q (plug (.fork r (.fork p u v) w) ancestors) = some c.tree ∧
      packed color q (plug (.fork p u (.fork r v w)) ancestors) = some d.tree ∧
      Trace c reads d cost ∧ cost ≤ 17 := by
  have hs : (Source.fork r (.fork p u v) w).support color =
      (Source.fork p u (.fork r v w)).support color := by
    simp only [Source.support,Finset.union_assoc]
  have hp : Patch a b (packed color q (.fork r (.fork p u v) w))
      (packed color q (.fork p u (.fork r v w))) := by
    rw [ha,hb]
    exact patch_root _ _
  obtain ⟨extras,rest,hc,hd⟩ := packed_patch_context color q hs hp ancestors
  have h := packed_rotation_decorated color q u v w p r extras
  rw [ha,hb] at h
  obtain ⟨reads,cost,ht,hcost⟩ := h rest
  exact ⟨⟨prepend extras a,rest⟩,⟨prepend extras b,rest⟩,reads,cost,hc,hd,ht,hcost⟩

end ChaCha.Paper20261030.ColoredStorage
