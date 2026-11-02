import ChaCha.Paper20261030.ColoredStorage

/-!
# Updating a record at a reached projection root

The packing assigns the source root's record to the first slot at one
projection root. Updating that record therefore needs one slot write at
that root and leaves all other projections unchanged. This local result
does not yet account for locating arbitrary source cursors or relocating
records after rotations.
-/

namespace ChaCha.Paper20261030.ColoredStorage

variable {α ρ C : Type*}

def Source.setRoot (fresh : ρ) : Source α ρ → Source α ρ
  | .leaf key _ => .leaf key fresh
  | .fork _ l r => .fork fresh l r

def Source.rootOwner [LinearOrder C] (color : α → C) : Source α ρ → C
  | .leaf key _ => color key
  | .fork _ l r => owner color l r

def Stored.replaceFirst (fresh : ρ) : Stored α ρ → Stored α ρ
  | .empty => .empty
  | .leaf key records => .leaf key (records.modifyHead (fun _ => fresh))
  | .fork records l r => .fork (records.modifyHead (fun _ => fresh)) l r

theorem Stored.replaceFirst_addRoot (fresh old : ρ) (t : Stored α ρ) :
    (t.addRoot old).replaceFirst fresh = t.addRoot fresh := by
  cases t <;> rfl

theorem pack_root_head [LinearOrder C] (color : α → C) (t : Source α ρ) :
    ∃ tail, (pack color (t.rootOwner color) t).rootRecords = t.rootRecord :: tail := by
  cases t with
  | leaf key record => exact ⟨[],by simp [Source.rootOwner,pack,Stored.rootRecords,Source.rootRecord]⟩
  | fork record l r =>
    have hn := (pack_nonempty color (owner color l r) (.fork record l r)).mpr
      (owner_mem color l r)
    simp only [Source.rootOwner,pack,Source.rootRecord] at hn ⊢
    cases he : (pack color (owner color l r) l).join (pack color (owner color l r) r) <;>
      simp_all [Stored.addRoot,Stored.rootRecords]

theorem pack_setRoot [LinearOrder C] (color : α → C) (q : C) (t : Source α ρ) (fresh : ρ) :
    pack color q (t.setRoot fresh) =
      if t.rootOwner color = q then (pack color q t).replaceFirst fresh else pack color q t := by
  cases t with
  | leaf key record =>
    by_cases h : color key = q <;>
      simp [Source.setRoot,Source.rootOwner,pack,h,Stored.replaceFirst]
  | fork record l r =>
    by_cases h : owner color l r = q <;>
      simp [Source.setRoot,Source.rootOwner,pack,h,Stored.replaceFirst_addRoot]

/-- One update of an existing record slot at the current vertex. -/
inductive RootWrite : Stored α ρ → Stored α ρ → Prop
  | leaf (key : α) (old fresh : ρ) (tail : List ρ) :
      RootWrite (.leaf key (old :: tail)) (.leaf key (fresh :: tail))
  | fork (old fresh : ρ) (tail : List ρ) (l r : Stored α ρ) :
      RootWrite (.fork (old :: tail) l r) (.fork (fresh :: tail) l r)

theorem RootWrite.of_head (t : Stored α ρ) (old fresh : ρ) (tail : List ρ)
    (h : t.rootRecords = old :: tail) : RootWrite t (t.replaceFirst fresh) := by
  cases t with
  | empty => simp [Stored.rootRecords] at h
  | leaf key records =>
    change records = old :: tail at h
    subst records
    exact .leaf _ _ _ _
  | fork records l r =>
    change records = old :: tail at h
    subst records
    exact .fork _ _ _ _ _

theorem RootWrite.shape {a b : Stored α ρ} (h : RootWrite a b) : a.shape = b.shape := by
  cases h <;> rfl

theorem RootWrite.capacity {a b : Stored α ρ} (h : RootWrite a b) (capacity : Nat) :
    a.Bounded capacity ↔ b.Bounded capacity := by
  cases h <;> rfl

theorem pack_root_write [LinearOrder C] (color : α → C) (t : Source α ρ) (fresh : ρ) :
    ∃ q, RootWrite (pack color q t) (pack color q (t.setRoot fresh)) ∧
      ∀ other, other ≠ q → pack color other (t.setRoot fresh) = pack color other t := by
  refine ⟨t.rootOwner color,?_,?_⟩
  · obtain ⟨tail,head⟩ := pack_root_head color t
    rw [pack_setRoot,if_pos rfl]
    exact RootWrite.of_head _ t.rootRecord fresh tail head
  · intro other hne
    rw [pack_setRoot,if_neg (Ne.symm hne)]

end ChaCha.Paper20261030.ColoredStorage
