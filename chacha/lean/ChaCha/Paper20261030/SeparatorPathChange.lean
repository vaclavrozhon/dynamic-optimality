import ChaCha.Paper20261030.SeparatorPath

/-!
# The exact separator-word change at a preferred descendant

All ancestors on the current preferred path lie outside a descendant's
separator interval. Changing preferences inside that descendant therefore
replaces one contiguous word while retaining both outside words and all
their records. A root flip changes only its own preference bit and
exchanges which child's existing preferred-path word is attached to it.
-/

namespace ChaCha.Paper20261030.SeparatorPath

theorem word_congr {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (h : ∀ split ∈ reference.nodes, p split = q split) : word reference p = word reference q := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    have hp := h ⟨a,cut,b⟩ (by simp [DepthTree.nodes])
    have hl := ihl (fun s hs => h s (by simp [DepthTree.nodes,hs]))
    have hr := ihr (fun s hs => h s (by simp [DepthTree.nodes,hs]))
    simp only [word,hp,hl,hr]

theorem word_flip_root {a b cut : Nat} (ha : a ≤ cut) (hb : cut < b)
    (l : DepthTree a cut) (r : DepthTree (cut + 1) b) (preference : DepthSplit → Bool) (fresh : Bool) :
    word (.node cut ha hb l r) (Function.update preference ⟨a,cut,b⟩ fresh) =
      if fresh then ⟨cut,(⟨a,cut,b⟩,true)⟩ :: word r preference
      else word l preference ++ [⟨cut,(⟨a,cut,b⟩,false)⟩] := by
  have hl : word l (Function.update preference ⟨a,cut,b⟩ fresh) = word l preference := by
    apply word_congr
    intro s hs
    have hbounds := l.node_bounds hs
    have hne : s ≠ ⟨a,cut,b⟩ := by intro he; subst s; simp only at hbounds; omega
    exact Function.update_of_ne hne _ _
  have hr : word r (Function.update preference ⟨a,cut,b⟩ fresh) = word r preference := by
    apply word_congr
    intro s hs
    have hbounds := r.node_bounds hs
    have hne : s ≠ ⟨a,cut,b⟩ := by intro he; subst s; simp only at hbounds; omega
    exact Function.update_of_ne hne _ _
  simp only [word,Function.update_self,hl,hr]

theorem Descendant.word_context {preference : DepthSplit → Bool} {a b c d : Nat}
    {reference : DepthTree a b} {subtree : DepthTree c d}
    (h : Descendant preference reference subtree) :
    ∃ before after : List Entry,
      word reference preference = before ++ word subtree preference ++ after ∧
      (∀ e ∈ before, e.1 < c) ∧ (∀ e ∈ after, d ≤ e.1) ∧
      ∀ alternate : DepthSplit → Bool,
        (∀ split, split ∉ subtree.nodes → alternate split = preference split) →
        word reference alternate = before ++ word subtree alternate ++ after := by
  induction h with
  | refl reference => exact ⟨[],[],by simp,by simp,by simp,fun _ _ => by simp⟩
  | @left a b cut c d ha hb l r subtree bit below ih =>
    obtain ⟨before,after,hw,hbefore,hafter,hall⟩ := ih
    have bounds := below.bounds
    have hnot : (⟨a,cut,b⟩ : DepthSplit) ∉ subtree.nodes := by
      intro hm
      have hs := subtree.node_bounds hm
      simp only at hs
      omega
    refine ⟨before,after ++ [⟨cut,(⟨a,cut,b⟩,false)⟩],?_,hbefore,?_,?_⟩
    · simp only [word,bit,Bool.false_eq_true,if_false,hw,List.append_assoc]
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hafter e he
      · have heq := List.mem_singleton.mp he
        subst e
        exact bounds.2
    · intro alternate hagree
      have hp : alternate ⟨a,cut,b⟩ = false := (hagree _ hnot).trans bit
      simp only [word,hp,Bool.false_eq_true,if_false,hall alternate hagree,List.append_assoc]
  | @right a b cut c d ha hb l r subtree bit below ih =>
    obtain ⟨before,after,hw,hbefore,hafter,hall⟩ := ih
    have bounds := below.bounds
    have hnot : (⟨a,cut,b⟩ : DepthSplit) ∉ subtree.nodes := by
      intro hm
      have hs := subtree.node_bounds hm
      simp only at hs
      omega
    refine ⟨⟨cut,(⟨a,cut,b⟩,true)⟩ :: before,after,?_,?_,hafter,?_⟩
    · simp only [word,bit,if_true,hw,List.cons_append]
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · change cut < c
        omega
      · exact hbefore e he
    · intro alternate hagree
      have hp : alternate ⟨a,cut,b⟩ = true := (hagree _ hnot).trans bit
      simp only [word,hp,if_true,hall alternate hagree,List.cons_append]

end ChaCha.Paper20261030.SeparatorPath
