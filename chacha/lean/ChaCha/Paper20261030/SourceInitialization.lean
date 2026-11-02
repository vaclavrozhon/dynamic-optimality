import ChaCha.Paper20261030.SourceReversal
import ChaCha.Paper20261030.ComponentInitialization

/-!
# Linear initialization in the decorated source-pointer model

Two full leaf trees with the same ordered leaf word can be transformed
into one another in linear pointer cost, including record writes. We
rotate each tree into a right spine with fixed records. A rotation adds
one vertex to that spine; advancing along the spine costs a constant.
This is a trace existence theorem. Acquiring the target records by a
bounded local initialization program is a separate requirement.
-/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage RouterProjection

variable {α ρ : Type*}

def rightSpine : Source α ρ → Nat
  | .leaf _ _ => 0
  | .fork _ _ right => rightSpine right + 1

private def leftCount : Source α ρ → Nat
  | .leaf _ _ => 0
  | .fork _ left _ => left.internalCount

theorem rightSpine_le (tree : Source α ρ) : rightSpine tree ≤ tree.internalCount := by
  induction tree <;> simp_all [rightSpine,Source.internalCount] <;> omega

theorem source_leaves_length (tree : Source α ρ) : tree.shape.leaves.length = tree.internalCount + 1 := by
  induction tree <;> simp_all [Source.shape,Router.leaves,Source.internalCount] <;> omega

inductive Normal (record : ρ) : Source α ρ → Prop
  | leaf (key : α) : Normal record (.leaf key record)
  | cons (key : α) {tail : Source α ρ} (rest : Normal record tail) :
      Normal record (.fork record (.leaf key record) tail)

theorem Normal.unique {record : ρ} {before after : Source α ρ}
    (first : Normal record before) (last : Normal record after)
    (words : before.shape.leaves = after.shape.leaves) : before = after := by
  induction first generalizing after with
  | leaf key =>
    cases last with
    | leaf other =>
      simp only [Source.shape,Router.leaves,List.singleton_inj] at words
      subst other
      rfl
    | @cons other tail rest =>
      have lengths := congrArg List.length words
      have positive := source_leaves_length tail
      simp only [Source.shape,Router.leaves,List.length_append,List.length_singleton] at lengths
      omega
  | @cons key tail rest ih =>
    cases last with
    | leaf other =>
      have lengths := congrArg List.length words
      have positive := source_leaves_length tail
      simp only [Source.shape,Router.leaves,List.length_append,List.length_singleton] at lengths
      omega
    | @cons other next nextNormal =>
      simp only [Source.shape,Router.leaves,List.singleton_append,List.cons.injEq] at words
      obtain ⟨rfl,tailWords⟩ := words
      rw [ih nextNormal tailWords]

theorem normalize_source (record : ρ) (tree : Source α ρ) :
    ∃ out, Normal record out ∧ out.shape.leaves = tree.shape.leaves ∧
      Rearranges tree out (7*tree.internalCount-rightSpine tree+1) := by
  cases tree with
  | leaf key old =>
    refine ⟨.leaf key record,.leaf key,rfl,?_⟩
    exact fun outside => ⟨[],1,.step (.write _ _ _) (.nil _),by simp [Source.internalCount,rightSpine]⟩
  | fork old left right =>
    cases left with
    | leaf key oldLeaf =>
      obtain ⟨out,normal,word,run⟩ := normalize_source record right
      have writeRoot : Rearranges (.fork old (.leaf key oldLeaf) right)
          (.fork record (.leaf key oldLeaf) right) 1 :=
        fun outside => ⟨[],1,.step (.write _ _ _) (.nil _),le_rfl⟩
      have writeLeaf : Rearranges (.leaf key oldLeaf) (.leaf key record) 1 :=
        fun outside => ⟨[],1,.step (.write _ _ _) (.nil _),le_rfl⟩
      refine ⟨.fork record (.leaf key record) out,.cons key normal,?_,?_⟩
      · simp only [Source.shape,Router.leaves,word]
      · apply ((writeRoot.trans writeLeaf.left).trans run.right).mono
        have spineBound := rightSpine_le right
        simp only [Source.internalCount,rightSpine]
        omega
    | fork pivot a b =>
      obtain ⟨out,normal,word,run⟩ := normalize_source record (.fork pivot a (.fork old b right))
      have rotate : Rearranges (.fork old (.fork pivot a b) right) (.fork pivot a (.fork old b right)) 1 :=
        fun outside => ⟨[],1,.step (.rotateRight _ _ _ _ _ _) (.nil _),le_rfl⟩
      refine ⟨out,normal,?_,(rotate.trans run).mono ?_⟩
      · simpa only [Source.shape,Router.leaves,List.append_assoc] using word
      · have spineBound := rightSpine_le right
        simp only [Source.internalCount,rightSpine]
        omega
termination_by (tree.internalCount,leftCount tree)
decreasing_by all_goals simp [Source.internalCount,leftCount]; omega

theorem initialize_source (before after : Source α ρ)
    (word : before.shape.leaves = after.shape.leaves) :
    Rearranges before after (14*before.shape.leaves.length) := by
  obtain ⟨first,firstNormal,firstWord,firstRun⟩ := normalize_source before.rootRecord before
  obtain ⟨last,lastNormal,lastWord,lastRun⟩ := normalize_source before.rootRecord after
  have equal := firstNormal.unique lastNormal (firstWord.trans (word.trans lastWord.symm))
  subst last
  apply (firstRun.trans lastRun.symm).mono
  have beforeLength := source_leaves_length before
  have afterLength := source_leaves_length after
  have lengths := congrArg List.length word
  omega

end ChaCha.Paper20261030.SourcePointer
