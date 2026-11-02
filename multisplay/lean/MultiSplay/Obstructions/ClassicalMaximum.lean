import MultiSplay.Obstructions.ClassicalPotentialCore

/-! Splaying the maximum of a tree whose right spine is left-heavy
cannot decrease the classical potential. The proof constructs the actual
bottom-up doubles and optional final zig, including their exact count. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree

variable {α : Type*}

inductive MaxSpine (key : α) : RawTree α → Nat → Prop
  | root (left : RawTree α) : MaxSpine key (.node left key .empty) 0
  | right {tree : RawTree α} {depth : Nat} (left : RawTree α) (root : α)
      (tail : MaxSpine key tree depth) : MaxSpine key (.node left root tree) (depth+1)

/-- All doubles are performed first. The only remaining operation is at
most one genuine root zig; no interior single rotation is introduced. -/
theorem MaxSpine.doubles {key : α} {tree : RawTree α} {depth : Nat} (spine : MaxSpine key tree depth) :
    ∃ (out : RawTree α) (count : Nat), MaxDoubles key tree out count ∧
      ((∃ left, out = .node left key .empty ∧ depth = 2*count) ∨
       (∃ left root child, out = .node left root (.node child key .empty) ∧ depth = 2*count+1)) := by
  induction spine with
  | root left => exact ⟨_,0,.refl _,Or.inl ⟨left,rfl,rfl⟩⟩
  | right left root tail ih =>
    obtain ⟨out,count,trace,shape⟩ := ih
    rcases shape with ⟨child,rfl,equal⟩ | ⟨a,x,b,rfl,equal⟩
    · exact ⟨_,count,trace.right left root,Or.inr ⟨left,root,child,rfl,by omega⟩⟩
    · refine ⟨_,count+1,(trace.right left root).append (.step (.root left a b root x) (.refl _)),
        Or.inl ⟨_,rfl,?_⟩⟩
      omega

 theorem MaxSpine.splay_nondecrease {key : α} {tree : RawTree α} {depth : Nat}
    (spine : MaxSpine key tree depth) (heavy : RightHeavy tree) :
    ∃ left, Auxiliary.Splay key tree (.node left key .empty) depth ∧
      potential tree ≤ potential (.node left key .empty) := by
  obtain ⟨out,count,trace,shape⟩ := spine.doubles
  have monotone := trace.potential heavy
  rcases shape with ⟨left,rfl,equal⟩ | ⟨a,x,b,rfl,equal⟩
  · exact ⟨left,by simpa only [equal] using trace.finish,monotone⟩
  · have last : Auxiliary.Splay key (.node a x (.node b key .empty))
        (.node (.node a x b) key .empty) 1 := .next (.zigRight a b .empty x) (.done _ _)
    exact ⟨.node a x b,by simpa only [equal] using trace.follow last,monotone.trans (zig_nondecrease a b x key)⟩

end MultiSplay.Obstructions.Classical
