import DynamicOptimality.Cost

/-!
# The common offline optimum is a lower bound for pointer execution cost

The proof reuses Cha-Cha's checked conversion from adjacent pointer accesses
to rooted hulls and then to shallow rotations with marked root requests.
Each shallow rotation is lifted to the existing indexed BST type used by
the splay optimum. No new optimum or execution-cost annotation is assumed.
-/

namespace DynamicOptimality

open ChaCha ChaCha.MTR

theorem restricted_lift {a b : RawTree Nat} (step : MTR.Tree.RestrictedStep a b)
    {lower upper : Nat} (t : BST lower upper) (ht : t.toRaw = a) :
    ∃ (u : BST lower upper) (depth : Nat),
      Splay.Tree.BST.RotationAt depth t u ∧ u.toRaw = b := by
  cases step with
  | rootRight a b c x y =>
    cases t with
    | empty => contradiction
    | node l r =>
      cases l with
      | empty => cases ht
      | node ll lr =>
        simp only [BST.toRaw,MTR.Tree.node.injEq] at ht
        rcases ht with ⟨⟨ha,rfl,hb⟩,rfl,hc⟩
        exact ⟨.node ll (.node lr r),0,.root (.right ll lr r),by simp [BST.toRaw,ha,hb,hc]⟩
  | rootLeft a b c x y =>
    cases t with
    | empty => contradiction
    | node l r =>
      cases r with
      | empty => cases ht
      | node rl rr =>
        simp only [BST.toRaw,MTR.Tree.node.injEq] at ht
        rcases ht with ⟨ha,rfl,⟨hb,rfl,hc⟩⟩
        exact ⟨.node (.node l rl) rr,0,.root (.left l rl rr),by simp [BST.toRaw,ha,hb,hc]⟩
  | rightRight a b c d x y z =>
    cases t with
    | empty => contradiction
    | node l r =>
      cases r with
      | empty => cases ht
      | node rl rr =>
        cases rl with
        | empty => cases ht
        | node rll rlr =>
          simp only [BST.toRaw,MTR.Tree.node.injEq] at ht
          rcases ht with ⟨ha,rfl,⟨⟨hb,rfl,hc⟩,rfl,hd⟩⟩
          exact ⟨.node l (.node rll (.node rlr rr)),1,
            .rightContext l (.root (.right rll rlr rr)),by simp [BST.toRaw,ha,hb,hc,hd]⟩
  | rightLeft a b c d x y z =>
    cases t with
    | empty => contradiction
    | node l r =>
      cases r with
      | empty => cases ht
      | node rl rr =>
        cases rr with
        | empty => cases ht
        | node rrl rrr =>
          simp only [BST.toRaw,MTR.Tree.node.injEq] at ht
          rcases ht with ⟨ha,rfl,⟨hb,rfl,⟨hc,rfl,hd⟩⟩⟩
          exact ⟨.node l (.node (.node rl rrl) rrr),1,
            .rightContext l (.root (.left rl rrl rrr)),by simp [BST.toRaw,ha,hb,hc,hd]⟩
  | leftRight a b c d x y z =>
    cases t with
    | empty => contradiction
    | node l r =>
      cases l with
      | empty => cases ht
      | node ll lr =>
        cases ll with
        | empty => cases ht
        | node lll llr =>
          simp only [BST.toRaw,MTR.Tree.node.injEq] at ht
          rcases ht with ⟨⟨⟨ha,rfl,hb⟩,rfl,hc⟩,rfl,hd⟩
          exact ⟨.node (.node lll (.node llr lr)) r,1,
            .leftContext (.root (.right lll llr lr)) r,by simp [BST.toRaw,ha,hb,hc,hd]⟩
  | leftLeft a b c d x y z =>
    cases t with
    | empty => contradiction
    | node l r =>
      cases l with
      | empty => cases ht
      | node ll lr =>
        cases lr with
        | empty => cases ht
        | node lrl lrr =>
          simp only [BST.toRaw,MTR.Tree.node.injEq] at ht
          rcases ht with ⟨⟨ha,rfl,⟨hb,rfl,hc⟩⟩,rfl,hd⟩
          exact ⟨.node (.node (.node ll lrl) lrr) r,1,
            .leftContext (.root (.left ll lrl lrr)) r,by simp [BST.toRaw,ha,hb,hc,hd]⟩

theorem toRaw_hasRoot {lower upper key : Nat} (t : BST lower upper)
    (ht : MTR.Tree.rootKey t.toRaw = some key) : t.HasRoot key := by
  cases t with
  | empty => contradiction
  | node l r =>
    have he := Option.some.inj ht
    subst key
    exact ⟨l,r,rfl⟩

/-- Trailing rotations can be discarded after the last request. -/
theorem marked_to_offline {a b : RawTree Nat} {word : List Nat} {cost : Nat}
    (trace : MarkedTrace a word b cost) {n : Nat} (t : BST 0 n) (ht : t.toRaw = a)
    (requests : List (Fin n)) (hw : requests.map Fin.val = word) :
    ∃ (u : BST 0 n) (rotations : Nat),
      OfflineExecution requests t u rotations ∧ rotations ≤ cost := by
  induction trace generalizing t requests with
  | nil =>
    have he : requests = [] := by simpa using hw
    subst requests
    exact ⟨t,0,.done t,le_rfl⟩
  | rotate step rest ih =>
    obtain ⟨middle,depth,rotation,hm⟩ := restricted_lift step t ht
    obtain ⟨u,rotations,execution,hc⟩ := ih middle hm requests hw
    by_cases hn : requests = []
    · subst requests
      exact ⟨t,0,.done t,Nat.zero_le _⟩
    · refine ⟨u,1 + rotations,?_,by omega⟩
      exact Splay.Accounting.OfflineOptimum.Execution.prependRotations hn
        (.singleton rotation) execution
  | serve atRoot rest ih =>
    cases requests with
    | nil => simp at hw
    | cons request requests =>
      obtain ⟨hk,hrest⟩ := List.cons.inj hw
      obtain ⟨u,rotations,execution,hc⟩ := ih t ht requests hrest
      have root : t.HasRoot request.val := toRaw_hasRoot t (by simpa [ht,hk] using atRoot)
      exact ⟨u,rotations,by simpa using Splay.Accounting.OfflineOptimum.Execution.next .refl root execution,hc⟩

/-- A concrete ordinary BST pointer execution pays the same attained OPT
used by the splay theorem, up to a universal factor. -/
theorem OPT_le_pointer_cost {n cost : Nat} (initial : BST 0 n)
    {final : RawTree Nat} (requests : List (Fin n))
    (execution : PointerExecution initial.toRaw (requests.map Fin.val) final cost) :
    OPT requests ≤ 13 * cost := by
  obtain ⟨hullCost,hhull,hull⟩ := execution.toAccessExecution
  obtain ⟨rotations,hr,trace⟩ := hull.marked_trace initial.toRaw_ordered
  obtain ⟨last,rc,offline,hc⟩ := marked_to_offline trace initial rfl requests rfl
  have minimum := OPT_le_execution offline
  have length := hull.length_le_cost
  simp only [List.length_map] at length
  omega

end DynamicOptimality
