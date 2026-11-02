import MultiSplay.AuxiliarySplay
import Mathlib.Data.List.Induction

/-!
# Splaying a sparse component by actual pointer operations

An ancestor list is the existing pointer model's zipper: each frame stores a
parent and the untouched sibling subtree. Its length is the selected key's
depth. `exists_from_cursor` performs the standard bottom-up splay on any such
zipper. Every rotation costs two pointer operations, including the adjacent
moves. The root-starting execution additionally pays for the initial descent.
No consecutive-key encoding or assumption about the component alphabet is used.
-/

namespace MultiSplay.Auxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)
open ChaCha.MTR.Pointer (Frame plug Cursor)

variable {α : Type*}

theorem Double.plug {key : α} {a b : RawTree α} (step : Double key a b)
    (ancestors : List (Frame α)) : Double key (plug a ancestors) (plug b ancestors) := by
  induction ancestors generalizing a b with
  | nil => exact step
  | cons frame rest ih =>
      cases frame with
      | left parent sibling => exact ih (step.leftContext parent sibling)
      | right sibling parent => exact ih (step.rightContext sibling parent)

/-- A selected occurrence can be exposed as a genuine cursor. With distinct
keys this is the ordinary unique search location. -/
theorem exists_cursor {tree : RawTree α} {key : α} (member : key ∈ inorder tree) :
    ∃ l r ancestors, tree = plug (.node l key r) ancestors := by
  induction tree with
  | empty => simp [inorder] at member
  | node l pivot r ihl ihr =>
      simp only [inorder, List.mem_append, List.mem_singleton] at member
      rcases member with (inLeft | rfl) | inRight
      · obtain ⟨a, b, ancestors, same⟩ := ihl inLeft
        refine ⟨a, b, ancestors ++ [.left pivot r], ?_⟩
        subst l
        have plug_append : ∀ (frames : List (Frame α)) (focus : RawTree α),
            plug focus (frames ++ [.left pivot r]) = .node (plug focus frames) pivot r := by
          intro frames
          induction frames with
          | nil => intro focus; rfl
          | cons frame rest ih => intro focus; cases frame <;> exact ih _
        exact (plug_append ancestors _).symm
      · exact ⟨l, r, [], rfl⟩
      · obtain ⟨a, b, ancestors, same⟩ := ihr inRight
        refine ⟨a, b, ancestors ++ [.right l pivot], ?_⟩
        subst r
        have plug_append : ∀ (frames : List (Frame α)) (focus : RawTree α),
            plug focus (frames ++ [.right l pivot]) = .node l pivot (plug focus frames) := by
          intro frames
          induction frames with
          | nil => intro focus; rfl
          | cons frame rest ih => intro focus; cases frame <;> exact ih _
        exact (plug_append ancestors _).symm

/-- Descend along the actual ancestor path, paying once for each edge. -/
theorem descend (l r : RawTree α) (key : α) (ancestors outer : List (Frame α)) :
    ChaCha.MTR.Pointer.Trace ⟨plug (.node l key r) ancestors, outer⟩ []
      ⟨.node l key r, ancestors ++ outer⟩ ancestors.length := by
  induction ancestors generalizing l r key outer with
  | nil => exact .nil _
  | cons frame rest ih =>
      cases frame with
      | left parent sibling =>
          have first := ih (.node l key r) sibling parent outer
          have last := ChaCha.MTR.Pointer.Trace.step
            (.left l r sibling key parent (rest ++ outer)) (.nil _)
          simpa [plug, List.cons_append] using
            ChaCha.Paper20261030.Auxiliary.trace_append first last
      | right sibling parent =>
          have first := ih sibling (.node l key r) parent outer
          have last := ChaCha.MTR.Pointer.Trace.step
            (.right sibling l r parent key (rest ++ outer)) (.nil _)
          simpa [plug, List.cons_append] using
            ChaCha.Paper20261030.Auxiliary.trace_append first last

/-- The usual zig, zig-zig and zig-zag cases, with the pointer initially at
the accessed key. Untouched siblings are preserved literally. -/
theorem exists_from_cursor (l r : RawTree α) (key : α)
    (ancestors : List (Frame α)) :
    ∃ after,
      Splay key (plug (.node l key r) ancestors) after ancestors.length ∧
      ∀ outer : List (Frame α),
      ChaCha.MTR.Pointer.Trace ⟨.node l key r, ancestors ++ outer⟩ []
        ⟨after, outer⟩ (2 * ancestors.length) := by
  induction ancestors using List.twoStepInduction generalizing l r with
  | nil => exact ⟨.node l key r, .done l r, fun _ => .nil _⟩
  | singleton first =>
    cases first with
    | left parent sibling =>
        refine ⟨.node l key (.node r parent sibling), ?_, ?_⟩
        · simpa [plug] using Splay.next (.zigLeft l r sibling parent) (.done _ _)
        · intro outer
          exact .step (.upLeft _ _ _ _)
            (.step (.rotateRight _ _ _ _ _ _) (.nil _))
    | right sibling parent =>
        refine ⟨.node (.node sibling parent l) key r, ?_, ?_⟩
        · simpa [plug] using Splay.next (.zigRight sibling l r parent) (.done _ _)
        · intro outer
          exact .step (.upRight _ _ _ _)
            (.step (.rotateLeft _ _ _ _ _ _) (.nil _))
  | cons_cons first second above ih _ =>
    cases first with
    | left parent sibling =>
        cases second with
        | left grandparent uncle =>
            obtain ⟨after, run, moves⟩ :=
              ih l (.node r parent (.node sibling grandparent uncle))
            refine ⟨after, ?_, ?_⟩
            · convert (
                Splay.next ((Double.leftLeft l r sibling uncle parent grandparent).plug above |> Step.double) run) using 1 <;>
                  simp only [plug, List.length_cons] <;> omega
            · intro outer
              have firstMoves := ChaCha.MTR.Pointer.Trace.step (.upLeft _ _ _ _)
                (.step (.upLeft _ _ _ _) (.step (.rotateRight _ _ _ _ _ _)
                  (.step (.rotateRight _ _ _ _ _ _) (moves outer))))
              simpa [List.cons_append, Nat.mul_add, Nat.add_assoc] using firstMoves
        | right uncle grandparent =>
            obtain ⟨after, run, moves⟩ :=
              ih (.node uncle grandparent l) (.node r parent sibling)
            refine ⟨after, ?_, ?_⟩
            · convert (
                Splay.next ((Double.rightLeft uncle l r sibling grandparent parent).plug above |> Step.double) run) using 1 <;>
                  simp only [plug, List.length_cons] <;> omega
            · intro outer
              have firstMoves := ChaCha.MTR.Pointer.Trace.step (.upLeft _ _ _ _)
                (.step (.rotateRight _ _ _ _ _ _) (.step (.upRight _ _ _ _)
                  (.step (.rotateLeft _ _ _ _ _ _) (moves outer))))
              simpa [List.cons_append, Nat.mul_add, Nat.add_assoc] using firstMoves
    | right sibling parent =>
        cases second with
        | left grandparent uncle =>
            obtain ⟨after, run, moves⟩ :=
              ih (.node sibling parent l) (.node r grandparent uncle)
            refine ⟨after, ?_, ?_⟩
            · convert (
                Splay.next ((Double.leftRight sibling l r uncle parent grandparent).plug above |> Step.double) run) using 1 <;>
                  simp only [plug, List.length_cons] <;> omega
            · intro outer
              have firstMoves := ChaCha.MTR.Pointer.Trace.step (.upRight _ _ _ _)
                (.step (.rotateLeft _ _ _ _ _ _) (.step (.upLeft _ _ _ _)
                  (.step (.rotateRight _ _ _ _ _ _) (moves outer))))
              simpa [List.cons_append, Nat.mul_add, Nat.add_assoc] using firstMoves
        | right uncle grandparent =>
            obtain ⟨after, run, moves⟩ :=
              ih (.node (.node uncle grandparent sibling) parent l) r
            refine ⟨after, ?_, ?_⟩
            · convert (
                Splay.next ((Double.rightRight uncle sibling l r grandparent parent).plug above |> Step.double) run) using 1 <;>
                  simp only [plug, List.length_cons] <;> omega
            · intro outer
              have firstMoves := ChaCha.MTR.Pointer.Trace.step (.upRight _ _ _ _)
                (.step (.upRight _ _ _ _) (.step (.rotateLeft _ _ _ _ _ _)
                  (.step (.rotateLeft _ _ _ _ _ _) (moves outer))))
              simpa [List.cons_append, Nat.mul_add, Nat.add_assoc] using firstMoves

/-- Total correctness on arbitrary component alphabets. The splay rotates
exactly once per initial path edge; search, rotations and serving cost `3*d+1`.
The final cursor is the component root, in any surrounding physical context. -/
theorem exists_pointer_splay {tree : RawTree α} {key : α} (member : key ∈ inorder tree) :
    ∃ after depth,
      Splay key tree after depth ∧
      ∀ outer : List (Frame α),
        ChaCha.MTR.Pointer.Trace ⟨tree, outer⟩ [key] ⟨after, outer⟩ (3 * depth + 1) := by
  obtain ⟨l, r, ancestors, rfl⟩ := exists_cursor member
  obtain ⟨after, run, moves⟩ := exists_from_cursor l r key ancestors
  refine ⟨after, ancestors.length, run, ?_⟩
  intro outer
  have serve : ChaCha.MTR.Pointer.Trace ⟨after, outer⟩ [key] ⟨after, outer⟩ 1 :=
    .serve run.root_after (.nil _)
  have result := ChaCha.Paper20261030.Auxiliary.trace_append (descend l r key ancestors outer)
    (ChaCha.Paper20261030.Auxiliary.trace_append (moves outer) serve)
  have arithmetic : ancestors.length + (2 * ancestors.length + 1) =
      3 * ancestors.length + 1 := by omega
  simpa only [List.nil_append, arithmetic] using result

end MultiSplay.Auxiliary
