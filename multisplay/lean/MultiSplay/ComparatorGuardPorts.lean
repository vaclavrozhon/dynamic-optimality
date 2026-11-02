import MultiSplay.ComparatorGuardFrame
import MultiSplay.ComparatorGuardExposed

/-! # Indexed reference paths determine all retained projection ports -/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality ChaCha Paper20261030
open EndpointEncoding ClassicalSwitch ColoredStorage PreferredProjection PrimaryWings
open ComparatorPrimary (routing signature lastGap)
open Primary (Key)

/-- A preferred reference path retaining the indexed interval of its focus. -/
inductive IndexedPath : {lo hi : Nat} → State → BST lo hi → Key → Spine Nat →
    {bottom top : Nat} → BST bottom top → Prop
  | here {lo hi} (state : State) (reference : BST lo hi) :
      IndexedPath state reference [] [] reference
  | left {lo key hi bottom top} {state : State} {left : BST lo key} {right : BST (key+1) hi}
      {address : Key} {spine : Spine Nat} {focus : BST bottom top}
      (agrees : state [] = false)
      (rest : IndexedPath (below state false) left address spine focus) :
      IndexedPath state (.node left right) (false::address) (spine++[(false,key)]) focus
  | right {lo key hi bottom top} {state : State} {left : BST lo key} {right : BST (key+1) hi}
      {address : Key} {spine : Spine Nat} {focus : BST bottom top}
      (agrees : state [] = true)
      (rest : IndexedPath (below state true) right address spine focus) :
      IndexedPath state (.node left right) (true::address) (spine++[(true,key)]) focus

theorem IndexedPath.raw {lo hi bottom top : Nat} {state : State} {reference : BST lo hi}
    {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus) :
    ClassicalSwitch.Path state reference.toRaw address spine focus.toRaw := by
  induction path with
  | here => exact .here _ _
  | left agrees rest ih => exact .left agrees ih
  | right agrees rest ih => exact .right agrees ih

/-- Every actual preferred address has an indexed focus, including empty
reference children. This relation adds no representation hypothesis. -/
theorem indexedPath_exists {lo hi : Nat} (state : State) (reference : BST lo hi)
    (address : Key) (follows : RootPreferred state address)
    (valid : address.length ≤ (ComparatorForest.finish state reference.toRaw).length) :
    ∃ (bottom top : Nat) (focus : BST bottom top) (spine : Spine Nat),
      IndexedPath state reference address spine focus := by
  induction reference generalizing state address with
  | empty boundary =>
      cases address with
      | nil => exact ⟨boundary,boundary,.empty boundary,[],.here _ _⟩
      | cons => simp [ComparatorForest.finish,BST.toRaw] at valid
  | @node lo key hi left right ihl ihr =>
      cases address with
      | nil => exact ⟨lo,hi,.node left right,[],.here _ _⟩
      | cons edge address =>
          obtain ⟨agrees,follows⟩ := (rootPreferred_cons state edge address).mp follows
          cases edge with
          | false =>
              have childValid : address.length ≤ (ComparatorForest.finish (below state false) (BST.toRaw left)).length := by
                simpa [BST.toRaw,ComparatorForest.finish,agrees] using valid
              obtain ⟨bottom,top,focus,spine,path⟩ := ihl (below state false) address follows childValid
              exact ⟨bottom,top,focus,spine++[(false,key)],.left agrees path⟩
          | true =>
              have childValid : address.length ≤ (ComparatorForest.finish (below state true) (BST.toRaw right)).length := by
                simpa [BST.toRaw,ComparatorForest.finish,agrees] using valid
              obtain ⟨bottom,top,focus,spine,path⟩ := ihr (below state true) address follows childValid
              exact ⟨bottom,top,focus,spine++[(true,key)],.right agrees path⟩

/-- A canonical raw reference path has the same actual indexed focus. -/
theorem indexedPath_of_raw {lo hi : Nat} (reference : BST lo hi)
    {state : State} {address : Key} {spine : Spine Nat} {focus : RawTree Nat}
    (path : ClassicalSwitch.Path state reference.toRaw address spine focus) :
    ∃ (bottom top : Nat) (indexed : BST bottom top),
      IndexedPath state reference address spine indexed ∧ indexed.toRaw = focus := by
  induction reference generalizing state address spine focus with
  | empty boundary =>
      cases path
      exact ⟨boundary,boundary,.empty boundary,.here _ _,rfl⟩
  | @node lo key hi left right ihl ihr =>
      cases path with
      | here => exact ⟨lo,hi,.node left right,.here _ _,rfl⟩
      | left agrees rest =>
          obtain ⟨bottom,top,indexed,child,same⟩ := ihl rest
          exact ⟨bottom,top,indexed,.left agrees child,same⟩
      | right agrees rest =>
          obtain ⟨bottom,top,indexed,child,same⟩ := ihr rest
          exact ⟨bottom,top,indexed,.right agrees child,same⟩

/-- Prefix signatures are in root-to-focus order. Each entry stores its
exit side and the actual upper boundary of that opaque reference child. -/
theorem IndexedPath.signatures {lo hi bottom top : Nat} {state : State} {reference : BST lo hi}
    {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus) :
    ∃ front : List (Bool × Nat), front.length = address.length ∧
      signature (routing state reference) = front ++ signature (routing (restrict state address) focus) ∧
      signature (routing (toggle state address) reference) =
        front ++ signature (routing (toggle (restrict state address) []) focus) ∧
      (routing state reference).terminal = (routing (restrict state address) focus).terminal ∧
      (routing (toggle state address) reference).terminal =
        (routing (toggle (restrict state address) []) focus).terminal := by
  induction path with
  | here state reference => exact ⟨[],rfl,rfl,rfl,rfl,rfl⟩
  | @left lo key hi bottom top state left right address spine focus agrees rest ih =>
      obtain ⟨front,length,old,fresh,oldTerminal,freshTerminal⟩ := ih
      refine ⟨(false,hi)::front,by simp [length],?_,?_,?_,?_⟩
      · simpa only [routing,agrees,signature,exits,List.map_cons,ComparatorPrimary.lastGap_routing,
          restrict,List.cons_append] using congrArg (List.cons (false,hi)) old
      · have root : toggle state (false::address) [] = false := by simp [toggle,agrees]
        simpa only [routing,root,signature,exits,List.map_cons,ComparatorPrimary.lastGap_routing,
          below_toggle_cons,restrict,List.cons_append] using congrArg (List.cons (false,hi)) fresh
      · simpa [routing,agrees,PrefRouter.terminal,restrict] using oldTerminal
      · have root : toggle state (false::address) [] = false := by simp [toggle,agrees]
        simpa [routing,root,PrefRouter.terminal,below_toggle_cons,restrict] using freshTerminal
  | @right lo key hi bottom top state left right address spine focus agrees rest ih =>
      obtain ⟨front,length,old,fresh,oldTerminal,freshTerminal⟩ := ih
      refine ⟨(true,key)::front,by simp [length],?_,?_,?_,?_⟩
      · simpa only [routing,agrees,signature,exits,List.map_cons,ComparatorPrimary.lastGap_routing,
          restrict,List.cons_append] using congrArg (List.cons (true,key)) old
      · have root : toggle state (true::address) [] = true := by simp [toggle,agrees]
        simpa only [routing,root,signature,exits,List.map_cons,ComparatorPrimary.lastGap_routing,
          below_toggle_cons,restrict,List.cons_append] using congrArg (List.cons (true,key)) fresh
      · simpa [routing,agrees,PrefRouter.terminal,restrict] using oldTerminal
      · have root : toggle state (true::address) [] = true := by simp [toggle,agrees]
        simpa [routing,root,PrefRouter.terminal,below_toggle_cons,restrict] using freshTerminal

end MultiSplay.ComparatorGuard
