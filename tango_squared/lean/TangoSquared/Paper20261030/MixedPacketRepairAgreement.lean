import TangoSquared.Paper20261030.LocalMixedPacketRepair

set_option autoImplicit false

/-! The scalar repair plan agrees with the actual grouping produced by
repacking. This relation accounts for raw offsets and complete packets;
it also ensures the finite repair traversal fits the reached output.
The orientation of a real fork is supplied by the head's wing plan. -/

namespace TangoSquared.Paper20261030.MixedPacketRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α β ρ ι : Type*}

inductive Matches : Layers → Expression α ρ ι → Prop where
  | base : Matches .base .base
  | raw (records : Packet α ρ ι) (plan : Layers) (expression : Expression α ρ ι)
      (rest : Matches plan expression) : Matches (.raw records.length plan) (.raw records expression)
  | leaf (id : ι) (records : List ρ) (fields : Fields ι Unit) (plan : Layers) (expression : Expression α ρ ι)
      (rest : Matches plan expression) : Matches (.leaf plan) (.whole id records fields expression)
  | fork (reverse : Bool) (id : ι) (records : List ρ) (fields : Fields ι Unit) :
      Matches (.fork reverse) (.whole id records fields .base)
  | prefix (records : List ρ) : Matches .prefix (.prefix records)

theorem Matches.logical {plan : Layers} {expression : Expression α ρ ι}
    (same : Matches plan expression) (records : List ρ) : Matches plan (HeadPacketLayout.addLogical records expression) := by
  cases same with
  | base => exact .base
  | raw packets plan expression rest => exact .raw packets plan expression rest
  | leaf id tail fields plan expression rest => exact .leaf id (records++tail) fields plan expression rest
  | fork reverse id tail fields => exact .fork reverse id (records++tail) fields
  | «prefix» tail => exact .prefix (records++tail)

inductive TreeMatches : Source κ Layers → Source κ (Expression α ρ ι) → Prop where
  | leaf (key : κ) (plan : Layers) (expression : Expression α ρ ι) (same : Matches plan expression) :
      TreeMatches (.leaf key plan) (.leaf key expression)
  | fork (plan : Layers) (expression : Expression α ρ ι)
      (left right : Source κ Layers) (a b : Source κ (Expression α ρ ι))
      (same : Matches plan expression) (hl : TreeMatches left a) (hr : TreeMatches right b) :
      TreeMatches (.fork plan left right) (.fork expression a b)

theorem TreeMatches.shape {plan : Source κ Layers} {context : Source κ (Expression α ρ ι)}
    (same : TreeMatches plan context) : plan.shape = context.shape := by
  induction same <;> simp_all only [Source.shape]

theorem TreeMatches.root {plan : Source κ Layers} {context : Source κ (Expression α ρ ι)}
    (same : TreeMatches plan context) : Matches plan.rootRecord context.rootRecord := by
  cases same <;> assumption

theorem TreeMatches.repacked_fits {plan : Source κ Layers} {context : Source κ (Expression α ρ ι)}
    (same : TreeMatches plan context) (blocks : κ → Source β (Packet α ρ ι)) (source : Source β (Cell α ρ ι))
    (repacked : Reached.Repacked blocks context source) : Fits plan source := by
  induction same generalizing source with
  | leaf => trivial
  | fork plan expression left right a b same hl hr ihl ihr =>
    cases repacked with
    | fork _ _ _ l r id leftReady rightReady => exact ⟨ihl l leftReady,ihr r rightReady⟩

theorem TreeMatches.setRoot {plan : Source κ Layers} {context : Source κ (Expression α ρ ι)}
    (same : TreeMatches plan context) (newPlan : Layers) (expression : Expression α ρ ι) (root : Matches newPlan expression) :
    TreeMatches (plan.setRoot newPlan) (context.setRoot expression) := by
  cases same with
  | leaf key oldPlan oldExpression old => exact .leaf key newPlan expression root
  | fork oldPlan oldExpression left right a b old hl hr => exact .fork newPlan expression left right a b root hl hr

theorem TreeMatches.logical {plan : Source κ Layers} {context : Source κ (Expression α ρ ι)}
    (same : TreeMatches plan context) (records : List ρ) :
    TreeMatches plan (context.setRoot (HeadPacketLayout.addLogical records context.rootRecord)) := by
  cases same with
  | leaf key plan expression root => exact .leaf key plan _ (root.logical records)
  | fork plan expression left right a b root hl hr => exact .fork plan _ left right a b (root.logical records) hl hr

def LayoutMatches : Option (Source κ Layers) → HeadPacketLayout.Layout κ α ρ ι → Prop
  | none,none => True
  | some plan,some context => TreeMatches plan context
  | _,_ => False

end TangoSquared.Paper20261030.MixedPacketRepair
