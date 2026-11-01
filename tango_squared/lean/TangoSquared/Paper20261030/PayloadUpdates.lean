import TangoSquared.Paper20261030.ChargedInsertion

/-!
# Charged changes to the payload of an exposed auxiliary key

The key, children, and cached size remain fixed. One read observes the
old record; one write stores the updated payload at that same vertex.
The caller supplies the local payload function. Its computation must be
accounted for by the application, rather than inferred from this trace.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {α : Type*} {β : α → Type*}

theorem updateValue_charged (size : Nat) (key : α) (old : β key)
    (f : β key → β key) (l r : Impl α β) (ancestors) :
    Trace ⟨recordTree (.inner size key old l r),ancestors⟩ [(size,⟨key,old⟩)]
      ⟨recordTree (.inner size key (f old) l r),ancestors⟩ 2 :=
  .read rfl (.step (.writeValue (recordTree l) (recordTree r) size key old (f old) ancestors) (.nil _))

theorem updateValue_observed (size : Nat) (key : α) (old : β key)
    (f : β key → β key) (l r : Impl α β) :
    ObservedRearranges (.inner size key old l r) (.inner size key (f old) l r) 2 :=
  fun ancestors => ⟨_,2,updateValue_charged size key old f l r ancestors,le_rfl⟩

/-- An application field update preserves every key and all routing. -/
theorem updateValue_erase (size : Nat) (key : α) (old fresh : β key) (l r : Impl α β) :
    erase (.inner size key old l r) = erase (.inner size key fresh l r) := rfl

end TangoSquared.Paper20261030.Auxiliary.Metadata
