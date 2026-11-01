import MultiSplay.ClassicalSwitchLocalization

/-! # Canonical hole addresses occur exactly once -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open EndpointEncoding

variable {α : Type*}

theorem preferredHoles_addresses_nodup (state : State) (reference : RawTree α) :
    ((preferredHoles state reference).map Prod.fst).Nodup := by
  induction reference generalizing state with
  | empty => simp [preferredHoles]
  | node left pivot right ihl ihr =>
      have leftUnique := (ihl (below state false)).map (f := List.cons false) (fun _ _ same => (List.cons.inj same).2)
      have rightUnique := (ihr (below state true)).map (f := List.cons true) (fun _ _ same => (List.cons.inj same).2)
      cases side : state [] with
      | false =>
          simpa [preferredHoles, side, prefixHoles, List.map_map, Function.comp_def,
            List.nodup_append', List.disjoint_left] using leftUnique
      | true =>
          simpa [preferredHoles, side, prefixHoles, List.map_map, Function.comp_def] using rightUnique

theorem preferredHoles_nodup (state : State) (reference : RawTree α) :
    (preferredHoles state reference).Nodup :=
  (preferredHoles_addresses_nodup state reference).of_map Prod.fst

end MultiSplay.ClassicalSwitch
