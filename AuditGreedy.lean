import Greedy
import Lean

/-! Dependency audits for the shared Greedy development.
`Greedy.competitive` proves the unconditional target for actual geometric
Greedy cost and the common attained optimum. The complete namespace audit
below includes private declarations and rejects every nonstandard axiom. -/

#check Greedy.Target
#check Greedy.competitive
#print axioms Greedy.competitive
#print axioms Greedy.bounded_comparison
#print axioms Greedy.cost_le_bounded_trace
#print axioms Greedy.execution_link_bound
#print axioms Greedy.TicketJournal.access_remaining
#print axioms Greedy.TicketJournal.links_correct
#print axioms Greedy.LinearLedger.with_initial_credit
#print axioms GreedyMerge.ActualLinks.actual_access_returns_canonical
#print axioms GreedyForest.Execution.AccountingTrace.activity_le_quadratic
#print axioms Greedy.twice_costFrom
#print axioms Greedy.actual_access_link_count
#print axioms Greedy.Execution.exists_shared_run
#print axioms Greedy.RunJournal.exists_journal
#print axioms Greedy.InitializedRun.exists_journal
#print axioms Greedy.RestorationJournal.stored_snapshot
#print axioms Greedy.RotationJournal.complete_rotation
#print axioms Greedy.AccessJournal.actual_prefix
#print axioms Greedy.GrowthJournal.initialized_books
#print axioms Greedy.GrowthJournal.initialized_history
#print axioms Greedy.GrowthJournal.initialized_all_sources
#print axioms Greedy.GrowthJournal.activeNames_card
#print axioms Greedy.GrowthJournal.Covered.nonzero_name
#print axioms Greedy.LabelHistory.difference
#print axioms Greedy.LabelSnapshots.initialized_sound
#print axioms Greedy.LabelSnapshots.initialized_all_snapshots
#print axioms Greedy.LabelHistory.sparse_creator_bound
#print axioms Greedy.GrowthJournal.stored_creator_shift
#print axioms Greedy.FamilyNames.initialized_inventory
#print axioms Greedy.FamilyOrder.initialized_all_sources
#print axioms Greedy.FamilyOrder.Invariant.straddling_block_unique
#print axioms Greedy.ClosedFamilies.remaining_sources_avoid
#print axioms Greedy.CreatorPhase.initialized_total_abs_le_three
#print axioms Greedy.CreatorPhase.initialized_summed_coefficient_bound
#print axioms Greedy.CreatorPhase.exists_bounded_shift_history
#print axioms Greedy.EntryJournal.batch_absolute
#print axioms Greedy.AccessJournal.actual_history_agrees
#print axioms Greedy.AdministrationJournal.plan_agrees
#print axioms Greedy.JointRunJournal.exists_joint
#print axioms Greedy.InitializedJoint.exists_journal_history
#print axioms Greedy.ClosedFamilies.remaining_sources_isolated
#print axioms Greedy.WinnerTickets.initialized_total_le_four
#print axioms Greedy.ClosedInstances.all_sources_closed
#print axioms Greedy.ClosedInstances.remaining_sources_small
#print axioms Greedy.ClosedInstances.afterAccess_empty_of_small
#print axioms Greedy.RunBirthJournal.registry_covers
#print axioms Greedy.RunBirthJournal.registry_card
#print axioms Greedy.InstanceCharge.initialized_mass_bound
#print axioms Greedy.IncomingExcess.initialized_mass_bound
#print axioms Greedy.DepartureAmounts.initialized_increase_bound
#print axioms Greedy.DepartureAmounts.initialized_boundary_nondrop_bound
#print axioms Greedy.RunJournal.access_positive_eq
#print axioms Greedy.RunJournal.access_boundary_bound
#print axioms Greedy.RunJournal.access_good_bound
#print axioms Greedy.RunJournal.access_negative_entry_bound
#print axioms Greedy.OutgoingExcess.first_bound
#print axioms Greedy.OutgoingExcess.initialized_combined_bound
#print axioms Greedy.RunJournal.access_positive_entry_bound
#print axioms Greedy.LiveMemory.access
#print axioms Greedy.LiveMemory.plan
#print axioms Greedy.LoserShift.access_eq
#print axioms Greedy.WinnerCredit.observed_bound
#print axioms Greedy.WinnerCredit.internal_bound
#print axioms Greedy.RunJournal.access_creator_eq
#print axioms Greedy.MembershipPointer.link
#print axioms Greedy.FamilyOrder.convertHeap_ordered
#print axioms Greedy.FamilyOrder.Ordered.transport
#print axioms Greedy.FreshRecanonicalization.execute_steps
#print axioms Greedy.WeightedMemory.weighted_loser_bound
#print axioms Greedy.EntryJournal.deficits_bound
#print axioms Greedy.EntryJournal.loser_bound
#print axioms Greedy.LinearLedger.linear
#print axioms Greedy.WeightedCut.weight_le_range
#print axioms Greedy.IntervalCancellation.internal_edge_sum_abs
#print axioms Greedy.FringeCancellation.fringe_internal_sum_abs
#print axioms Greedy.SignedLifetime.total_abs_le_three
#print axioms Greedy.CreatorCancellation.shift_bound
#print axioms Greedy.WeightedActiveCut.sum_le_range
#print axioms Greedy.PositiveBoundary.active_first_phase
#print axioms Greedy.PositiveBoundary.fringe_first_phase
#print axioms Greedy.NegativeBoundaryGeometry.unsafe_card_le_one
#print axioms Greedy.NegativeBoundary.fringe_excess_bound
#print axioms Greedy.PhaseDrops.winner_charges_le_four_drops
#print axioms Greedy.SourceWeights.stored_signed_geometry
#print axioms Greedy.WeightedDepartures.event_bound
#print axioms Greedy.labelRange_of_polylog
#print axioms Greedy.target_of_bounded_comparison

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    let publicName := privateToUserName name
    if [`Greedy, `GreedyForest, `GreedyMerge].any (·.isPrefixOf publicName) then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      if axioms.any (fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound) then
        unexpected := unexpected.push (name, axioms)
  logInfo m!"Audited Greedy declarations, including private declarations: {count}"
  logInfo m!"Declarations using nonstandard axioms: {unexpected}"
  unless unexpected.isEmpty do
    throwError "Nonstandard axiom dependency in Greedy"
