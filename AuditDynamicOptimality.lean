import DynamicOptimality
import Splay
import ChaCha
import ChaChaPaper20261030
import Lean

set_option stderrAsMessages false

/-! Audit public and private declarations using Lean's standard collector.
The imported axiom summaries avoid rereading proof bodies under memory
pressure. Keep this file outside the module system so private declarations
remain included. Progress goes directly to stderr for long-running audits. -/

open Lean in
run_cmd do
  Lean.Elab.Command.liftIO <| IO.eprintln "Imports loaded; checking public endpoints."

#print axioms ChaCha.Paper20261030.HeadBlocks.ExposedLocal.reassemble
#print axioms ChaCha.Paper20261030.HeadBlocks.Shared.run
#print axioms ChaCha.Paper20261030.HeadBlocks.Local.actions_length
#print axioms ChaCha.Paper20261030.OrderedContext.PacketAcquisition.acquire
#print axioms ChaCha.Paper20261030.HeadBlocks.PacketAcquisition.acquisition_bounds
#print axioms ChaCha.Paper20261030.MultiSourceSingleCursor.compile_run
#print axioms ChaCha.Paper20261030.MultiSourceMask.compile_run
#print axioms ChaCha.Paper20261030.MultiSourceRecenter.three_run
#print axioms ChaCha.Paper20261030.PrimaryReentryController.dispatch
#print axioms ChaCha.Paper20261030.RootRecordTour.run
#print axioms ChaCha.Paper20261030.PrimaryHeaderRefresh.component_refresh
#print axioms ChaCha.Paper20261030.PrimaryRefreshingReentry.append_refresh
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedComponentController.access
#print axioms ChaCha.Paper20261030.ImmutableSource.readonly_run
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.compile_tagged_run
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedTerminalController.expose
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedOriginalExitController.access
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedCompletionController.access
#print axioms ChaCha.Paper20261030.IdentifiedHeadExchange.global_unique
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.compile_root_run
#print axioms ChaCha.Paper20261030.Structural.HeadBoundary.repair_exact
#print axioms ChaCha.Paper20261030.Structural.HeadBoundary.blocks_unchanged
#print axioms ChaCha.Paper20261030.Structural.observer_checked
#print axioms ChaCha.Paper20261030.BoundaryReadController.working_records
#print axioms ChaCha.Paper20261030.ComponentObserverCompiler.compile_run
#print axioms ChaCha.Paper20261030.ComponentBoundaryReadController.active
#print axioms ChaCha.Paper20261030.ComponentBoundaryReadController.sentinel
#print axioms ChaCha.Paper20261030.PackedPrimary.head_step_boundary_views
#print axioms ChaCha.Paper20261030.PackedPrimary.root_step_boundary_views
#print axioms ChaCha.Paper20261030.PhysicalContextRepair.run
#print axioms ChaCha.Paper20261030.PhysicalContextRepair.eight_reachable
#print axioms ChaCha.Paper20261030.PhysicalContextRepair.shared
#print axioms ChaCha.Paper20261030.ComponentPhysicalRepair.execute
#print axioms ChaCha.Paper20261030.ComponentPhysicalRepair.identifier_inventory
#print axioms ChaCha.Paper20261030.PrimaryHeaderController.fromRoot_correct
#print axioms ChaCha.Paper20261030.PhysicalPacketStaging.Context.stage
#print axioms ChaCha.Paper20261030.PhysicalPacketStaging.Repacking.repack
#print axioms ChaCha.Paper20261030.PhysicalPacketStaging.Repacking.identifiers
#print axioms ChaCha.Paper20261030.PacketContext.stage_pruned
#print axioms ChaCha.Paper20261030.PacketContext.eight_bounds
#print axioms ChaCha.Paper20261030.PhysicalIdentifierInitialization.execute
#print axioms ChaCha.Paper20261030.PhysicalIdentifierInitialization.metadata
#print axioms ChaCha.Paper20261030.PhysicalIdentifierInitialization.identifier_inventory
#print axioms ChaCha.Paper20261030.ObservedHeadBlueprint.bits_exact
#print axioms ChaCha.Paper20261030.ObservedHeadBlueprint.active_exact
#print axioms ChaCha.Paper20261030.PrimaryVirtualPackets.prefix_absent
#print axioms ChaCha.Paper20261030.PrimaryVirtualPackets.interval_packet
#print axioms ChaCha.Paper20261030.VirtualHeadPacketController.computed
#print axioms ChaCha.Paper20261030.VirtualHeadPacketController.computed_root
#print axioms ChaCha.Paper20261030.VirtualHeadPacketController.output_ready
#print axioms ChaCha.Paper20261030.VirtualPhysicalPackets.install
#print axioms ChaCha.Paper20261030.ImmutableSourceRecordInvariant.run
#print axioms ChaCha.Paper20261030.PacketAlignment.stored_id
#print axioms ChaCha.Paper20261030.PacketAlignment.run
#print axioms ChaCha.Paper20261030.PacketAlignment.head_reassemble
#print axioms ChaCha.Paper20261030.PacketLayers.stage_matches
#print axioms ChaCha.Paper20261030.PacketLayers.Reached.stage
#print axioms ChaCha.Paper20261030.PacketLayers.Reached.repack
#print axioms ChaCha.Paper20261030.HeadPacketLayout.before_realizes
#print axioms ChaCha.Paper20261030.HeadPacketLayout.after_realizes
#print axioms ChaCha.Paper20261030.HeadPacketLayout.after_good
#print axioms ChaCha.Paper20261030.HeadReassembleRepack.execute
#print axioms ChaCha.Paper20261030.MixedHeadExchange.execute
#print axioms ChaCha.Paper20261030.RootMixedHeadExchange.active_layout
#print axioms ChaCha.Paper20261030.RootMixedHeadExchange.run
#print axioms ChaCha.Paper20261030.StoredVirtualHeaderRead.execute
#print axioms ChaCha.Paper20261030.PacketLayers.Representation.realJoin
#print axioms ChaCha.Paper20261030.PacketLayers.Representation.attachment
#print axioms ChaCha.Paper20261030.MixedHeadInputView.input

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedExposureController.active
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedExposureController.sentinel
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreController.active
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreController.sentinel
#print axioms ChaCha.Paper20261030.Dyadic.exitDepth_eq_lcaDepth
#print axioms ChaCha.Paper20261030.Dyadic.exit_separator_test
#print axioms ChaCha.Paper20261030.Dyadic.computeExitDepth_correct
#print axioms ChaCha.Paper20261030.Dyadic.WidthRegisters.bounded_next
#print axioms ChaCha.Paper20261030.MultiSourceAugment.compile_run
#print axioms ChaCha.Paper20261030.PrimaryEntryController.dispatch
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.OriginalEntryController.access
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.OriginalCompletionController.access
#print axioms ChaCha.Paper20261030.LocalColoredCompiler.compile_run
#print axioms ChaCha.Paper20261030.LocalComponentForestCompiler.compile_run
#print axioms ChaCha.Paper20261030.ForestConnector.compile_run
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.compile_run
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ComponentAccessController.access
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.EndpointController.access
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ComponentEndpointController.access
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.real_payload_focus
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.original_keys
#print axioms ChaCha.Paper20261030.ForestConnector.ThreeColors.entry_run
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.serve_run
#print axioms ChaCha.Paper20261030.MultiSourceProgram.Serves.run
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.representation_root
#print axioms ChaCha.Paper20261030.MultiSourceProgram.Run.wellFormed
#print axioms ChaCha.Paper20261030.MultiSourceProgram.Run.leaves
#print axioms ChaCha.Paper20261030.VirtualHeaderController.compile_run
#print axioms ChaCha.Paper20261030.PayloadForestController.compile_run
#print axioms ChaCha.Paper20261030.ForestMirrorController.compile_run
#print axioms ChaCha.Paper20261030.ImmutableStructural.checked_compile_run
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ColoredAccessController.access

#print axioms DynamicOptimality.BST.rotation_pointer
#print axioms DynamicOptimality.LocalVineInitialization.normalize
#print axioms DynamicOptimality.LocalVineInitialization.counter_bound
#print axioms DynamicOptimality.LocalSnapshot.working_records
#print axioms ChaCha.Paper20261030.Auxiliary.BalanceController.balance_run
#print axioms ChaCha.Paper20261030.Auxiliary.JoinController.link_run
#print axioms ChaCha.Paper20261030.Auxiliary.JoinController.link_prefix_right_rank
#print axioms ChaCha.Paper20261030.Auxiliary.JoinController.link_prefix_left_rank
#print axioms ChaCha.Paper20261030.Auxiliary.SplitController.split_run
#print axioms ChaCha.Paper20261030.GapSource.Controller.compile_root_run
#print axioms ChaCha.Paper20261030.GapSource.Controller.extra_records
#print axioms ChaCha.Paper20261030.Auxiliary.SourceController.compile_ordinary
#print axioms ChaCha.Paper20261030.BoundaryObservations.ClosedNeighborController.query_represented
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.DepartureController.head_selection
#print axioms DynamicOptimality.OPT_attained
#print axioms DynamicOptimality.splay_target_iff
#print axioms DynamicOptimality.OPT_le_pointer_cost
#print axioms DynamicOptimality.exists_pointer_of_OPT
#print axioms DynamicOptimality.competitive_iff_pointer
#print axioms DynamicOptimality.splay_competitive
#print axioms Splay.concreteTargetBound
#print axioms ChaCha.Paper20261030.Auxiliary.Metadata.balance_charged
#print axioms ChaCha.Paper20261030.Auxiliary.Metadata.splitAt_charged_log

#print axioms DynamicOptimality.Relabel.execution
#print axioms DynamicOptimality.hull_touch_heap
#print axioms DynamicOptimality.hull_key_separation
#print axioms ChaCha.Paper20261030.Rectangles.robustBound_le_shared_OPT
#print axioms ChaCha.Paper20261030.Dyadic.bst_run_shared_OPT

#print axioms ChaCha.Paper20261030.GapBST.Storage.trace
#print axioms ChaCha.Paper20261030.GapBST.Storage.services
#print axioms ChaCha.Paper20261030.Auxiliary.Metadata.Execution.pointer

#print axioms ChaCha.Paper20261030.Auxiliary.PayloadMap.split_impl_map
#print axioms ChaCha.Paper20261030.BoundaryObservations.CleanController.split
#print axioms ChaCha.Paper20261030.BoundaryObservations.MarkedCutController.cut
#print axioms ChaCha.Paper20261030.BoundaryObservations.PreferenceFlipController.prefer_right
#print axioms ChaCha.Paper20261030.BoundaryObservations.PreferenceFlipController.prefer_left
#print axioms ChaCha.Paper20261030.PathDecomposition.left_head_controller
#print axioms ChaCha.Paper20261030.PathDecomposition.repair_context_controller
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RepairController.head_step
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.AccessController.access

#print axioms ChaCha.Paper20261030.Structural.ContextController.rotate_right
#print axioms ChaCha.Paper20261030.Structural.ContextController.rotate_left
#print axioms ChaCha.Paper20261030.PhysicalPackedParentController.ascend
#print axioms ChaCha.Paper20261030.PackedRotationProgram.rotate
#print axioms ChaCha.Paper20261030.PhysicalPackedWriteController.write
#print axioms ChaCha.Paper20261030.PackedRotationController.rotate_right
#print axioms ChaCha.Paper20261030.PackedRotationController.rotate_left
#print axioms ChaCha.Paper20261030.PhysicalPackedChildController.descend
#print axioms ChaCha.Paper20261030.PhysicalForestCompiler.compile_run
#print axioms ChaCha.Paper20261030.PhysicalRecordFinder.find_parent
#print axioms ChaCha.Paper20261030.ColoredStorage.forest_parent_record
#print axioms ChaCha.Paper20261030.PhysicalForestMetadata.parent_present
#print axioms ChaCha.Paper20261030.ImmutableStructural.extra_records
#print axioms ChaCha.Paper20261030.PackedChildController.descend
#print axioms ChaCha.Paper20261030.PackedReadController.read
#print axioms ChaCha.Paper20261030.ImmutableSource.steps_invariant
#print axioms ChaCha.Paper20261030.ImmutableStructural.compile_run
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.StructuralAccessController.access
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.AccessController.access_service
#print axioms ChaCha.Paper20261030.SourceLocalProgram.ReachesLeafRead.trace

#print axioms ChaCha.Paper20261030.CanonicalMixedHeadInput.input
#print axioms ChaCha.Paper20261030.CanonicalMixedRootInput.input
#print axioms ChaCha.Paper20261030.ReadyMixedHeadExchange.execute
#print axioms ChaCha.Paper20261030.CanonicalPreparedComponentViews.active
#print axioms ChaCha.Paper20261030.CanonicalVirtualHeaderRead.execute
#print axioms ChaCha.Paper20261030.VirtualHeadPacketController.computed_from_forests

#print axioms ChaCha.Paper20261030.MultiSourceProgram.Run.extend
#print axioms ChaCha.Paper20261030.MultiSourceRegisterExtension.execute
#print axioms ChaCha.Paper20261030.MultiSourceRecordEquivalence.compile_run
#print axioms ChaCha.Paper20261030.MultiSourceImmutable.compile_run
#print axioms ChaCha.Paper20261030.MultiSourceNestedImmutable.execute
#print axioms ChaCha.Paper20261030.MultiSourcePacketPrefix.execute
#print axioms ChaCha.Paper20261030.MultiSourceEnclosingOperation.execute
#print axioms ChaCha.Paper20261030.NestedComponentReturn.header
#print axioms ChaCha.Paper20261030.EnclosedComponentExecution.execute
#print axioms ChaCha.Paper20261030.EnclosedRootedComponentExecution.execute
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.compile_write_labels
#print axioms ChaCha.Paper20261030.MultiSourceAugment.compile_run_predicate
#print axioms ChaCha.Paper20261030.MultiSourceImmutable.compile_run_predicate
#print axioms ChaCha.Paper20261030.MultiSourceNestedImmutable.execute_predicate
#print axioms ChaCha.Paper20261030.EnclosedComponentExecution.execute_aligned
#print axioms ChaCha.Paper20261030.EnclosedRootedComponentExecution.execute_aligned
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.active_enclosed
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.sentinel_enclosed
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution.active_enclosed
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution.sentinel_enclosed
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution.root_active_enclosed
#print axioms ChaCha.Paper20261030.NestedComponentEntry.execute
#print axioms ChaCha.Paper20261030.ReenteredComponentExecution.execute
#print axioms ChaCha.Paper20261030.ReenteredRootedComponentExecution.execute
#print axioms ChaCha.Paper20261030.PrimaryHeaderRefresh.at_cursor
#print axioms ChaCha.Paper20261030.CachedRootOperation.execute
#print axioms ChaCha.Paper20261030.CachedReenteredComponent.dispatch
#print axioms ChaCha.Paper20261030.CachedRootedComponentExecution.execute

#print axioms ChaCha.Paper20261030.MultiSourceNestedImmutable.checked
#print axioms ChaCha.Paper20261030.MultiSourceNestedImmutable.anchors
#print axioms ChaCha.Paper20261030.MultiSourceNestedImmutable.inorderLabels
#print axioms ChaCha.Paper20261030.EnclosingPacketOperation.identifier_tree
#print axioms ChaCha.Paper20261030.SourcePositions.recordAt_label_unique
#print axioms ChaCha.Paper20261030.MultiSourceProgram.represents_of_fingerLabel
#print axioms ChaCha.Paper20261030.ColoredStorage.Source.eq_of_erasure_inorder
#print axioms ChaCha.Paper20261030.SubtreeMetadata.focus_eq
#print axioms ChaCha.Paper20261030.MultiSourceProgram.retained_subtree_handoff
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.real_payload_occurs
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.enclosed_payload_occurs
#print axioms ChaCha.Paper20261030.CanonicalRetainedPayloadHandoff.handoff
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.active_reentered
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.sentinel_reentered

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.active_handoff

#print axioms ChaCha.Paper20261030.MultiSourceAugment.paired_inventory
#print axioms ChaCha.Paper20261030.CachedRootOperation.execute_with_metadata
#print axioms ChaCha.Paper20261030.CachedRootOperation.retained_anchor
#print axioms ChaCha.Paper20261030.CachedRootContinuation.execute_with_metadata
#print axioms ChaCha.Paper20261030.CachedReenteredContinuation.dispatch
#print axioms ChaCha.Paper20261030.CachedObservedComponent.working_records
#print axioms ChaCha.Paper20261030.PacketPrefixErasure.reattach
#print axioms ChaCha.Paper20261030.PacketPrefixErasure.physical
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.active_cached_handoff
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.sentinel_cached
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.incoming_cached

#print axioms ChaCha.Paper20261030.CanonicalRoutingParentRepair.frames
#print axioms ChaCha.Paper20261030.CanonicalRoutingCursor.parent_repair
#print axioms ChaCha.Paper20261030.CanonicalRoutingCursor.update_agrees_of_distinct
#print axioms ChaCha.Paper20261030.CanonicalRoutingPayloadUpdate.update_unique
#print axioms ChaCha.Paper20261030.CanonicalRoutingPayloadUpdate.update_enclosed
#print axioms ChaCha.Paper20261030.LocalComponentCompiler.real_payload_position

#print axioms ChaCha.Paper20261030.EnclosingPacketOperation.ancestor_handoff
#print axioms ChaCha.Paper20261030.CachedRootOperation.ancestor_handoff
#print axioms ChaCha.Paper20261030.MultiSourceParkContinuation.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedPairController.compose
#print axioms ChaCha.Paper20261030.CanonicalForestWingUpdate.erase_same
#print axioms ChaCha.Paper20261030.CanonicalForestWingUpdate.assembled
#print axioms ChaCha.Paper20261030.PacketParentNeutral.fixed_actual_prefix
#print axioms ChaCha.Paper20261030.CanonicalReachedPayloadPosition.position
#print axioms ChaCha.Paper20261030.CanonicalPacketLayerViews.routing_keys_distinct
#print axioms ChaCha.Paper20261030.CanonicalRoutingPayloadUpdate.reached
#print axioms ChaCha.Paper20261030.CanonicalComponentUniqueness.realized_focus
#print axioms ChaCha.Paper20261030.CanonicalIncomingComponentUpdate.update
#print axioms ChaCha.Paper20261030.SourcePositions.ancestor_split
#print axioms ChaCha.Paper20261030.CachedRootOperation.reached_ancestor
#print axioms ChaCha.Paper20261030.CanonicalIncomingComponentUpdate.cached
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.incoming_cached_with_active
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedPairExecution.execute
#print axioms ChaCha.Paper20261030.PathRecordRead.execute
#print axioms ChaCha.Paper20261030.ForestConnector.ThreeColors.reached_header
#print axioms ChaCha.Paper20261030.ReachedVirtualHeaderRead.execute
#print axioms ChaCha.Paper20261030.ReachedVirtualHeaderPair.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedPairHeaderExecution.execute

#print axioms ChaCha.Paper20261030.ObservedHeadParameters.computed
#print axioms ChaCha.Paper20261030.ObservedHeadExchangeExecution.execute
#print axioms ChaCha.Paper20261030.PreparedLeafIntervals.split_range
#print axioms ChaCha.Paper20261030.PreparedLeafIntervals.represented_active
#print axioms ChaCha.Paper20261030.PreparedLeafIntervals.represented_incoming
#print axioms ChaCha.Paper20261030.PrimaryObservedHeadParameters.computed
#print axioms ChaCha.Paper20261030.ObservedCanonicalHeadExecution.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedHeadController.append_head
#print axioms ChaCha.Paper20261030.HeadVirtualOutputShapes.active
#print axioms ChaCha.Paper20261030.HeadVirtualOutputShapes.dormant
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedHeadExecution.execute

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses.active_restore
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses.dormant_restore
#print axioms ChaCha.Paper20261030.ObservedHeadParameters.output_ready
#print axioms ChaCha.Paper20261030.VirtualPhysicalPackets.ready_erases
#print axioms ChaCha.Paper20261030.HeadSourceInventory.unique
#print axioms ChaCha.Paper20261030.ComputedComponentReconstruction.pieces
#print axioms ChaCha.Paper20261030.HeadRealOutputShapes.active
#print axioms ChaCha.Paper20261030.HeadRealOutputShapes.dormant

#print axioms ChaCha.Paper20261030.ComputedComponentReconstruction.active
#print axioms ChaCha.Paper20261030.ComputedComponentReconstruction.dormant
#print axioms ChaCha.Paper20261030.EnclosingPacketOperation.output_focus_valid
#print axioms ChaCha.Paper20261030.CanonicalActiveHeadForest.reconstruct
#print axioms ChaCha.Paper20261030.CanonicalDormantHeadForest.reconstruct
#print axioms ChaCha.Paper20261030.CanonicalRealPayloadValidity.realized

#print axioms ChaCha.Paper20261030.HeadBoundaryRoute.component
#print axioms ChaCha.Paper20261030.CanonicalBoundaryRoute.locate
#print axioms ChaCha.Paper20261030.SourcePositions.reached_proper
#print axioms ChaCha.Paper20261030.SourcePositions.distinct_labels_of_proper_descent
#print axioms ChaCha.Paper20261030.ReachedBoundaryRoute.execute
#print axioms ChaCha.Paper20261030.ObservedDormantRoute.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedHeadReturnController.append_route
#print axioms ChaCha.Paper20261030.PrimaryHeaderPairRefresh.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedHeadCacheController.append_refresh
#print axioms ChaCha.Paper20261030.PrimaryHeaderController.switched_represents

#print axioms ChaCha.Paper20261030.CachedReachedRootedOperation.execute

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedPreparedRestoration.active
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedPreparedRestoration.dormant

#print axioms ChaCha.Paper20261030.PrimaryHeaderController.Represents.preserve
#print axioms ChaCha.Paper20261030.PrimaryHeaderController.Represents.refresh
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestorationController.compose
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.DormantRestorationPreservesActive.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ActiveRestorationPreservesDormant.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestorationExecution.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.InteriorHeadExecution.execute

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses.sentinel_restore
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses.root_active_restore
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses.root_dormant_restore
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedRootPreparedRestoration.sentinel
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.CachedRootPreparedRestoration.active

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure.sentinel_cached_handoff

#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedPairController.compose
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedPairExecution.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedPairHeaderController.append_reads
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedPairHeaderExecution.execute

#print axioms ChaCha.Paper20261030.ObservedRootHeadParameters.computed
#print axioms ChaCha.Paper20261030.HeadVirtualOutputShapes.root_active
#print axioms ChaCha.Paper20261030.PrimaryObservedRootHeadParameters.computed
#print axioms ChaCha.Paper20261030.ObservedCanonicalRootHeadExecution.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadController.append_head
#print axioms ChaCha.Paper20261030.HeadRealOutputShapes.root_active
#print axioms ChaCha.Paper20261030.CanonicalRootActiveHeadForest.reconstruct
#print axioms ChaCha.Paper20261030.ObservedRootDormantRoute.execute
#print axioms ChaCha.Paper20261030.PrimaryHeaderController.switched_minimum_represents
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadReturnController.append_route
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadCacheController.append_refresh
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadExecution.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootDormantRestorationPreservesActive.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootActiveRestorationPreservesDormant.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedRestorationController.compose
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedRestorationExecution.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootHeadExecution.execute
#print axioms ChaCha.Paper20261030.CachedReachedHeaderOperation.execute
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.SharedCachedSecondaryAccess.execute

#print axioms ChaCha.Paper20261030.RestoredHeadPayloadFrame.off_boundary
#print axioms ChaCha.Paper20261030.ForestConnector.ThreeColors.reached_header_leaf
#print axioms ChaCha.Paper20261030.ReachedBottomService.execute
#print axioms ChaCha.Paper20261030.PreparedIncomingRoute.active
#print axioms ChaCha.Paper20261030.PreparedIncomingRoute.sentinel
#print axioms ChaCha.Paper20261030.HeadCacheFrame.MetadataFrame.trans
#print axioms ChaCha.Paper20261030.HeadCacheFrame.pair_refresh_frame_of_run
#print axioms ChaCha.Paper20261030.HeadCacheFrame.canonical_payload_cache
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.PreparedHeadController.append_head_frame
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadController.append_head_frame
#print axioms ChaCha.Paper20261030.ObservedCanonicalHeadExecution.inorder_of_run
#print axioms ChaCha.Paper20261030.ObservedCanonicalRootHeadExecution.inorder_of_run
#print axioms ChaCha.Paper20261030.GlobalPrimaryInventory.Unique.update_pair
#print axioms ChaCha.Paper20261030.SecondaryDecomposition.Components.Valid.head_outputs
#print axioms ChaCha.Paper20261030.GlobalPrimaryRepresentation.LogicalInvariant.head_outputs
#print axioms ChaCha.Paper20261030.PrimaryWings.ComponentRoot.endpoint_unique
#print axioms ChaCha.Paper20261030.PrimaryWings.ComponentRoot.endpoint_exists
#print axioms ChaCha.Paper20261030.GlobalPrimaryRepresentation.Nested.head_update

open Lean in
run_cmd do
  let env ← getEnv
  let prefixes := #[`DynamicOptimality, `Splay, `ChaCha]
  let mut targets : Array Name := #[]
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName name)) then
      targets := targets.push name
  Lean.Elab.Command.liftIO <| IO.eprintln s!"Starting namespace audit: {targets.size} declarations."
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Array Name) := #[]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    if axioms.any (fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound) then
      unexpected := unexpected.push (name, axioms)
    count := count + 1
    if count % 2000 == 0 then
      Lean.Elab.Command.liftIO <| IO.eprintln s!"Axiom audit progress: {count}/{targets.size}."
  logInfo m!"Audited shared, splay, and Tango declarations: {count}"
  logInfo m!"Declarations using nonstandard axioms: {unexpected}"
  unless unexpected.isEmpty do
    throwError "Nonstandard axiom dependency in the shared development"
