import MultiSplay.ForestPotential
import MultiSplay.HeavyRootOperations
import MultiSplay.RibRootOperations
import MultiSplay.SupportedPointer
import MultiSplay.AuxiliarySplay
import MultiSplay.CommonForest
import MultiSplay.AuxiliaryReflection
import MultiSplay.BoundarySwitch
import MultiSplay.ForestReflection
import MultiSplay.ForestDomains
import MultiSplay.SplayPointer
import MultiSplay.ForestRealization
import MultiSplay.CopyComparator
import MultiSplay.EndpointEncoding
import MultiSplay.EndpointPrimary
import MultiSplay.ReferenceAddresses
import MultiSplay.SwitchEmissions
import MultiSplay.EndpointComparator

import MultiSplay.InterfaceExcess
import MultiSplay.InterfaceRootOperations
import MultiSplay.InterfaceDetach
import MultiSplay.OrdinalShift
import MultiSplay.StackShift
import MultiSplay.RepresentationShift
import MultiSplay.Alphabet
import MultiSplay.RawRotation
import MultiSplay.OrdinalEncoding
import MultiSplay.ForestProgram
import MultiSplay.ForestCompiler
import MultiSplay.SparseHeavy
import MultiSplay.SparseRib
import MultiSplay.SparseServices
import MultiSplay.SparseForest
import MultiSplay.SparseInitialization

import MultiSplay.RankEmbedding
import MultiSplay.JoinRanks
import MultiSplay.JoinHeap
import MultiSplay.BlockEmbedding
import MultiSplay.InterfaceEmbedding
import MultiSplay.InterfaceHistory
import MultiSplay.RibPathSimulation
import MultiSplay.LayeredNormalizer
import MultiSplay.LayeredJoin
import MultiSplay.LayeredServices
import MultiSplay.LayeredForest
import MultiSplay.LayeredBoundedForest
import MultiSplay.RichJoinStable
import MultiSplay.RichSplitFramed
import MultiSplay.InterfacePlacementFrame
import MultiSplay.FramedSplay

import MultiSplay.InitializedForestSplayBound
import MultiSplay.SharedSplayComponents
import MultiSplay.PackedBoundedPreparation
import MultiSplay.PhysicalForestSplayBound
import MultiSplay.ForestSplayNormalForm
import MultiSplay.CommonForestSplayBound
import MultiSplay.SecondaryEmissionWords
import MultiSplay.IntervalLowerBound
import MultiSplay.EndpointLedgerSupport
import MultiSplay.EndpointCounterBound

/-!
Formal components of the standard multi-splay proof: exact switch words,
physical splaying and chronological forest replay, persistent sparse forest
normalization with explicit pointer traces and bounded preparation paths, strict
interface root operations, reusable rich histories through common joins and
splits with persistent block placements, and the endpoint-aware primary switch bound against
the shared OPT.

The portable forest splay comparison constructs its finite global universe,
disjoint component placements, complete shared history, and one-time
initialization from the indexed physical program. Its uniform
factor is G * (clog 2 G + 1)^2, or the stabilized
log log K * (log log log K)^2 factor for the bounded normalizer height.
The raw common-forest theorem accepts an independently supplied physical
splay execution and an arbitrary raw comparator for the same event word.
It constructs the full bounded normalizer and the indexed coupling, and
proves exact physical cost transfer by uniqueness of splaying and component
selection. Empty components and arbitrary component-list permutations are
allowed. All constituent splays also have shared pointer-model implementations.
The secondary ledger is defined from the literal adaptive switch emissions.
For every binary depth hierarchy, changing from increasing to actual switch
order changes its count by at most twice the primary-switch count.
The dynamic lower bound is also proved for every binary interval hierarchy,
using the shared actual pointer execution model and the constant 2888.
This extension does not use the Tango-squared upper bound.
The encoded leaf ledger contains the increasing multisplay ledger as exact
chronological row subsequences. Its initialization support has at most 3n
primary core vertices and 4n left-writing owner rows.
The actual endpoint-aware counter bound is proved for arbitrary initial
primary preferences and every binary depth hierarchy: for a perfect reference,
requests + primary switches + actual secondary flips <= 2137120*OPT + 21n.
This root does not assert full multi-splay competitiveness:
the physical multi-splay comparator and its assembly with the raw forest splay
theorem remain. The E(G) improvement is not used here.
-/
