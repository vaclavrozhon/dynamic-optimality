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
import MultiSplay.InitializedForestCoefficientBound
import MultiSplay.SharedSplayComponents
import MultiSplay.PackedBoundedPreparation
import MultiSplay.PhysicalForestSplayBound
import MultiSplay.ForestSplayNormalForm
import MultiSplay.CommonForestSplayBound
import MultiSplay.CommonForestCoefficientBound
import MultiSplay.SecondaryEmissionWords
import MultiSplay.IntervalLowerBound
import MultiSplay.EndpointLedgerSupport
import MultiSplay.EndpointCounterBound

import MultiSplay.ComparatorGuardHull
import MultiSplay.ComparatorGuardPath
import MultiSplay.ComparatorGuardPreparation
import MultiSplay.ComparatorSuffixSeam
import MultiSplay.ComparatorVirtualSeam
import MultiSplay.CompetitiveLogHeight

/-!
Classical MultiSplay in the shared abstract BST model. `Online.strategy`
performs the literal classical switches using actual original-key rotations.
Its cost includes the initial search depth of every request, and a single
charged initialization accepts every supplied initial BST.

`Online.competitive_logarithmic` proves factor
`L₃(n) * egTargetFactor (ceil(log₂(n+1)))` against
`DynamicOptimality.OPT + n`. The Splay factor is the strongest existing
export, evaluated at logarithmic component size. `Online.competitive_generic`
and `Online.competitive_generic_shifted` permit any factor supported by valid
persistent Splay interface coefficients; the shifted form also assumes
monotonicity. These final results have no cheap-comparator or physical
simulation hypothesis.

The proof retains the exact physical run and its chronological forest word.
The comparator maintains persistent endpoint-owned row memory, performs the
same guarded splits and joins on actual component keys, and charges its
secondary services to the proved actual ledger. The endpoint counter theorem
then pays this ledger and all classical switches using the shared optimum.
See `multisplay/COMPOSED_BOUND.txt` for the mathematical proof map.
-/
