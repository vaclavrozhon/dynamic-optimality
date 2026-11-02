import DynamicOptimality.ReferenceClosure.Execution
import DynamicOptimality.ReferenceClosure.GuardCounterexample

/-!
# NCA closure for the shared geometric BST model

`Geometry.ReferenceClosure.execution_referenceClosure` transforms every
geometric execution into one whose rows and closed time-interval unions
are closed under nearest common ancestors in any supplied reference BST.
It preserves requests and times and multiplies touch cost by at most two.
`Geometry.ReferenceClosure.GuardCounterexample` also checks why adding
extra boundary ancestors is a different, invalid closure rule.
-/
