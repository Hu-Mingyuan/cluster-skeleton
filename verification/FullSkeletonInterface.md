# Full skeleton and original geometric target

`ClusterSkeleton.FullSkeleton` imports the accepted forward and reverse
inclusions and combines them for the literal
`NativeCompleteFlow.completeFlow S hdet hε hκ hδ`. Its hypotheses are only the
original seed, unimodularity, and admissible auxiliary parameters
`0 < ε`, `2 * ε + 1 ≤ κ`, and `0 < δ`.

The library declarations are:

- `trappedSet_eq_coordinateCap`: subset antisymmetry on the two inclusions.
- `liouvilleData`: the accepted global primitive, exterior derivative,
  Liouville vector field, contraction identity, and same native complete flow.
- `liouvilleData_flow`: the package preserves that actual flow.
- `torus_anchor`: its exterior derivative has the prescribed logarithmic value.
- `liouvilleData_trappedSet`: the package's full skeleton is the coordinate cap.
- `liouvilleSkeletonTarget_of_parameters`: density and those constructed
  witnesses inhabit the original `LiouvilleSkeletonTarget`.
- `liouvilleSkeletonTarget`: auxiliary parameters `ε = 1`, `κ = 3`, `δ = 1`
  give a uniform witness. These are not frozen coordinate values.
- `firstGeometricTarget`: the unchanged general `FirstGeometricTarget`.

The carrier is the actual complex exchange-equation subtype with its inherited
topology. The full integer matrix remains skew-symmetric and determinant one;
only the mutable quiver is required to be acyclic. Frozen coordinates remain
arbitrary nonzero variables. No flow, completeness statement, compactness
claim, inclusion, or geometric target is supplied as a hypothesis. The cap and
trapped-set definitions are unchanged and independent.

`FullSkeletonConsumer` uses the package to characterize compact forward-orbit
closure by the literal cap equations, handles initially zero originals,
combines forward invariance with the equality, verifies the same skeleton
after conversion to the pinned FsFltz complete Liouville manifold, and consumes
both original targets. At the mutable unit boundary the cap product imposes
no extra partner restriction.

Exact compilation, per-root axiom and native-identity coverage, publication,
and independent review are recorded in the source-bound delivery artifacts.
The consumer's verification scope is the recorded joint fixture unless a
separate standalone receipt explicitly states otherwise. This interface file
does not itself certify those checks or stage/phase acceptance. Historical
source, metadata, order, failed/deferred-check, and archive qualifications
remain in the inherited evidence; the optimized audit remains unadopted.

The full first target excludes the later finite-type, cocore, and holomorphic
extension milestones. Their proofs are not claimed here.
