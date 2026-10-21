# Geometric proof-to-code map

Read the self-contained [proof blueprint PDF](../proof-blueprint.pdf), with editable source in [`tex/proof-blueprint.tex`](tex/proof-blueprint.tex). The [target guide](target-theorem.md) separates definitions and formulation from proofs.

| Step | Mathematical content | Main Lean modules |
| --- | --- | --- |
| Actual exchange space | Nonempty carrier; independent zero indices; monomial node charts; inherited topology; native atlas | `Seed`, `ZeroSet`, `IndependentNodeChart`, `SmoothAtlas` |
| Global symplectic form | Node extension of the imaginary logarithmic form, overlap compatibility, nondegeneracy | `NodeTwoForm`, `NodeNondegeneracy`, `LocalFormGluing`, `GlobalTwoForm`, `GlobalSymplectic` |
| Global primitive | Explicit smooth cutoffs and corrections, singular-term cancellation, gluing and exterior derivative | `PrimitiveCutoffs`, `DominanceCutoff`, `TorusPrimitive`, `NodePrimitiveCancellation`, `NativeNodePrimitive`, `GlobalPrimitive` |
| Complete flow | Actual Liouville field, all-strata bounds, finite-time confinement, two-sided native integral curves | `GlobalLiouvilleField`, `AllStrataGrowth`, `FiniteTimeConfinement`, `NativeCompleteFlow` |
| Cap is trapped | Compactness and forward invariance, including zero strata | `CapSet`, `BoundaryTangency`, `CapAngularTangency`, `CapForwardInvariance`, `ConstructedFlowCapInclusion` |
| Trapped points lie in cap | Radial escape, interior partner rigidity, zero-stratum partner escape | `CompactInteriorRigidity`, `ZeroStratumEscape`, `ConstructedFlowReverseInclusion` |
| Final existence | Same-flow set equality and constructed witnesses | `FullSkeleton` |

The final theorem is `ClusterSkeleton.FullSkeleton.firstGeometricTarget`. Both inclusions concern `NativeCompleteFlow.completeFlow`.

Files under `verification/*Consumer.lean` and their interface notes are development-era consumer checks. The standard verification entry point and its current coverage are documented in [`verification/README.md`](../verification/README.md).

The rewritten PDF contains only the relevant geometry. It proves a real smooth extension of the imaginary logarithmic form; later finite-type, cocore, and categorical statements from the original notes are not included.
