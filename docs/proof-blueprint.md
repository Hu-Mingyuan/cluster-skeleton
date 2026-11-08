Current reference: `proof-blueprint.pdf` and `docs/tex/proof-blueprint.tex` now use the supplied skeleton appendix. Reuse the existing Lean source described below; audit conventions and fill any genuine differences in the requested skew-symmetric scope. The weighted notation does not itself establish a weighted Lean theorem.

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

[`FullSkeletonConsumer.lean`](../verification/FullSkeletonConsumer.lean) applies the final theorem to the literal coordinate conditions and to the complete Liouville manifold. The reproducible build, transitive axiom audit, and their exact source bindings are described in the [verification guide](../verification/README.md).

The rewritten PDF contains only the relevant geometry. It proves a real smooth extension of the imaginary logarithmic form; later finite-type, cocore, and categorical statements from the original notes are not included.
