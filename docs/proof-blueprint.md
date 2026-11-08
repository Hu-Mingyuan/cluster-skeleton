Current reference: `proof-blueprint.pdf` and `docs/tex/proof-blueprint.tex` now use the supplied skeleton appendix. Reuse the existing Lean source described below; audit conventions and fill any genuine differences in the requested skew-symmetric scope. The weighted notation does not itself establish a weighted Lean theorem.

# Geometric proof-to-code map

Read the self-contained [proof blueprint PDF](../proof-blueprint.pdf), with editable source in [`tex/proof-blueprint.tex`](tex/proof-blueprint.tex). The [target guide](target-theorem.md) separates definitions and formulation from proofs.

| Step | Mathematical content | Main Lean modules |
| --- | --- | --- |
| Actual exchange space | Nonempty carrier; independent zero indices; monomial node charts of explicit torus rank `d - 2\|I\|`; inherited topology; native atlas | `Seed`, `ZeroSet`, `IndependentNodeChart`, `IndependentNodeSmooth`, `SmoothAtlas` |
| Global symplectic form | Node extension of the imaginary logarithmic form, overlap compatibility, nondegeneracy | `NodeTwoForm`, `NodeNondegeneracy`, `LocalFormGluing`, `GlobalTwoForm`, `GlobalSymplectic` |
| Global primitive | Explicit smooth cutoffs and corrections, singular-term cancellation, gluing and exterior derivative | `PrimitiveCutoffs`, `DominanceCutoff`, `TorusPrimitive`, `NodePrimitiveCancellation`, `NativeNodePrimitive`, `GlobalPrimitive` |
| Complete flow | Actual Liouville field, all-strata bounds, finite-time confinement, two-sided native integral curves | `GlobalLiouvilleField`, `AllStrataGrowth`, `FiniteTimeConfinement`, `NativeCompleteFlow` |
| Cap is trapped | Compactness and forward invariance, including zero strata | `CapSet`, `BoundaryTangency`, `CapAngularTangency`, `CapForwardInvariance`, `ConstructedFlowCapInclusion` |
| Trapped points lie in cap | Radial escape, interior partner rigidity, zero-stratum partner escape | `CompactInteriorRigidity`, `ZeroStratumEscape`, `ConstructedFlowReverseInclusion` |
| Stratified cap | The cap as the union of the reference strata `Λ_I` over independent `I`; closedness and per-stratum compactness | `CapStrata` |
| Final existence | Same-flow set equality, its stratified form, and constructed witnesses | `FullSkeleton` |

The final theorem is `ClusterSkeleton.FullSkeleton.firstGeometricTarget`. Both inclusions concern `NativeCompleteFlow.completeFlow`.

## The stratified form of the skeleton

`ClusterSkeleton.lambdaStratum S I` is the reference's stratum
`Λ_I = {b_i = 0, ‖a_i‖ ≤ 1 (mutable i ∈ I), ‖a_j‖ = 1 (j ∉ I)}` on the actual exchange points, in [`CapStrata.lean`](../ClusterSkeleton/CapStrata.lean). Two theorems there identify it with the independently defined cap:

- `coordinateCap_eq_iUnion_lambdaStratum : coordinateCap S = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val`, via `lambdaStratum_subset_coordinateCap` and `coordinateCap_subset_lambdaStratum_strictCapIndices` (the stratum realized by a cap point is indexed by `Seed.Point.strictCapIndices`, independent by `CapIndependence.coordinateCap_strictCapIndices_independent`);
- `isClosed_lambdaStratum` and `isCompact_lambdaStratum`, the reference's per-stratum compactness.

Composing with the equality for the same constructed flow gives the reference's stratified skeleton identity verbatim:

```lean
theorem FullSkeleton.trappedSet_eq_iUnion_lambdaStratum :
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val
```

Independence is used only to index the union by the same family the reference uses; neither inclusion needs it.

The node charts carry the reference's explicit torus exponent: for independent `I`, `ClusterSkeleton.IndependentNodeChart.complementRank_eq_sub_two_mul_card` proves `SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card`, so `IndependentNodeChart.homeomorph` lands in `({i // i ∈ I} → Node) × (ℂ*)^(d - 2|I|)`, with `two_mul_card_le : 2 * I.card ≤ d`. Both are in [`IndependentNodeSmooth.lean`](../ClusterSkeleton/IndependentNodeSmooth.lean).

These close gaps **G1** and **G2** of the [audit](skeleton-audit.md); the scope is unchanged (skew-symmetric unimodular, mutable acyclic, variable frozen coordinates, no weighted or principal-coefficient claim).

[`FullSkeletonConsumer.lean`](../verification/FullSkeletonConsumer.lean) applies the final theorem to the literal coordinate conditions and to the complete Liouville manifold. The reproducible build, transitive axiom audit, and their exact source bindings are described in the [verification guide](../verification/README.md).

The PDF and `docs/tex/proof-blueprint.tex` state the reference's stratified identity; `tex` records the Lean declarations above, while `proof-blueprint.pdf` predates them and has not been regenerated, because the publication host has no LaTeX toolchain.

The rewritten PDF contains only the relevant geometry. It proves a real smooth extension of the imaginary logarithmic form; later finite-type, cocore, and categorical statements from the original notes are not included.
