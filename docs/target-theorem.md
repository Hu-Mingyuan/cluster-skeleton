# Definitions, formulation, and the proved target

The full mathematical statement is in [target-theorem.pdf](../target-theorem.pdf), with editable source in [`tex/target-theorem.tex`](tex/target-theorem.tex).

## Input and definitions

Let `B` be the full `d × d` skew-symmetric integer matrix, with `det B = 1`. Its mutable subquiver is acyclic. Frozen coordinates are variable nonzero complex numbers. The space is the actual subtype of pairs `(a,b)` satisfying `a_i b_i = P_i(a) + Q_i(a)` for mutable indices and `a_f ≠ 0` for frozen indices, with the inherited topology.

| Declaration | Role |
| --- | --- |
| `Seed`, `Seed.Unimodular` | Input data and hypotheses |
| `Seed.Point` | Actual exchange-equation carrier |
| `coordinateCap` | Frozen norms equal one; mutable norms at most one and `(1 - ‖a_i‖²)b_i = 0` |
| `lambdaStratum S I` | The reference stratum `Λ_I`: `b_i = 0` and `‖a_i‖ ≤ 1` for mutable `i ∈ I`, `‖a_j‖ = 1` for `j ∉ I` |
| `trappedSet` | Points with relatively compact forward orbit under a given native flow |
| `SmoothPresentation`, `LiouvilleData` | Interfaces specifying required witnesses and properties |
| `LiouvilleSkeletonTarget`, `FirstGeometricTarget` | Propositions expressing the goal |

All are in namespace `ClusterSkeleton`. The actual space is nonempty: take all `a_j = 1` and mutable `b_i = 2`. Defining an interface does not construct an inhabitant.

## What the theorem proves

For every such input, the construction supplies a smooth real manifold of dimension `2d` on that fixed space, with smooth immersive coordinate inclusion and dense initial torus. It constructs a smooth real one-form `λ` such that `dλ` is symplectic and agrees on the torus with the imaginary part of `(1/2) Σ B_ij dlog(a_i) ∧ dlog(a_j)`.

It constructs the same Liouville field `ι_Z dλ = λ` and its native smooth flow for all real times, and proves **`trappedSet Φ = coordinateCap`**.

The same equality is also available in the reference's stratified form,

```
trappedSet Φ = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val,
```

as `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`, obtained from the cap equality and `coordinateCap_eq_iUnion_lambdaStratum`. The union runs over the independent subsets of the mutable vertices; each `lambdaStratum S I` with `I ⊆ S.mutable` is compact (`isCompact_lambdaStratum`). This is a restatement of the same proved equality, not an additional claim.

On the chart side, the node charts have the explicit torus rank the reference states: for independent `I`, `IndependentNodeChart.complementRank_eq_sub_two_mul_card` proves `SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card`, with `two_mul_card_le : 2 * I.card ≤ d`.

The quantifiers are `∀ input, ∃ smooth presentation, λ, Z, Φ, ...`. A flow, completeness, cap invariance, and either skeleton inclusion are not extra hypotheses. The final theorem chooses the admissible cutoff parameters `ε = 1`, `κ = 3`, `δ = 1`.

| Declaration | Proof or construction |
| --- | --- |
| `SmoothAtlas.presentation` | Constructs the native manifold presentation |
| `FullSkeleton.liouvilleData` | Constructs the primitive, field, and complete flow package |
| `FullSkeleton.torus_anchor` | Checks the prescribed torus two-form |
| `FullSkeleton.trappedSet_eq_coordinateCap` | Proves the equality for the same flow |
| `coordinateCap_eq_iUnion_lambdaStratum` | Proves the cap is the union of the strata `Λ_I` over independent `I` |
| `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` | Proves the stratified form of the same equality |
| `IndependentNodeChart.complementRank_eq_sub_two_mul_card` | Proves the node-chart torus rank is `d - 2\|I\|` |
| `FullSkeleton.liouvilleSkeletonTarget` | Proves the seed-specific target |
| `FullSkeleton.firstGeometricTarget` | Proves the universally quantified original target |

The final declarations are in [`FullSkeleton.lean`](../ClusterSkeleton/FullSkeleton.lean); their proposition is in [`GeometryTarget.lean`](../ClusterSkeleton/GeometryTarget.lean). The strata are defined and identified with the cap in [`CapStrata.lean`](../ClusterSkeleton/CapStrata.lean), and the torus rank is in [`IndependentNodeSmooth.lean`](../ClusterSkeleton/IndependentNodeSmooth.lean).

## Scope and trust boundary

This proves real smooth symplectic geometry, not algebraic smoothness or a complex-manifold structure. Holomorphic extension, finite type, cap products, cocores, and HMS are not claimed. The scope is the skew-symmetric unimodular case with mutable acyclicity and variable frozen coordinates; no weighted (`D̃ ≠ I`) and no principal-coefficient statement is asserted. The stratified restatement and the torus rank add no hypothesis and change no existing statement.

The current [`target-theorem.pdf`](../target-theorem.pdf) and its editable source [`tex/target-theorem.tex`](tex/target-theorem.tex) include the stratified statement.

Both mathematical statement review and Lean checking are necessary. The [verification guide](../verification/README.md) records build and axiom evidence. Only the foundational axioms `propext`, `Classical.choice`, and `Quot.sound` are allowed; no additional geometric axioms are permitted.
