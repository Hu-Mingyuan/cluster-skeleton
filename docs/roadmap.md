# Cluster skeleton formalization

The first milestone constructs the Liouville geometry of the complex points of the unimodular acyclic cluster model and identifies its full dynamical skeleton. The mathematical source is the supplied October 20, 2026 manuscript, Theorem 2.1, Lemmas 2.2–2.5 and Proposition 2.6.

## Mathematical contract

Let B be an integral skew-symmetric d by d matrix with determinant one. Partition Fin d into mutable and frozen vertices. The mutable arrow relation Bᵢⱼ > 0 is acyclic; frozen coordinates remain nonzero variables.

The carrier Y_B is the subtype of complex coordinate space defined by aᵢbᵢ = Pᵢ + Qᵢ for mutable i and a_f ≠ 0 for frozen f, where Pᵢ = ∏ⱼ aⱼ^(Bᵢⱼ.toNat) and Qᵢ = ∏ⱼ aⱼ^((-Bᵢⱼ).toNat). Use the inherited topology and native Mathlib manifold and tangent-space definitions. Construct the smooth atlas on this carrier, anchored by its actual smooth immersive inclusion in coordinate space.

Construct a smooth real one-form α whose exterior derivative is symplectic and agrees on the initial torus with the imaginary part of (1/2)ΣᵢⱼBᵢⱼ dlog aᵢ ∧ dlog aⱼ. Construct the actual Liouville vector field and a jointly smooth complete flow solving its ODE for every real time.

Independently define the coordinate cap K_B by |a_f| = 1 for frozen f, and |aᵢ| ≤ 1 and (1 - |aᵢ|²)bᵢ = 0 for mutable i. Prove that the set of points whose forward orbit has compact closure equals K_B for this same flow. Prove the dense-torus and extension-uniqueness bridges; a holomorphic extension claim additionally needs its complex-analytic proof.

## Foundation reuse

Pin fs-fltz-minimal at 1a3d387cfacc746e25aad31e5b27b1803103e7cb, Lean 4.34.1, and Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612. Reuse the upstream Apache-2.0 library as a Lake dependency without editing it.

- FsFltz.Geometry.Smooth wraps native ChartedSpace, IsManifold, tangent spaces, continuous alternating maps, and the actual Mathlib exterior derivative.
- FsFltz.Geometry.Liouville provides CompleteLiouvilleFlow, including its actual ODE, and completed Liouville structures.
- SmoothLiouville proves smoothness of the vector obtained from a nondegenerate contraction equation.
- LinearGrowthCompleteFlow and ProperExhaustionCompleteFlow are candidates for the completeness bridge after their hypotheses have been proved for this model.
- CompletionCore proves the equivalence of a genuine completion core and relatively compact forward orbits. It is not needed to define the trapped set and should be imported only when the finite-type completion is constructed.

## Dependency order

1. Define the exchange model, native topology, coordinate cap and dynamical trapped set. Write a faithful target proposition and smoke-test the upstream interfaces.
2. Prove zero-set independence by well-founded induction on the finite mutable arrow relation. This theorem needs no determinant assumption. Prove equivalence of the well-founded encoding with absence of directed cycles.
3. Prove compactness of the coordinate cap directly from the coordinate equations. Prove the generic compact-forward-invariant-set inclusion into the trapped set.
4. Complete primitive integral rows to coordinates; construct node charts, transitions and the smooth atlas. Establish the dense initial torus and the symplectic extension.
5. Construct smooth cutoffs, the dominance factors and H. Prove simultaneous extension of α = AᵀB dθ - dH at every zero stratum, then the global exterior-derivative identity.
6. Compute the radial and angular equations, prove zero-stratum invariance, establish growth bounds and construct the two-sided complete flow.
7. Prove K_B forward invariant. Exclude every other trapped orbit using radial monotonicity, eventual angular dynamics and ODE uniqueness, including initial zero coordinates.
8. Prove finite type via backward control, then cap product descriptions and generalized cocores as subsequent geometric milestones.

## Acceptance

Every delivered proof must compile with the pinned environment. Audit transitive axioms of the proved declarations; only propext, Classical.choice and Quot.sound are allowed. Do not use sorry, new axioms, opaque proof substitutes or assumptions that encode the desired conclusion.

Keep the target proposition distinct from its proof. A defined proposition or record of desired witnesses is an open obligation until inhabited by a checked proof. Maintain explicit completed and outstanding theorem lists. Check mathematical statement fidelity separately from compilation, particularly the actual carrier and topology, matrix and frozen-variable conventions, derivatives, completeness and use of the same flow in the skeleton equality.

The first batch comprises the model, target interfaces, zero-set independence and elementary cap/trapped-set lemmas. The full Liouville existence and skeleton equality remain subsequent obligations until constructed.
