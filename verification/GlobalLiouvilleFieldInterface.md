# Global native Liouville field and nonzero-coordinate radial control

`GlobalLiouvilleField.Z S hdet ε κ hδ` is exactly the pinned native
`liouvilleVector` of `GlobalPrimitive.alpha` on
`(SmoothAtlas.presentation S hdet).manifold`. Its points are the actual complex
exchange subtype with inherited topology. The full integer matrix is skew
symmetric with determinant one, only the mutable quiver is acyclic, and frozen
coordinates remain nonzero variables.

`isSmoothVectorField_Z` uses pinned `SmoothLiouville` smoothness and the accepted
global primitive/nondegeneracy. `contraction_exteriorDerivative` uses native
`liouvilleEquation_exists`, not a supplied solution. It and `contraction_omega`
quantify over every native tangent at every exchange point. `Z_eq_torus` uses
native nondegenerate uniqueness, the global derivative identity, and literal
primitive agreement to identify this global vector with the accepted torus vector.

`mutable_radial_equation`, `frozen_radial_equation_torus`,
`angular_equation_partial_deriv`, and `logarithmic_linear_growth` transfer the
accepted torus calculus to this global vector. The angular formula uses the
genuine real partial derivative of the accepted local-log Hamiltonian.
The growth constant is independent of the point. Those formulas and that growth
assertion are restricted to the initial torus, as in manuscript (2.9).

`A S p j` is the literal `Real.log ‖p.a j‖` and `L` is its native scalar derivative
along `Z`. `differential_A` proves the real logarithmic differential formula
for every native tangent assuming only the selected coordinate is nonzero.
`L_eq_logarithmicComponents` applies it to the global vector. Other mutable
coordinates can vanish. No global smoothness of a totalized mutable logarithm
is asserted.

`contMDiffAt_A` reuses the accepted local logarithmic smoothness lemma.
`contMDiffOn_scalarDerivative` composes the actual tangent map with the smooth
native vector section, then uses the tangent-bundle model-space homeomorphism.
It proves `contMDiffOn_L` on the open selected-coordinate nonzero locus.
`continuousAt_A` and `continuousAt_L` supply the pointwise continuity used below.

`le_of_dense_open` restricts density to an open neighborhood.
`L_eq_A_of_collar` first proves equality on the OPEN collar A_j > -2ε, where
the radial cutoff vanishes, then extends by continuity from the torus.
`L_eq_A_of_nonneg` therefore includes A_j=0 without assuming density inside
a closed sign locus. `L_negative_bound` passes only the weak inequality
L_j ≤ A_j - radial(A_j) through continuity on the open negative locus;
strict negativity follows separately from the accepted cutoff inequality.
`frozen_radial_equation` applies at every exchange point using `frozen_ne_zero`.
These are selected-coordinate consequences of manuscript (2.10).

All results retain ε>0 and κ≥2ε+1 where needed. They hold for every δ>0,
which includes the required 0<δ<π regime explicitly exercised by the consumer.
The consumer covers arbitrary global tangent contractions, torus identification,
literal mutable/angular formulas and uniform growth, and general selected-nonzero
radial conclusions. Its A₂ boundary family has a=(0,-1) and partners=(w,-1)
for arbitrary complex w. A four-coordinate determinant-one family has one zero
mutable coordinate and an independently varying selected nonzero mutable radius,
exercising both negative and nonnegative radial conclusions. An all-frozen family
has a variable exponential radius, and an inhabited dimension-zero seed exercises
the native field.

The consumer invokes unmodified `Lean.collectAxioms` on every imported project
and FsFltz declaration, including private/generated roots, all local consumer
roots, nine mandatory supplements, and explicitly realized lazy equations.
Source-bound delivery evidence records the complete inherited 2294 per-root
results, fresh results, full-name overlap equality, actual native import/source/
output identities, exact checker identity, managed checks, and compiled names.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The optimized audit remains UNADOPTED. Publication preserves all 88 accepted
GlobalPrimitive entries, the exact three accepted TorusLiouvilleDynamics additions,
and unrelated extras, adding only the three owned files: 94 published entries.

Root-owned OPEN obligations remain: boundary coordinate tangency and zero-stratum
invariance, normalized partner dynamics, all-strata growth and two-sided complete
flow, same-flow skeleton equality, final umbrella imports and global packaging,
audit adoption and provenance engineering recovery. This module does not prove
those conclusions or all of Lemma 2.5. Independent Astra/high acceptance and actual
terminal reviewer collection must be established by the delivery records; a
compiled module or this interface alone does not establish mission acceptance.
