# Native torus Liouville dynamics

Owned module: `ClusterSkeleton/TorusLiouvilleDynamics.lean`.
Consumer/checker: `verification/TorusLiouvilleDynamicsConsumer.lean`.

The carrier is the accepted `Seed.Point` of actual complex exchange solutions,
with its inherited topology and `SmoothAtlas.presentation S hdet`. Frozen
coordinates remain nonzero variables. The integer matrix is the entire
skew-symmetric determinant-one matrix; only the mutable neighbor set enters the
dominance cutoff. All statements about the totalized torus primitive and vector
are restricted to `initialTorus S`.

## Source correspondence and public conclusions

The source is `references/acyclic_cluster_HMS.pdf`, SHA256
`4426e18f96290d63d0650817dc07834e58217516248e7dd10c45470d0a10b666`,
pages 10–12: (2.7), (2.9), (2.10), Lemma 2.5 and Proposition 2.6.
Names below are in `ClusterSkeleton.TorusLiouvilleDynamics`.

- `Z` is exactly the pinned native `M.liouvilleVector` of the accepted
  `TorusCorrection.alpha`. `logarithmicComponents` are its native coordinate
  differentials divided by the nonzero coordinates.
- `contraction` proves contraction with the actual `GlobalTwoForm.omega`
  against every native tangent. `native_equation_exists` proves finite
  dimensional solvability from native nondegeneracy using Euclidean duality;
  the accepted `exteriorDerivative_alpha`, torus nondegeneracy and logarithmic
  tangent equivalence supply its hypotheses.
- `mutable_radial_equation` gives the literal correction in (2.9), including
  native `deriv vartheta`; `frozen_radial_equation` gives `ZA_f = A_f` for every
  variable frozen coordinate. `dominance_angular_derivative_zero` and
  `differential_H_angular` explicitly remove dominance derivatives from this
  radial equation. Full-matrix injectivity yields the component formula.
- `angular_equation` identifies the full row pairing of imaginary components
  with the actual differential on `radialTangent`, which is the inverse
  logarithmic tangent equivalence applied to the real coordinate basis.
  `differential_H_radial` computes this differential by the actual native
  amplitude derivative; its subsequent bound is proved, not assumed.
- `logarithmicHamiltonian` is the literal lifted Hamiltonian. The global value
  identity `H_logarithmic_identity`, smooth local logarithm
  `localLog_contMDiffAt`, and `H_logarithmic_germ` connect it to the accepted
  `TorusCorrection.H`. `differential_H_logarithmic` proves the native chain
  rule for arbitrary tangents. `angular_equation_partial_deriv` identifies
  the angular equation with the ordinary partial radial derivative.
  `hasFDerivAt_vartheta_arg` uses a smooth local angle at every nonzero base
  point, including the principal argument cut; `vartheta_deriv_representative`
  proves independence of integer-period representatives.
- `radial_eq_of_nonneg`, `radial_zero`, and `radial_negative_bound` prove all
  requested radial sign assertions (also for frozen indices).
- `chi_deriv_compactSupport`, `chi_deriv_bound`,
  `fderiv_dominance_apply`, `dominance_partial_bound`, and
  `fderiv_amplitude_apply` derive the derivative estimates from the accepted
  literal cutoffs. `amplitude_partial_bound`, `real_components_growth`,
  `full_matrix_inverse_bound`, and `imaginary_components_growth` combine them.
  `logarithmic_linear_growth` proves a finite positive constant depending only
  on the fixed seed and parameters, uniformly over all actual torus points.

No theorem assumes the field formula, a derivative supplied by a caller, growth,
coercivity, a global extension, or completeness. The consumer quantifies all
allowed parameters (`epsilon > 0`, `kappa >= 2 epsilon + 1`, `0 < delta < pi`);
some module conclusions hold under weaker parameter restrictions.

## Consumer coverage and trust

The consumer tests arbitrary actual native tangents, the literal mutable formula,
the full angular partial derivative, signs and uniform growth. It includes empty
mutable sets, dimension zero, a mixed mutable/frozen determinant-one matrix,
varying frozen coordinates, a point with nonzero Hamiltonian and native radial
correction (the mutable component changes from -5 to -3), and an actual torus
point on the principal argument cut. Its native `Lean.collectAxioms` audit covers
all imported project/FsFltz modules by defining-module attribution plus public
and private name fallback, every local declaration, and nine inherited generated
supplements; lazy equations are explicitly realized. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. Exact managed-check receipts,
per-root overlap reconciliation, source/import/olean identities and publication
receipts belong to the delivery evidence artifact.

## Boundary of this delivery

This is torus computation and growth only. It does not assert global smoothness
of the totalized alpha or Z, global primitive extension, all-strata completeness,
a complete flow, or the skeleton theorem. The coordinate cap and trapped set
remain independently defined. Those global composition obligations remain with
root `df1a0cdf-af80-4485-9c04-b045ff0f3ffb` through existing successor75
`e23fab2f-a182-46fe-93a1-55fe26fa88f9`.

The source base is the exact accepted TorusCorrection64 commit
`02d8147d9504291816aaa29b34dd29b1afb9c8c9` (tree
`cb0eba46ddebc6bfafd9dd721597cd161a878dae`). This delivery preserves those
64 entries and adds only the module, consumer, and this interface (67 entries).
