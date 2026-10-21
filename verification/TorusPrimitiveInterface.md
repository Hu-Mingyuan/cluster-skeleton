# Native torus primitive

Source: `acyclic_cluster_HMS.pdf`, pp. 9–10, equation (2.7). Baseline:
`6b99d39f5a9102c9749100054a66a7475769eb4b`, with all 52 accepted files and modes preserved.

`ClusterSkeleton.TorusPrimitive` directly imports the accepted `GlobalTwoForm`.
For every `Seed d` and `hdet : S.Unimodular`, all forms live on
`(SmoothAtlas.presentation S hdet).manifold`, whose points and topology are the
actual exchange-equation subtype. Frozen coordinates remain nonzero variables.

* `angleCovector` is `Im(a_j⁻¹ da_j)`, using `P.coordinateDifferential`.
* `beta` is the native covector form `Σᵢⱼ Bᵢⱼ log ‖aᵢ‖ angleCovectorⱼ`.
  `evalOne_beta` fixes its normalization: no half, minus, or inverse matrix.
* `contDiffAt_beta_inChart` proves smoothness of its coefficients at every
  torus point in every native chart.
* `exteriorDerivative_beta p hp` identifies its actual exterior derivative with
  the exact accepted `GlobalTwoForm.omega S hdet p`. The torus premise is explicit.
* `alpha H` subtracts `covectorForm M (differentialCovector M H)` from `beta`.
  `evalOne_alpha` exposes the actual native derivative of the ordinary function H.
* `contDiffAt_alpha_inChart` and `exteriorDerivative_alpha` require only native
  `ContMDiffOn ... ∞ H (initialTorus S)`, and retain torus membership.
  `alpha_zero` identifies the zero correction with beta.

The calculus proof uses a normalized logarithm germ at each torus point.
The affine one-form in these coordinates differentiates to the accepted
`matrixForm`, by integer skew symmetry. Native pullback and chart transport
then give the derivative identity. The correction uses local chart derivatives
and native `extDeriv_extDeriv_apply`; no global smoothness of beta or H is assumed.
Totalized logarithms at zero are definitions only and supply no extension proof.

`TorusPrimitiveConsumer.lean` checks arbitrary dimensions and torus points,
ordinary torus-smooth H, zero H, a proved nonconstant coordinate H, an inhabited
zero-dimensional seed, and actual A₂ beta and derivative evaluations equal to 1.
Its native `Lean.collectAxioms` selection includes every defining-module root,
private/generated roots, local consumer roots, and all nine inherited supplements.
The separate delivery evidence carries all 671 accepted inherited results with
their unchanged source identities. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.

OPEN under the existing integration/primitive/flow owners: construction of the
manuscript H and its cutoff data; boundary cancellation, gluing, and a global
smooth primitive; a complete native Liouville flow; and the full same-flow
skeleton equality. This torus calculus prerequisite proves none of these.
