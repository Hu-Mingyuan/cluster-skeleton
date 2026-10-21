# Scalar orbit dynamics

This module addresses the scalar radial consequences of manuscript (2.9)--(2.10)
and the frozen part of Proposition 2.6, pp. 10--12 of the pinned manuscript.
It uses the accepted `PrimitiveCutoffs.radial`, native `HasDerivAt`, and actual
`Flow ℝ S.Point`. It constructs neither the cluster vector field nor a complete
cluster flow.

For `ε > 0`, `2*ε+1 ≤ κ`, and `RadialEquation ε κ A c`, the only coefficient
bound in the negative branch is `∀ t ≥ 0, c t ≤ 1`. No continuity, local
boundedness, assumed monotonicity, or uniform negative velocity is imposed.

* `radial_velocity_le` proves the source's pointwise velocity inequality.
* `radial_drift_monotone` derives monotonicity of `x - radial ε κ x` from
  the accepted native derivative bound.
* `radial_le_initial`, `radial_negative`, and `radial_antitone` derive forward
  monotonicity and sign preservation from the ODE, using Mathlib comparison.
* `radial_affine_bound` proves exactly
  `A t ≤ A 0 + (A 0 - radial ε κ (A 0))*t` for nonnegative time and negative
  initial radius. `radial_tendsto_atBot` and `radial_exp_tendsto_zero` give
  escape of the log radius and convergence of its exponential to zero.
* `radial_eq_exp_of_nonneg`, `radial_zero`, and `radial_positive` derive the
  zero and positive cases without even using the coefficient upper bound.
  On each finite interval a strict exponential barrier keeps `A` in the
  zero-cutoff region; a native integrating-factor derivative proves the formula.

For any supplied flow on the literal exchange points, `continuous_frozen_log`
uses `Seed.Point.frozen_ne_zero` to prove global continuity of a frozen log norm.
`frozen_log_orbit` proves its exponential formula under the explicitly stated
native ODE. `trapped_frozen_log_bounded` bounds its absolute value on the actual
compact closure of the forward orbit. `trapped_frozen_norm_eq_one` excludes
both signs of a nonzero initial log norm by exponential growth of its absolute
value. This continuity argument is not asserted for mutable coordinates at zero.
The coordinate cap and dynamical trapped set remain independently defined.

The consumer exercises the genuine cutoff at `ε=1`, `κ=3`: the nonvacuous
negative solutions `A(t)=-exp(t)` and `A(t)=-4-3*t` (the latter has `c=1`
and a nonzero radial correction throughout the genuine affine tail), zero/positive solutions with nonconstant
coefficient `c(t)=-t`, and conditional rigidity. Its two-dimensional all-frozen
seed has a full skew integer determinant-one matrix and empty acyclic mutable
quiver. `variableFrozenPoint z hz` permits every nonzero complex `z`; the
consumer proves the trapped obstruction at these actual points, including a
nonunit example, without inventing a cluster flow.

The final consumer runs unmodified native `Lean.collectAxioms` separately for
each selected declaration, including defining-module attribution and private
name fallbacks, local declarations, lazy equations, and all nine accepted
attribution-sensitive supplements. The delivery artifact records its actual
result together with complete source-matched inherited per-root evidence.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

Ownership is limited to this note, `ClusterSkeleton/ScalarOrbitDynamics.lean`,
and `verification/ScalarOrbitDynamicsConsumer.lean`, on the unchanged accepted
64-entry parent `02d8147d9504291816aaa29b34dd29b1afb9c8c9`. Shared root imports,
upstream sources, the live audit, and the manuscript are unchanged. Native
vector-field construction, proof that the cluster flow satisfies these ODEs,
all-strata completeness, and the full same-flow skeleton equality remain open
with the existing integration owner. Compilation and review receipts, rather
than this interface note, determine delivery acceptance.
