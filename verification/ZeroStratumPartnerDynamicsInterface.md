# Native zero-stratum partner dynamics

This module composes the accepted ZeroStratumInvariance and
NormalizedPartnerNormDrift interfaces on the literal complex exchange-equation
carrier, its induced topology, SmoothAtlas.presentation and exactly
GlobalLiouvilleField.Z. Frozen coordinates remain nonzero variables. The full
integer matrix is skew-symmetric with determinant one; only the mutable quiver
is acyclic.

For ε>0, κ≥2ε+1 and δ>0, let γ be a native IsMIntegralCurveOn of this field
on a preconnected J⊆ℝ. If s,t∈J and the original mutable coordinate a_i(γ s)
is zero, normSq_eq_exp_mul proves

    normSq(normalizedPartner (γ t) i)
      = exp(2*(1+κ)*(t-s))*normSq(normalizedPartner (γ s) i).

The positive-δ scope includes 0<δ<π. There is no neighborhood-confinement,
complete-flow, invariant-stratum or solution-formula premise. Native
coordinate_zero_iff first proves a_i(γ u)=0 for each u∈J. The accepted global
pointwise normSq_hasDerivWithinAt_zero then supplies the actual
HasDerivWithinAt of the squared normalized-partner norm on J. The scalar
helper differentiates exp(c*(t-u))*f(u), with c=2*(1+κ). Its derivative is
zero; the native convex mean-value norm estimate proves equal values at s
and t. Preconnected real sets are convex. No division or unique-derivative
hypothesis is needed, including for singleton sets and relative endpoints.

partner_zero_iff and partner_ne_zero_iff give persistence in both time
directions. normSq_lt gives strict growth when s<t and the initial partner
is nonzero. strictMonoOn_normSq propagates this to the whole domain. The exact
law also includes zero partners and arbitrarily many simultaneous zeros.

The consumers combine the original-coordinate invariance, literal mfderiv,
actual within-derivative and integrated law. They cover reversed times,
closed-interval endpoint derivatives, singleton domains, A₂ initial points
with arbitrary and zero partners, simultaneous zero coordinates with arbitrary
partners, a simultaneous zero/growing partner pair, and independent variable
frozen data. Empty mutable scope is stated explicitly; dimension zero has an
inhabited actual all-time constant native curve and no mutable coordinate.
The nonzero-dimensional curve consumers are conditional on genuine curves;
this module does not construct those curves or assert their completeness.

## Compiled theorem inventory

ClusterSkeleton.ZeroStratumPartnerDynamics (7):
exp_law_of_hasDerivWithinAt, normSq_hasDerivWithinAt, normSq_eq_exp_mul,
partner_zero_iff, partner_ne_zero_iff, normSq_lt, strictMonoOn_normSq.

ZeroStratumPartnerDynamicsConsumer (19):
native_composition, both_time_directions, strict_growth,
closed_interval_endpoints, singleton_domain, boundary_coordinates,
pair_unimodular, frozen_unimodular, empty_unimodular, a2_partner,
double_partners, a2_arbitrary_partner_curve, a2_zero_partner_curve,
simultaneous_partners_curve, simultaneous_zero_and_growing_partner,
variable_frozen_curve, empty_mutable_scope, frozen_only_family,
dimension_zero_native_curve.

The seven consumer fixture definitions are boundaryPoint, pairSeed, frozenSeed,
frozenPoint, emptySeed, doubleBoundary and variableFrozenBoundary. They are
actual seeds/exchange points. The accepted original declaration blocks remain
unchanged in isolated composition checkers to preserve generated-name identities.

## Source and verification contract

Input union103 is artifact ad8ecb82-5d0a-4d97-bec8-050f37918fc2,
SHA256 95e16897c9395060a009baf0c7bfd4f04d6435f93e9fd66ac2f9b68d9ea621c0,
422507 bytes. Publication uses accepted zero100 commit
d7555db1362ccec8ff0636e5e0fa064532764761 as parent, adds unchanged norm3 from
bfe4cd2f9cfdeae2ffe411fa0db6483f97de5795 and only these three new owned files:
exact106. Every old path/mode/blob/SHA and unrelated local extra is preserved.

The delivery evidence records managed exact-source module, consumer and
composition checks under Lean4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
and FsFltz 1a3d387cfacc746e25aad31e5b27b1803103e7cb. It carries all2785 inherited
per-root native axiom results and fresh project/FsFltz/private/generated/consumer
results, exact-name overlap comparisons, all9 supplements, and inherited/new
lazy equations. It records source, ordered-import, native-output and checker
identities. The only permitted axioms are propext, Classical.choice and
Quot.sound; the optimized audit remains UNADOPTED. Exact publication, independent
Astra/xhigh manuscript/native review and its actual terminal collection, bounded
maintainer acceptance and its actual durable terminal collection are separate
receipts. Compilation alone is not mission acceptance.

The manuscript is acyclic_cluster_HMS.pdf (2026-10-20), Lemma2.5, page11,
specifically the asserted exponential norm consequence of (2.11).
This bounded real norm law does not establish the smooth angular coefficient
or the full complex equation (2.11). All-strata growth, two-sided complete flow,
and the same-flow skeleton equality remain OPEN. ScalarOrbitDynamics77 is not
an input and is not imported. GeometryTarget and the independently defined
coordinate cap and trapped set are unchanged. Root mission
df1a0cdf-af80-4485-9c04-b045ff0f3ffb and its scheduler successor retain every
original stage3–6 criterion and sole shared-import/final-integration/packaging,
audit-adoption and provenance-recovery ownership. No phase/global acceptance
is claimed.
