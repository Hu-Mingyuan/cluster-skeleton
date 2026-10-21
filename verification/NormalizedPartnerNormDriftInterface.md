# Native normalized-partner squared-norm drift

The module uses exactly `GlobalLiouvilleField.Z S hdet ε κ hδ` on
`SmoothAtlas.presentation S hdet`, the actual exchange-equation complex points
with their induced topology. Frozen coordinates remain nonzero variables. The
full integer matrix is skew-symmetric and unimodular; only its mutable quiver
is acyclic. The statements assume ε>0, κ≥2ε+1 and δ>0, which strengthens the
requested 0<δ<π regime.

For every center p, mutable i∈p.zeroSet and q in the actual OPEN set
`LocalPrimitive.neighborhood S ε κ δ p`, `normSq_drift` proves

    D_Z normSq(b) = 2 Re(conj(b) (z b − 1) nodeLogQuotient(z,b)) + 2 κ normSq(b),
    z = q.a i,  b = normalizedPartner q i.

The quotient is the accepted removable extension of log(1−z b)/z, whose value
at z=0 is −b. It is not log(1−z b)/(z b). `normSq_drift_zero` proves at EVERY
actual q with q.a i=0 that D_Z normSq(b)=2(1+κ)normSq(b), including b=0 and
arbitrary simultaneous zeros.

The native product/chain rules use the smooth actual node map.
`partner_drift_of_ne_zero` divides only by a proved nonzero original coordinate;
it never divides by the partner. The proof then uses accepted `deep_radius`
and an explicit real pairing. `quotient_smooth` establishes smoothness on the
proved slit-plane branch domain using `contDiffOn_nodeLogQuotient`. The native
scalar derivative and the complete right-hand expression are continuous on
the open neighborhood. `normSq_drift` applies accepted torus density within
that open set, including its mixed strata. The zero-coordinate specialization
uses the actual removable value and no division.

`normSq_hasDerivWithinAt` and `normSq_hasDerivWithinAt_zero` consume a genuine
`IsMIntegralCurveOn` of THIS global field, on an arbitrary time set. They give
native `HasDerivWithinAt` statements at a time belonging to that set. The local
version assumes only membership of that point in the stated neighborhood;
the zero version assumes only the selected coordinate is zero at that point.
Neither assumes the curve stays in the neighborhood or zero locus.

The 14 module theorems are `partner_smooth`, `differential_partner`,
`normSq_smooth`, `scalarDerivative_normSq`, `partner_normSq_smooth`,
`quotient_smooth`, `partner_drift_of_ne_zero`, `pairing_sub`,
`normSq_drift_of_ne_zero`, `normSq_drift`, `normSq_drift_zero`,
`hasDerivWithinAt_scalar_along_integralCurve`, `normSq_hasDerivWithinAt`, and
`normSq_hasDerivWithinAt_zero`, all in `ClusterSkeleton.NormalizedPartnerNormDrift`.

The companion consumer exercises literal native `mfderiv` and scalarDerivative,
the norm-square expression, both genuine-curve bridges, actual A₂ boundary
points with arbitrary complex partners including zero, two simultaneous zeros
with independent arbitrary partners, and arbitrary nonzero frozen coordinates.
Its `mixedPoint t v` has originals (1−exp(t),−exp(t),0,−1) and normalized
partners (1,v). For every nonzero real t sufficiently near zero it lies in
the SAME open neighborhood of `doubleBoundary 1 v`; the first original and
partner are nonzero while the second mutable original is zero. Thus
`mixed_norm_drift_eventually` tests the extension on a nontrivial norm-square
outside the initial torus. Empty mutable and inhabited dimension-zero seeds
are exercised with their actual lack of mutable norm equations; the latter
also checks the literal native derivative of a constant squared norm.

Compiled declarations, exact-source managed checks, per-root native axiom
maps, inherited overlap comparisons and publication identities are recorded
in the delivery artifact. The audit retains all 2639 inherited roots, all nine
mandatory supplements, 230 inherited lazy equations and all new generated,
private and consumer roots. It uses unmodified `Lean.collectAxioms` and allows
only propext, Classical.choice and Quot.sound. The optimized audit remains
UNADOPTED. New-import composition checks isolate inherited consumer declaration
blocks to preserve generated-name identities.

Publication is the accepted 97-file commit
`28cd68ae9627f1826a99b9feae5a55b9520d72d1` plus ONLY this module, consumer and
interface (exactly 100 files). Existing modes/blob IDs/SHA256 hashes and unrelated
local extras are preserved. Shared imports, upstream sources and the PDF are
unchanged. Independent review and maintainer acceptance remain separate from
successful compilation.

This is squared-norm dynamics only. It does not prove the smooth angular
coefficient or the full complex normalized-partner equation (manuscript page
11, Lemma 2.5, equation 2.11), zero-stratum invariance, global growth, complete
flow, or the same-flow skeleton theorem. ZeroStratumInvariance remains owned
by sibling mission112 / author97; it is not imported. The root mission retains
the full complex equation, angular coefficient, all-strata growth, two-sided
completeness, same-flow skeleton, shared imports and final integration through
successor96 `68949252-bca3-474a-bf13-6e417f9d50d3`. No required criterion has
been removed or replaced by the norm-square result.
