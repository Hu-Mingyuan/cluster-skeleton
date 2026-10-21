# Native local node drift and boundary tangency

This module uses exactly `GlobalLiouvilleField.Z S hdet ε κ hδ` on
`SmoothAtlas.presentation S hdet`. Points are the actual exchange-equation
subtype with its inherited topology. Frozen coordinates remain variable and
nonzero. The full integer matrix is skew-symmetric with determinant one; only
the mutable quiver is acyclic. No shared imports, targets, upstream sources or
manuscript files are changed.

For ε>0, κ≥2ε+1 and δ>0, `nodeLog_drift` and `nodeProduct_drift` prove, on
exactly `LocalPrimitive.neighborhood S ε κ δ p`, for each i∈p.zeroSet,
D_Z log(1−a_i normalizedPartner_i)=log(1−a_i normalizedPartner_i) and
D_Z(a_i normalizedPartner_i)=(a_i normalizedPartner_i−1)log(1−a_i normalizedPartner_i).
`drift` is the pinned native `complexDifferential` evaluated on the accepted
field. The positive-δ statements imply the requested 0<δ<π regime.
`deep_radius` proves the native scalar derivative of log‖a_i‖ equals −κ
when that selected coordinate is nonzero, even when other coordinates vanish.

`nodeMap_smooth` is reused from NativeNodePrimitive. `nodeLog_smooth`,
`nodeProduct_smooth`, `differential_nodeProduct`, and `differential_nodeLog`
establish the local smoothness and actual native chain rules. The logarithm
is differentiated only on its proved slit-plane domain; the product sign is
positive to first order at zero, as on manuscript page 11, Lemma 2.5.
`differential_nodeLog_torus` uses the native full-matrix character derivative.
`row_real_drift_torus` retains all frozen columns. `local_H_radial` follows
from actual amplitude pullback germs: the selected partial is one, adjacent
partials vanish on an open neighborhood, and nonadjacent partials vanish by
the explicit derivative formula. Pointwise plateau values are never used as
substitutes for derivative identities. `contMDiffOn_complexDerivative`
composes the native tangent map with the smooth vector section. Density extends
the continuous local log drift only across the specified OPEN neighborhood.

`coordinate_tangent` proves for every actual point p and every finite index i
that p.a i=0 implies P.coordinateDifferential i p (Z p)=0. It does not require
a supplied tangency witness or a partner nonvanishing assumption.
`zero_coordinate_tangent_of_partner_ne_zero` first uses the native product rule.
For a zero partner, `boundaryPerturb` varies only b_i by t Q_i, leaving every a
and every other b fixed. Its exchange equations, continuity, unchanged zero set,
value at t=0 and normalized-partner translation are proved. The punctured
complex-parameter limit therefore stays in the SAME zero stratum.
`boundaryPerturb_eventually_mem` also proves eventual membership in the center's
same local neighborhood. There is no division by a zero coordinate or zero partner.

The consumer tests literal `mfderiv` identities and local smoothness generically,
arbitrary-point native tangency, A₂ boundary points with arbitrary complex partner
including zero, a determinant-one four-dimensional seed with two simultaneous
zeros and arbitrary partners, selected nonzero deep radii while a different
mutable coordinate stays zero, an actual punctured family eventually in the
neighborhood, variable frozen coordinates, empty mutable sets, and an inhabited
dimension-zero seed. These tests concern the same accepted global field.

The final source-bound delivery records the complete declaration inventory,
managed exact-source module/consumer/combined checks, every inherited 2551
per-root transitive axiom result, all fresh project/FsFltz/private/generated/
consumer roots, nine mandatory supplements and inherited/new lazy equations.
It compares full declaration names and axiom sets, actual import sequences and
source/native-output/checker identities. Only propext, Classical.choice and
Quot.sound are allowed. The optimized audit remains UNADOPTED. Publication must
be exactly the accepted 94 path/mode/blob/SHA256 entries plus these three owned
files, with unrelated local extras preserved.

Root-owned OPEN targets remain zero-stratum invariance along genuine integral
curves, normalized-partner dynamics, all-strata growth and two-sided complete
flow, and the same-flow skeleton equality. The existing GeometryTarget
propositions remain unresolved; none is asserted as a consequence of pointwise
tangency. Root successor e0b24dd7-8e9a-4d2a-9765-585916fe1e00 retains sole final
shared imports, integration and packaging. Independent mathematical/manuscript/
native-calculus acceptance and actual terminal reviewer collection are separate
delivery evidence; compilation alone does not establish mission acceptance.
