# Native radial orbits

This bounded module proves radial consequences of manuscript (2.9)–(2.10)
and the radial necessary conditions in Proposition 2.6, pp. 10–12 of the pinned
`acyclic_cluster_HMS.pdf`. The carrier is literally `S.Point` with its inherited
topology and `SmoothAtlas.presentation S hdet`. `Seed` retains the full integer
skew matrix and acyclic mutable subquiver; `hdet` is determinant one. Frozen
coordinates remain independently variable nonzero coordinates.

The field is exactly `GlobalLiouvilleField.Z`. On the torus the bounded first
derivative of `vartheta`, and dominance/rho in [0,1], give a constant independent
of point and index bounding `|L-A|` by `C*|radial A|`. Continuity extends this
inequality only on the open locus where the selected coordinate is nonzero.
Other coordinates may vanish simultaneously. Thus `radial A=0` implies `L=A`,
including the boundary `A=-2*epsilon`. The totalized quotient `c=(A-L)/radial A`
is derived from that field; its exact equation is justified also when the
denominator vanishes. The accepted native negative-drift estimate proves `c≤1`.

A genuine native integral curve on `Ioi (t₀-η)`, with `η>0`, needs just one initial
nonzero-coordinate premise. Accepted zero-stratum invariance propagates it.
The native manifold chain rule and the openness of the time domain give ordinary
`HasDerivAt` derivatives, including at shifted time zero. The unchanged accepted
`ScalarOrbitDynamics` results then supply the negative affine bound, sign,
antitonicity, logarithmic limit and radius limit, zero rigidity, and positive
exponential law. The module proves these for all `δ>0`; the manuscript's stricter
`δ<pi` remains available in consumer statements.

A compact set bounds each continuous original-coordinate norm, even if it meets
larger zero strata. This gives eventual avoidance of every compact set when an
initial norm exceeds one, and noncompact forward closure. For an existing
native `Flow` whose every orbit solves the exact field on `univ`, membership in
the existing independently defined `trappedSet` implies every original norm is
at most one and every frozen norm is one. The frozen scalar theorem's ODE premise
is discharged by the native chain rule and the exact frozen radial equation.
No mutable logarithm is asserted continuous at zero.

The compiled module theorems, all in `ClusterSkeleton.NativeRadialOrbit`, are:

- `amplitude_abs_le_radial`
- `uniform_radial_error_bound`
- `L_eq_A_of_radial_eq_zero`
- `L_eq_A_of_ge_cutoff`
- `L_eq_A_sub_radial_mul_c`
- `c_le_one`
- `hasDerivAt_A`
- `coordinate_ne_zero`
- `shifted_hasDerivAt_A`
- `radialEquation`
- `negative_log_laws`
- `nonnegative_log_law`
- `positive_log_law`
- `zero_log_law`
- `eventually_not_mem_compact`
- `not_isCompact_closure_forward_image`
- `original_norm_le_one_of_mem_trappedSet`
- `frozen_log_hasDerivAt`
- `frozen_norm_eq_one_of_mem_trappedSet`
- `trapped_radial_restrictions`

The sole new non-proof definition is `c`. Compilation receipts and full per-root
axiom evidence, including generated declarations, are delivered separately.
The standalone consumer theorems, all in `NativeRadialOrbitConsumer`, are:

- `cutoff_boundary`
- `shifted_time_seven`
- `supplied_flow_trapped`
- `empty_mutable_trapped`
- `triple_unimodular`
- `triple_coordinates`
- `triple_selected_nonzero`
- `triple_zeroSet`
- `triple_selected_log`
- `triple_cutoff_boundary`
- `triple_two_zeros_persist`
- `triple_positive_log`
- `triple_zero_log`
- `triple_negative_logs`
- `frozen_unimodular`
- `frozen_coordinates`
- `frozen_norms`
- `frozen_logs`
- `frozen_trapped_norms`
- `frozen_trapped_parameters`
- `frozen_not_trapped_of_nonzero_parameter`
- `frozen_both_sides_of_one`
- `triple_positive_escape`
- `empty_unimodular`
- `dimension_zero_flow_native`
- `dimension_zero_trapped`

These consumers use a six-coordinate block-skew determinant-one seed with
mutable set {0,2,4}. Its selected mutable radius is exp(x), while both other
mutable coordinates are zero with independently free partners. This exercises
the closed cutoff boundary and positive, zero, and negative log cases on mixed
strata, including compact escape and two persistent zeros. A second all-frozen
two-coordinate seed varies exp(x), exp(y) independently and tests each sign in
each coordinate. The shifted-time consumer uses time 7 in Ioi(5), including a
genuine HasDerivAt at the shifted origin. The zero-dimensional consumer supplies
an actual native identity flow and a trapped point and invokes the same theorem.

The module and standalone consumer compile with managed exact-source receipts.
The final receipt/axiom/publication index and independent review/maintainer
acceptance are separate evidence; this note does not establish acceptance.

Ownership is exactly this note, `ClusterSkeleton/NativeRadialOrbit.lean`, and
`verification/NativeRadialOrbitConsumer.lean`. Publication must have the exact
accepted composition114 parent `30c504f954079417ae78e38af42418709eaa0ebc`, its
114 unchanged entries, three byte-identical additions from accepted scalar67
`3107ec5e2d93d3bfa4ee20fb740ad27be6b19004`, and these three fresh files: 120 entries.
Physical unrelated extras remain preserved. Shared imports, accepted proofs,
the PDF, and upstream sources are unchanged; optimized audit remains unadopted.

Root mission `df1a0cdf-af80-4485-9c04-b045ff0f3ffb`, through its existing
integration/scheduler owner, retains all-strata growth, the complete two-sided
native flow, cap invariance, remaining angular rigidity and partner constraints,
full same-flow skeleton equality, final integration/packaging, audit adoption,
and provenance with every original root/stage3–6 criterion. This module does
not construct a complete flow or establish those outcomes. Their independent
investigation does not depend on acceptance of this bounded consequence.
