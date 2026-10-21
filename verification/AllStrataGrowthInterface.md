# Uniform native growth on every zero stratum

Mission 133 (`cdf98864-2b86-4c95-a6d9-7821946b55c6`, revision 1) extends the
exact accepted 120-file parent
`f57c1e084ce8e7a49e0d0a0825603b396980b55f`, tree
`ab5ed2d2cd7007a08454b7532a1e177c49db5658`, by only this interface,
`ClusterSkeleton/AllStrataGrowth.lean`, and
`verification/AllStrataGrowthConsumer.lean`. All accepted source bytes, file
modes and unrelated audit extras are preserved. The versioned objective is
revision 4 at `4c28a63587f7e2778d84e03b3e2bca3f0121137a`.

## Mathematical interface

The carrier is the literal exchange-equation subtype `S.Point` with its
inherited topology. Geometry uses `SmoothAtlas.presentation S hdet` and the
exact accepted native `GlobalLiouvilleField.Z`. The full integer matrix is
skew-symmetric with determinant one; only the mutable quiver is acyclic.
Frozen coordinates remain nonzero variables.

For `ε > 0`, `2*ε+1 ≤ κ`, and `δ > 0`, define
`R S p = ∑ j, |LocalAngularDynamics.maskedLogs S p.zeroSet p j|`.
The manuscript range `δ < π` is included; none of these estimates needs that
upper bound. `uniform_growth` proves one `C > 0`, quantified before all points,
indices and partner values, satisfying:

1. The sum of absolute real components of the actual native logarithmic
   derivative outside `p.zeroSet` is at most `C * R S p`.
2. The sum of absolute center `nu S ε κ δ p p j` over **all** full-matrix
   indices is at most `C * (1 + R S p)`.
3. The sum of `|Re G_j| + |Im G_j|` outside `p.zeroSet`, for the actual native
   `GlobalLiouvilleField.logarithmicComponents`, is at most `C * (1 + R S p)`.
4. At each mutable zero index, the norm of the actual complex differential of
   `normalizedPartner` applied to that same `Z` is at most
   `C * (1 + R S p) * ‖normalizedPartner p i‖`.

`nodeLog_center_zero` derives `log(1)=0` from the actual zero coordinate.
`angularRhs_center` removes those singular summands, and bounds every surviving
summand using the accepted amplitude derivative and order-zero angular bounds.
`full_matrix_nu_equation` proves the full matrix equation by determinant-one
inversion, including frozen rows and columns. It is valid for arbitrary centers
and evaluation points. The growth estimate itself concerns the diagonal
center value `p,p`; it is not a uniform neighborhood estimate for an arbitrary
fixed center.

`radial_growth` uses the accepted selected-coordinate radial defect bound,
`radial_abs_le`, and the native identity `L_eq_logarithmicComponents`.
`complex_growth` identifies `nu` with the actual imaginary component only on
the nonzero complement. `partner_drift_growth` applies the accepted
`partner_drift_zero` equation at the actual center, then takes its complex norm.
It never divides by the partner, so arbitrary partners, including zero, are
covered. `frozen_mem_compl` explicitly retains every frozen index.

## Native curves

`integralCurve_growth` takes a genuine Mathlib `IsMIntegralCurveOn` of the exact
`Z` on an arbitrary preconnected time set. It fixes the initial zero set using
the accepted `ZeroStratumInvariance.zeroSet_eq`. All four estimates use that
fixed mask. For each complementary coordinate it supplies both a real masked
logarithm `HasDerivWithinAt` and the complex local logarithm derivative of
`u ↦ log ((γ u).a j / (γ t).a j)` at the current time. At every initial zero
index it supplies the genuine complex partner derivative and its norm bound.

The complex logarithm chain rule is applied at the normalized value `1`, where
the actual coordinate is nonzero. The partner chain rule uses the neighborhood
centered at the current point. No whole-curve chart membership or caller-supplied
scalar/angular ODE is a premise. The consumer on the open time interval `Ioi 5`
with initial time `7` converts these within derivatives to ordinary derivatives.
No continuity or differentiability of the point-dependent mask across strata is
asserted, and no absolute-value sum is differentiated.

## Exact theorem inventory

The 18 module theorems below have compiled in the managed module build:

- `ClusterSkeleton.AllStrataGrowth.R_nonneg`
- `ClusterSkeleton.AllStrataGrowth.R_eq_sum`
- `ClusterSkeleton.AllStrataGrowth.coordinate_ne_zero_of_mem_compl`
- `ClusterSkeleton.AllStrataGrowth.frozen_mem_compl`
- `ClusterSkeleton.AllStrataGrowth.radial_growth`
- `ClusterSkeleton.AllStrataGrowth.normalizedLog_hasDerivWithinAt`
- `ClusterSkeleton.AllStrataGrowth.angularRhs_center`
- `ClusterSkeleton.AllStrataGrowth.full_matrix_nu_equation`
- `ClusterSkeleton.AllStrataGrowth.angularRhs_center_bound`
- `ClusterSkeleton.AllStrataGrowth.nu_center_growth`
- `ClusterSkeleton.AllStrataGrowth.partner_coefficient_norm_le`
- `ClusterSkeleton.AllStrataGrowth.partner_drift_growth`
- `ClusterSkeleton.AllStrataGrowth.nodeLog_center_zero`
- `ClusterSkeleton.AllStrataGrowth.complex_growth`
- `ClusterSkeleton.AllStrataGrowth.uniform_growth`
- `ClusterSkeleton.AllStrataGrowth.fixed_mask_hasDerivWithinAt`
- `ClusterSkeleton.AllStrataGrowth.partner_center_hasDerivWithinAt`
- `ClusterSkeleton.AllStrataGrowth.integralCurve_growth`

The consumer defines `GrowthAt` as the four explicit inequalities and contains
the following 18 compiled theorems. Their source-matched combined proof check
passed; the separate complete native audit receipt is recorded in the delivery:

- `AllStrataGrowthConsumer.uniform_native_growth`
- `AllStrataGrowthConsumer.selected_coordinate`
- `AllStrataGrowthConsumer.R_eq_log_norm_sum`
- `AllStrataGrowthConsumer.literal_carrier_and_frozen`
- `AllStrataGrowthConsumer.triple_size`
- `AllStrataGrowthConsumer.triple_partners`
- `AllStrataGrowthConsumer.triple_uniform_growth`
- `AllStrataGrowthConsumer.triple_zero_partners`
- `AllStrataGrowthConsumer.triple_open_time_growth`
- `AllStrataGrowthConsumer.a4_size`
- `AllStrataGrowthConsumer.a4_nonvacuous_uniform_growth`
- `AllStrataGrowthConsumer.variable_frozen_size`
- `AllStrataGrowthConsumer.variable_frozen_uniform_growth`
- `AllStrataGrowthConsumer.torus_uniform_growth`
- `AllStrataGrowthConsumer.empty_mutable_uniform_growth`
- `AllStrataGrowthConsumer.frozen_size`
- `AllStrataGrowthConsumer.frozen_two_parameters`
- `AllStrataGrowthConsumer.dimension_zero_application`

The only new mathematical definitions are `AllStrataGrowth.R` and
`AllStrataGrowthConsumer.GrowthAt`. The former is a size function, and the latter
is inhabited uniformly by the proved theorem; neither substitutes for a proof.

## Verification and ownership

The pins remain Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`. The consumer uses a private combined
fixture with byte-identical accepted proof ranges and their accepted EOF-scope
restoration. Five inherited audit-only command blocks are omitted with exact
byte intervals and hashes recorded; only the fresh native collector executes. A standalone check of this dependent consumer is not claimed.
Its actual fixture, ordered imports, source identities, native outputs, checker,
receipts and full per-declaration axiom maps are supplied with the private
delivery. The collector remains native `Lean.collectAxioms`; the optimized audit
is **UNADOPTED**.

The complete accepted evidence from delivery
`56147a64-a613-4509-92f7-100c2c4718eb`, complete-map artifact
`852e0576-d173-411f-82e2-5a1bea3dcea8`, and archive
`35def607-90c9-4176-b7e1-95208079ed24` is carried by exact identity: all 3158
inherited per-root maps, nine supplements, 13 historical contexts, 12 ordered
projections, 287 lazy equations, 41 congruences, and 5181 native module
identities. Fresh source/import closure is checked separately, with full-name
overlap equality and every new project/private/generated/consumer declaration.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The accepted
fixture-scope correction and its failed-attempt provenance remain evidence.

This is a pointwise growth result. Finite-time compact confinement, native
continuation, the actual two-sided complete flow, cap invariance, angular
rigidity, interior partner constraints and the full same-flow skeleton theorem
remain with root mission `df1a0cdf-af80-4485-9c04-b045ff0f3ffb`, Planner 114,
and its existing scheduler successor 117
`c966b200-2920-4212-9f34-97d59a0c6ff7`. Their original criteria and manifests
`6a0e2320` / `26f582dc` are unchanged. This batch is neither global acceptance
nor a blanket prerequisite for independent cap work. Private publication, independent review, bounded maintainer acceptance and
actual native/durable execution collections are separate requirements. Their
exact statuses and receipts are recorded in the private delivery; compilation
alone does not establish mission acceptance.
