# Pointwise cap angular tangency

This batch proves the pointwise angular assertions used in the converse argument
of Proposition 2.6 of `acyclic_cluster_HMS.pdf` (October 20, 2026; SHA256
`4426e18f96290d63d0650817dc07834e58217516248e7dd10c45470d0a10b666`).
The native coefficient formulas come from the accepted Lemma 2.5 construction.
The exact parent is private126 commit
`8f481a8af5ff40f1b5ee77b140d575b9733fcf8a`, tree
`0df6605ce4c95e28813af08860ddac52828528e6`.
Only the proof module, this interface, and its consumer are added.

The point type is literally `S.Point`, with its inherited topology and the
constructed `SmoothAtlas.presentation S hdet`. The seed uses the full integral
skew-symmetric determinant-one matrix; acyclicity concerns only the mutable
quiver. Frozen coordinates remain independent nonzero variables.
`coordinateCap S` is the accepted coordinate definition, independent of dynamics.

For every cap point, `0 < ε`, `2*ε+1 ≤ κ`, and `0 < δ`, the module proves:

- `LocalAngularDynamics.angularRhs S ε κ δ p p j = 0` for every index.
- `LocalAngularDynamics.nu S ε κ δ p p = 0` using the full matrix inverse.
- The imaginary part of the exact `GlobalLiouvilleField.logarithmicComponents`
  vanishes at every selected nonzero original coordinate, with arbitrary other
  zero coordinates.
- The actual native `coordinateDifferential` of exactly
  `GlobalLiouvilleField.Z` is zero at every coordinate of modulus one.
- Along any actual `IsMIntegralCurveOn` for this same field on any time set,
  cap membership and modulus one at a single time imply the actual
  `HasDerivWithinAt` of that coordinate is zero at that time.

The algebraic angularRhs/nu lemmas are stronger: they only need `2*ε < κ`,
and do not need the determinant or positivity of δ. The native conclusions
retain all parameters of the mission. The curve conclusion needs neither an
open domain nor cap membership throughout the curve; the consumer also obtains
an ordinary derivative on an arbitrary open domain.

The proof reuses `coordinateCap_strictCapIndices_independent` and puts the cap
point in that independent locus. The cap equation makes the interior partner
zero, and the normalized node equation gives `exchangeCharacter = -1` for
interior directions, including zeros. In the accepted center angular formula,
interior summands have angular factor zero. Unit directions have masked log
zero, radial cutoff zero, and actual radial derivative zero. The full
`fderiv_amplitude_apply` formula is retained, including dominance and rho
derivatives. No cross-stratum smoothness is asserted for the moving zero mask.
The accepted all-strata coefficient agreement and native radial equation then
identify the real and imaginary parts of the exact field. The native curve
chain rule differentiates at the current point; there is no whole-curve chart.

Consumers include an A₂ family crossing a zero stratum, both zero and nonzero
strict-interior characters, two simultaneous zero directions in a full
unimodular four-dimensional seed, independently variable frozen unit values,
a mutable unit coordinate with partner explicitly equal to -1, a conditional
consumer for any genuine same-field curve through the A₂ family at time 7 on
(5,9), the initial torus,
empty mutable sets, and dimension zero. Generic consumers retain all strata.

The exact 14 proof declarations are in `ClusterSkeleton.CapAngularTangency`:

- `norm_eq_one_of_not_strict`
- `mem_strict_locus`
- `normalizedPartner_eq_zero_of_interior`
- `exchangeCharacter_eq_neg_one_of_interior`
- `angular_eq_zero_of_interior`
- `maskedLogs_eq_zero_of_unit`
- `radial_and_deriv_zero`
- `amplitude_fderiv_zero_of_unit`
- `angularRhs_eq_zero`
- `nu_eq_zero`
- `logarithmicComponents_im_eq_zero`
- `logarithmicComponents_eq_zero_of_unit`
- `coordinate_drift_eq_zero_of_unit`
- `coordinate_hasDerivWithinAt_zero`


The exact 20 consumer proofs are in `CapAngularTangencyConsumer`:

- `selected_nonzero_all_strata`
- `variable_frozen_coordinate`
- `mutable_boundary_without_partner_premise`
- `arbitrary_open_curve_at_cap_time`
- `literal_carrier`
- `initial_torus_cap`
- `unit_point_native_drift`
- `empty_mutable_native_drift`
- `interiorPoint_mem`
- `strict_nonzero_character`
- `strict_zero_character`
- `nonzero_boundary_partner_native_drift`
- `shifted_open_curve`
- `pair_unimodular`
- `simultaneousPoint_mem`
- `simultaneous_zero_native`
- `frozen_unimodular`
- `independent_frozen_units`
- `empty_unimodular`
- `dimension_zero`


The consumer additionally constructs six concrete definitions:
`interiorPoint`, `pairSeed`, `simultaneousPoint`, `frozenSeed`, `frozenPoint`,
and `emptySeed`. Generated/private declarations are included in the native
per-root audit, together with every imported project/FsFltz declaration and
all nine designated supplements. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. Exact source hashes, managed receipts, inherited
3244-map reconciliation, all 13 original contexts/12 orders, equation and
congruence coverage, and native-output identities are supplied in the
source-bound delivery artifacts. The optimized audit remains unadopted.

Validation is pinned to Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`.
The proof module and direct consumer use targeted managed checks. Exact
source-bound receipts and reconciliation results are recorded in the final
delivery artifacts. An earlier consumer run elaborated and completed its native
audit but was deferred because this interface was written during the managed
snapshot; that attempt is retained as unverified provenance.

This is pointwise tangency. Forward cap invariance, propagation of the strict
interior partner constraints for nonzero original coordinates, global angular
rigidity, and full same-flow skeleton equality remain root-owned obligations.
There is no complete-flow construction or dependency on the unaccepted sibling
lane in this batch. Shared imports, integration, audit adoption, and global
acceptance remain with root mission `df1a0cdf-af80-4485-9c04-b045ff0f3ffb`
and its existing scheduler successor `9c4a3824-04e7-400d-bea7-c0e296a6505a`.
