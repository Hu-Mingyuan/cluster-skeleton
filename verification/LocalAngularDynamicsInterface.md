# Local angular dynamics interface

This batch constructs a smooth real angular coefficient for the **exact**
`GlobalLiouvilleField.Z` and proves the full complex normalized-partner equation
on `LocalPrimitive.neighborhood S ε κ δ p`. The mathematical source is
`acyclic_cluster_HMS.pdf` (2026-10-20), page 11, Lemma 2.5, the displayed coordinate
equation and Eq. (2.11); page 11 was inspected visually against the pinned PDF.
It establishes these local equations, not the remaining completeness argument.

## Contract and construction

The carrier is the literal `Seed.Point` exchange-equation subtype with inherited
topology and `SmoothAtlas.presentation`. The full integer matrix is skew-symmetric
and determinant one; only the mutable quiver is acyclic. Frozen coordinates are
nonzero variables. No extra dimension, nonempty mutable set, single-zero, or
nonzero-partner hypothesis is used.

Let `I = p.zeroSet`, `U = LocalPrimitive.neighborhood S ε κ δ p`.
`maskedLogs` puts zero in coordinates in I and `log ‖q.a j‖` in the remaining
coordinates. This is native smooth on `candidateChartLocus S I`.
`angularRhs` is the finite sum of the singular node-log terms and surviving
amplitude derivatives; adjacent terms are zero. `nu` applies the inverse of the
**full real matrix** to this explicit vector.

`amplitude_fderiv_congr` proves derivative dependence on the actual self/row
support using both `fderiv_dominance_apply` and `fderiv_amplitude_apply`.
`amplitude_fderiv_mask` justifies replacing the singular logs in surviving terms.
`maskedPartial_smooth` uses native `ContDiff.fderiv_right` and `clm_apply`.
Zero-index amplitudes are identified by equality of neighborhood germs in every
radial basis direction; adjacent amplitudes have zero germ. The actual torus
angular equation gives `B * angularComponents = angularRhs`, and determinant
one justifies the inverse. Equality extends to each nonzero-coordinate locus by
continuity and dense initial torus inside an **open** set.

For ε > 0, κ ≥ 2ε+1 and δ > 0, all finite indices have native `ContMDiffOn ∞`
coefficients agreeing with the imaginary logarithmic components wherever the
coordinate is nonzero in U. The δ > 0 statements are stronger than the requested
0 < δ < π regime. Smoothness itself does not require the ε or κ inequalities.
For mutable i in I, every q in U satisfies

```
D_Z a_i = (-κ + I * nu_i) * a_i
D_Z b   = (z*b-1) * nodeLogQuotient(z,b) - b * (-κ + I * nu_i)
```

where `z=q.a i` and `b=normalizedPartner q i`. The second identity is extended
from the torus using native smooth drift and the proved removable-log quotient.
At z=0, `nodeLogQuotient(0,b)=-b` yields the full complex Eq. (2.11):

```
D_Z b = (1+κ-I*nu_i)*b
```

This includes b=0 and simultaneous zeros. The proof neither divides a smooth
function by z at z=0 nor assumes angular divisibility or a smooth extension.
The curve results give literal complex `HasDerivWithinAt` statements along
`IsMIntegralCurveOn` of this same Z, on arbitrary time sets, requiring only
pointwise membership in U. No complete flow or invariant-neighborhood premise
is introduced.

## Consumers

The consumer exercises native smoothness and `HasMFDerivAt` of nu, explicit
`mfderiv` of normalized partners, and genuine complex curve equations. Its A2
family allows arbitrary complex partners, including zero. A two-block seed
checks simultaneous zeros and a punctured mixed-stratum family inside one fixed
U. A frozen coordinate varies over all nonzero complex values. Empty mutable
sets give zero angular coefficients; the dimension-zero carrier is inhabited
and supports the native constant-function complex differential.

The all-mutable A4 path has its full determinant and acyclicity proved. Its actual
exchange point has
`a=(0,-1,exp(x),exp(i*t))` and
`b=(w,-exp(x),(exp(i*t)-1)/exp(x),(1+exp(x))/exp(i*t))`.
The zero set is exactly {0}, the normalized partner at 0 is w, and the surviving
indices are {2,3}. At ε=1, κ=3, δ=π/2, x=-5 and t=π/8, the correction at vertex 2
is `-2*(π/8) ≠ 0`. The point belongs to the actual U centered at itself.
`a4_complex_consumer` applies native angular smoothness and the full complex
partner law at this nonvacuous configuration.

## Exact theorem inventory

Module namespace: `ClusterSkeleton.LocalAngularDynamics`.
The following 19 theorem declarations are the module inventory:

- `maskedLogs_smooth`
- `amplitude_fderiv_congr`
- `amplitude_fderiv_mask`
- `maskedPartial_smooth`
- `survivingAngular_smooth`
- `angularRhs_smooth`
- `nu_smooth`
- `amplitude_partial_zeroIndex`
- `angularRhs_eq_radial`
- `nu_eq_torus`
- `nu_eq_logarithmicComponents`
- `logarithmic_selected`
- `coordinate_drift`
- `partner_drift`
- `partner_drift_zero`
- `hasDerivWithinAt_complex_along_integralCurve`
- `coordinate_hasDerivWithinAt`
- `partner_hasDerivWithinAt`
- `partner_hasDerivWithinAt_zero`

Consumer namespace: `LocalAngularDynamicsConsumer`.
The following 33 theorem declarations are the consumer inventory:

- `generic_smooth`
- `generic_native`
- `coefficient_native_differentiable`
- `genuine_curve_local`
- `genuine_curve_zero`
- `center_partner`
- `boundary_coordinates`
- `pair_unimodular`
- `frozen_unimodular`
- `empty_unimodular`
- `a2_partner`
- `double_partners`
- `mixed_zero`
- `continuous_mixedPoint`
- `mixed_coordinates`
- `mixed_complex_family`
- `a2_arbitrary_partner`
- `a2_zero_partner`
- `simultaneous_zero_complex`
- `variable_frozen_complex`
- `empty_mutable_nu`
- `frozen_only_family`
- `dimension_zero`
- `a4_unimodular`
- `a4_zeroSet`
- `a4_partner`
- `a4_surviving`
- `a4_logs`
- `a4_character`
- `a4_dominance`
- `a4_correction_nonzero`
- `a4_nonvacuous`
- `a4_complex_consumer`

## Evidence and preserved scope

Input: artifact `a9bc6570-cac1-4380-b2c2-a8f9673cb355`, exact 282973 raw bytes,
SHA256 `31204bd4b0942fa17a531c27093a1f3e449af30f03090b211ba787cdc2c1f2ce`.
Accepted norm100 parent `bfe4cd2f9cfdeae2ffe411fa0db6483f97de5795`, tree
`fc33d1ff1b1b6734204934b5c3ff795dea11ad0c`. Publication is this parent plus exactly
this module, consumer and interface: angular103. All 100 accepted file modes,
Git blob IDs and SHA256 values were checked locally; unrelated extras remain.
No shared-root import, old proof, manuscript, upstream, ScalarOrbitDynamics,
or sibling ZeroStratumPartnerDynamics modification/import is part of this batch.

Managed checks use pinned Lean 4.34.1, Mathlib and FsFltz. The consumer contains
the accepted native `Lean.collectAxioms` selector with private/generated roots
and all nine explicit supplements. Separate generated composition contexts
preserve inherited consumer declarations. The source-bound delivery packet
records the module/consumer/composition receipts, full inherited 2710 plus every
fresh per-root native result, inherited/new lazy roots, exact-name overlap
equality, source/ordered-import/native-output/checker identities, verified private
publication, independent substantive review and actual native/durable terminal
collections. Only `propext`, `Classical.choice`, `Quot.sound` are allowed.
The optimized audit remains UNADOPTED. Compilation and audit receipts, review and
maintainer acceptance are separate evidence and are not implied by this document.

There are no open local mathematical targets in this module. Global all-strata
growth, two-sided complete flow, same-flow skeleton equality, final integration,
packaging, provenance recovery, and audit adoption remain with the root and its
scheduler successor. `GeometryTarget` and all original stage 3–6 requirements
remain unchanged and open until separately proved and accepted.
