# Strict-interior nonzero partner propagation

`ClusterSkeleton.interiorPartnerPropagationTarget` inhabits the separately
defined `ClusterSkeleton.InteriorPartnerPropagationTarget`. The carrier is the
literal `S.Point` exchange subtype with inherited topology and the constructed
`SmoothAtlas.presentation`. The curve solves the exact `GlobalLiouvilleField.Z`.

The parameters are full integral skew-symmetric determinant-one `S`, mutable-only
acyclicity, `ε > 0`, `κ ≥ 2ε+1`, `δ > 0`, and `η > 0`. For any genuine native
integral curve on `Ioi (t₀-η)`, one initial membership `γ t₀ ∈ coordinateCap S`
and a mutable `i` with `(γ t₀).a i ≠ 0` and `‖(γ t₀).a i‖ < 1` imply, for every
`t ≥ 0`, character `-1`, normalized partner `0`, and actual mutation partner `0`
at `γ (t₀+t)`. Other original coordinates can vanish simultaneously. Frozen
coordinates remain nonzero variables.

The source is `acyclic_cluster_HMS.pdf` (2026-10-20), Proposition 2.6, page 12:
its exact angular equation, finite-interval uniqueness argument, and converse
cap-invariance paragraph. This delivery proves the specified propagation
ingredient; full cap invariance and the full skeleton remain with root.

## Proof and route refinement

1. Accepted strict-cap independence derives every full-row neighbor's initial
   unit norm. The accepted native zero-log law propagates those norms. No later
   cap membership is supplied.
2. Native Laurent-character differentiation treats each zero-exponent factor as
   a constant before differentiating. Only row-support coordinates must be
   nonzero, so unrelated zero coordinates are permitted.
3. The full angular matrix equation reduces to the selected summand:
   nonadjacent partials vanish, and adjacent amplitudes and their derivatives
   vanish at unit coordinates. The coefficient is the actual amplitude
   derivative evaluated at `Pi.single i (A p i)`.
4. Its continuity uses only the selected logarithmic radius, whose nonvanishing
   follows from the accepted zero-stratum theorem. There is no assertion of
   global smoothness of a moving zero mask. Native chain rules give
   `q' = I * q * c * vartheta δ (arg (-q))`, including the initial endpoint.
5. The actual cutoff satisfies the global estimate
   `‖q‖ * |vartheta δ (arg (-q))| ≤ (π/2) * ‖q+1‖`, by Jordan's sine inequality
   and the polar sine identity. The coefficient is bounded on each finite
   interval. Native Grönwall gives `q = -1` including both endpoints. This
   replaces the suggested local argument/continuation route without changing
   the target or adding a hypothesis.
6. Row-support nonvanishing gives a nonzero negative monomial. The literal
   exchange equation and selected original nonvanishing give the actual
   partner zero and hence the normalized partner zero.

The shallow collar is retained: neither deep radius nor a cutoff-one premise
appears. The module imports no `NativeCompleteFlow`.

## Checked theorem inventory

The exact authored theorem list follows. Generated declarations are additionally
included in the per-root native audit.

21 core proofs, with namespace `ClusterSkeleton.InteriorPartnerPropagation`
except the final `ClusterSkeleton.interiorPartnerPropagationTarget`:

- `initial_neighbor_unit`
- `unit_norm_forward`
- `neighbors_unit_forward`
- `negativeMonomial_ne_zero`
- `partners_zero_of_character`
- `hasFDerivAt_character_row`
- `mdifferentiableAt_character_row`
- `differential_character_row`
- `angularRhs_eq_self_of_unit_neighbors`
- `differential_character_of_unit_neighbors`
- `abs_arcsin_sin_le`
- `abs_vartheta_le_sin`
- `norm_mul_vartheta_arg_le`
- `angular_scalar_eq_neg_one_of_bounded`
- `angular_scalar_eq_neg_one`
- `angular_scalar_eq_neg_one_of_hasDerivAt`
- `characterCoefficient_continuous`
- `shifted_character_hasDerivAt`
- `character_eq_neg_one_forward`
- `propagate`
- `interiorPartnerPropagationTarget`

15 consumer proofs in `InteriorPartnerPropagationConsumer`:

- `interiorPoint_mem`
- `pair_unimodular`
- `simultaneousPoint_mem`
- `all_neighbors_from_initial_cap`
- `selected_with_other_zero`
- `shifted_initial_endpoint`
- `literal_carrier`
- `shallow_collar`
- `a2_family_forward`
- `simultaneous_family_forward`
- `phase_unimodular`
- `phasePoint_mem`
- `independent_frozen_phases_forward`
- `shallow_family_initial`
- `exact_target`

The consumers cover the selected nonzero disk coordinate with a simultaneous
other zero original, shifted time and `t=0`, a full row with three frozen columns
and two independently variable unit phases, the inhabited shallow family
`a₀ = exp(-ε)`, an A₂ family with a nonzero boundary partner, and derivation of
every neighbor premise from one initial cap membership.

## Source and verification boundary

The exact accepted base is cap129 commit
`a37247b5d4c42c47d26e3c0d83d7b78c80eb0b0b`, tree
`87758bb67425a04119d2c9120b6db892f752c70a`. The publication contains only this
interface, the new core, and the new consumer in addition to those 129 entries.
Every accepted path/mode/blob/SHA and all six unrelated actual extras are
preserved. No shared-root/import, old-proof, PDF, upstream, or audit-adoption
edit belongs to this delivery.

Managed checks use Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`. The delivery evidence records exact
module/consumer receipts, final source/native/checker identities, actual ordered
import closure, every fresh declaration's transitive native axiom map, full-name
overlap equality, private publication, independent substantive review, and the
bounded maintainer decision and actual terminal collection.

All 3659 accepted per-root maps, including original 3244, remain in their own
exact contexts, with nine supplements, thirteen original contexts/twelve order
comparisons, cap 650 equations/41 congruences, inherited 298/41 and 295/41, and
designated 287/41. Historical native 5184 modules/36188 physical identities/
121043 bindings (including 121006) and cap-current 5181/36095/84833 are retained
separately from the fresh closure. Different contexts are not asserted equal.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The optimized
audit remains **UNADOPTED**. Failed, deferred, and generated-fixture provenance
is retained; only successful source-matched receipts establish compilation.

## Outstanding root work

Root retains full cap forward invariance, remaining trapped-orbit angular
rigidity/partner constraints, both full skeleton inclusions for the same actual
flow, complete-flow composition, explicit audit adoption/current provenance,
and every original root/stage3–6 criterion and manifest. This lane does not
accept the formalization phase or global objective.
