# Escape on an initially zero coordinate

This result proves the initially zero coordinate case of the necessary
condition in Proposition 2.6, using the accepted native zero invariance and
normalized squared-norm law associated with Lemma 2.5 and equation (2.11).
The carrier is the literal complex exchange-equation subtype with its inherited
topology. The atlas is SmoothAtlas.presentation (its native charts instance).
The full integer matrix is skew-symmetric with determinant one; only the mutable
quiver is acyclic. Frozen coordinates remain nonzero variables.

For ε > 0, κ ≥ 2ε + 1, δ > 0, and any genuine native IsMIntegralCurveOn γ of
exactly GlobalLiouvilleField.Z on Ici t₀, if the original a_i(γ t₀) = 0 and
the original b_i(γ t₀) ≠ 0, eventually_not_mem_compact proves:

    ∀ compact K ⊆ S.Point, ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K.

The δ > 0 scope includes the manuscript range 0 < δ < π; positivity alone
is not asserted to imply δ < π. The forward image has noncompact closure.
Equivalently, compact forward closure and an initially zero original coordinate
force the original partner to vanish. No converse compactness claim is made.

The zero locus Z_i is closed by continuity of the original coordinate. At each
point p of Z_i, its own independent zeroSet and mem_zero_locus imply the negative
exchange monomial is nonzero and normalizedPartner is continuous at p.
Consequently its squared norm is bounded on K ∩ Z_i. This accommodates compact
limit points where additional coordinates vanish; no fixed chart or initial
full-stratum closure assertion is used.

Native coordinate_zero_iff places every forward point in Z_i. The accepted
normSq_eq_exp_mul gives exp(c(t-t₀))A with c = 2(1+κ) > 0 and A > 0; nonzero
original b_i implies A > 0 using the proved nonzero denominator. If M is the
compact-slice upper bound, the proof uses

    T = max t₀ (t₀ + (M/A + 1)/c)

and Real.add_one_le_exp to contradict that bound for every t ≥ T.
It asserts neither global quotient continuity nor unbounded original b_i.

The flow corollaries use the existing independently defined trappedSet of a
supplied native Flow ℝ S.Point. Their explicit orbit hypothesis is the native
IsMIntegralCurveOn of exactly Z on Ici 0 through the considered point.
Flow.forwardOrbit_eq_range_nonneg identifies that orbit with the curve image.
This is a conditional application, not a construction or acceptance of a complete
flow, cap invariance, a skeleton inclusion, or skeleton equality.

## Theorem inventory

ClusterSkeleton.ZeroStratumEscape (10):
isClosed_zero_coordinate, denominator_ne_zero, continuousAt_normalizedPartner,
normalizedPartner_eq_zero_iff, compact_zero_slice_bound,
eventually_not_mem_compact, not_isCompact_closure_forward_image,
partner_eq_zero_of_isCompact_closure, partner_eq_zero_of_mem_trappedSet,
not_mem_trappedSet.

ZeroStratumEscapeConsumer (21):
boundary_coordinates, pair_unimodular, frozen_unimodular, empty_unimodular,
a2_partner, double_partners, reversed_coordinates, a2_nonzero_partner_escape,
a2_compact_closure_forces_zero, a2_zero_partner_persists, reversed_a2_escape,
simultaneous_zero_and_escape, variable_frozen_escape,
shifted_halfline_endpoint, time_translation_escape,
supplied_flow_necessary_and_excluded, a2_supplied_flow,
empty_mutable_scope, frozen_only_family, dimension_zero_native_curve,
dimension_zero_compact_forward.

The eight actual fixture definitions are boundaryPoint, reversedBoundary,
pairSeed, frozenSeed, frozenPoint, emptySeed, doubleBoundary and
variableFrozenBoundary. Their seed and exchange hypotheses are proved.
Reversed A₂ explicitly has denominator -1 and normalized partner -w.
The simultaneous-zero fixture has one zero original partner and a second
arbitrary nonzero partner. The frozen fixture has an independently arbitrary
nonzero complex coordinate. Closed-endpoint derivatives and actual native time
translation are exercised. Dimension zero has a proved constant native curve
with compact forward closure and no mutable index. Nonzero-dimensional native
curves and flows are honest supplied hypotheses, not existence claims.

## Verification and ownership

Accepted input: private commit 1224eed928dc08f66193c7f5bb06c80cdfd4c920,
tree 4b7d7b8d07368f88dc319a792fba8d47775c7604, 106 entries.
The source-bound packet is artifact 98c097ba-bac2-4da4-9768-bb4fb2b86bb8,
SHA256 0107adca72fdefb912d837cc050b7481f69fe9e54347c5032a634f714e2c658a,
603249 bytes, full raw verified. The actual allocated source was compared with
every accepted path/mode/blob/SHA; only six missing accepted files were recovered
through the exact private source API. Six unrelated allocated extras were
preserved, excluded from imports and publication.

Publication must preserve all 106 accepted entries and add only this interface,
ClusterSkeleton/ZeroStratumEscape.lean and
verification/ZeroStratumEscapeConsumer.lean: 109 entries total. Physical recovery
HEAD is not the accepted baseline. LocalAngularDynamics and ScalarOrbitDynamics
are not inputs. Shared root imports and old proof sources are unchanged.

The source-bound delivery records the actual successful targeted managed module,
consumer and composition checks under Lean 4.34.1, Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612 and FsFltz
1a3d387cfacc746e25aad31e5b27b1803103e7cb. It records every inherited 2844-root
native transitive axiom map and fresh project/FsFltz/private/generated/consumer
map, exact full-name overlap equality, all nine supplements, all 255 inherited
and fresh lazy equations, ordered imports and source/native-output/checker
identities. Only propext, Classical.choice and Quot.sound are allowed.
The optimized audit remains UNADOPTED. A failed elaboration is not a compiled
theorem; exact passing inventories and receipts belong to the delivery evidence.

Verified private publication, independent Astra/xhigh mathematical/manuscript/
native review, actual native terminal collection, bounded maintainer acceptance,
and actual durable terminal execution/stop collection are separate required
evidence. This document alone claims none of those lifecycle outcomes.

Root df1a0cdf-af80-4485-9c04-b045ff0f3ffb through planner102 and existing
successor107 04411b12-a924-488d-b581-6b4db8794d3f retains shared integration,
all-strata growth, two-sided complete native flow, full same-flow skeleton,
audit adoption/provenance recovery, and every original root/stage3–6 obligation.
No mission correction, criterion removal, or replacement target is introduced.
