# Finite-time confinement interface

Mission 136 (`ca4efd84-2c62-4819-b702-e7b7ba24b215`) adds only this interface,
`ClusterSkeleton/FiniteTimeConfinement.lean`, and
`verification/FiniteTimeConfinementConsumer.lean` to accepted private123 commit
`b237b4d9587750907d89cbdbb4ec4be47c9b5b6f`, tree
`74534af4888e01ab6e383aaa517082b8c41cbab2`. All 123 accepted entries and the
three unrelated audit extras are preserved. The publication must contain 126
entries and use that exact parent; the mirror historical HEAD is not the input.

## Contract

`ClusterSkeleton.FiniteTimeConfinement.finite_time_compact_confinement`
uses literal `S.Point`, its inherited topology, `SmoothAtlas.charts S hdet`
and exactly `GlobalLiouvilleField.Z S hdet ε κ hδ`. `Seed` retains the full
integer skew matrix, mutable acyclicity, variable nonzero frozen coordinates,
and `hdet : S.Unimodular` retains determinant one. The sufficient parameter
conditions are `0 < ε`, `2*ε+1 ≤ κ`, and `0 < δ`, strengthening the requested
range by making no upper restriction on δ.

For each `p` and `T ≥ 0`, the theorem selects a compact `K` **before** every
`γ`, open preconnected `J`, and initial time `t₀`. Every native integral curve
of the same field on `J` with `t₀ ∈ J` and `γ t₀ = p` satisfies `γ t ∈ K`
for all `t ∈ J` with `|t-t₀| ≤ T`. No full closed horizon is required inside
`J`; both time directions and approach to omitted finite endpoints are covered.

`uniform_original_bounds` constructs a positive common lower bound for all
initially nonzero original coordinates, an upper bound for every original
coordinate, and an upper bound for every mutable original partner, with the
same quantifier order. Frozen variables receive both bounds.
`bounded_horizon_closure` puts the closure of the bounded-horizon image in the
same compact `K` and proves that closure compact. It does not assert compactness
of an unclosed image.

## Proof dependencies and geometric meaning

The proof fixes the initial zero mask using accepted native
`ZeroStratumInvariance.zeroSet_eq`. Only the fixed-mask logarithms are
differentiated, through `AllStrataGrowth.fixed_mask_hasDerivWithinAt` and the
open-domain promotion to an actual `HasDerivAt`. The individual radial defect
bound from `NativeRadialOrbit`, together with `PrimitiveCutoffs.radial_abs_le`,
gives `|A′| ≤ C |A|`. Native Mathlib Gronwall on the segment between two times,
and the actual derivative of the reversed time parameter, give a two-sided
exponential estimate. No regularity of a point-dependent mask is asserted.

Exponentiating the logarithmic bound gives positive lower/upper moduli.
Accepted `ZeroStratumPartnerDynamics.normSq_eq_exp_mul` controls normalized
partners at zero indices, including initial partner zero; a loose finite norm
bound avoids any nonzero-partner hypothesis. At a zero original index,
`ZeroStratumEscape.denominator_ne_zero` justifies
`b = normalizedPartner * negativeMonomial`. At a nonzero original index,
`b = (positiveMonomial + negativeMonomial) / a` follows from the exchange
equation and uses the derived positive lower bound. The normalized denominator
is never assumed nonzero there.

`CoordinateBounds.coordinateBox` bounds all original coordinates and partners
and puts a positive lower bound on frozen moduli. Its ambient image is exactly
the closed exchange-equation locus intersected with these closed bounds. It is
contained in a finite-dimensional closed ball and hence compact. The positive
frozen bound ensures every ambient limit remains an actual point. The subtype
embedding transfers compactness to the literal inherited topology. The proof
also handles empty mutable types and dimension zero.

This is a bounded consequence of the accepted all-strata growth interfaces
supporting the manuscript Theorem 2.1/Lemmas 2.2–2.5/Proposition 2.6 program.
It does not prove continuation, a complete flow, cap invariance, angular
rigidity, partner constraints for the cap, or equality with the dynamical
skeleton. Those remain with root `df1a0cdf-af80-4485-9c04-b045ff0f3ffb` and its
existing scheduler lineage. The independently defined cap is unchanged.

## Verification status

The module and complete source-matched consumer checks, exact compiled theorem
inventory, inherited/fresh per-root axiom reconciliation, source/native/checker
identities, independent review, and verified private publication are recorded
in the final mission receipts. Until those receipts are complete, this file is
an implementation interface, not a mission acceptance claim.

The consumer is a source-matched checking fragment. Its accepted fixture proof
ranges are assembled byte for byte from the accepted joint checker, with only
two inherited audit-only commands omitted and EOF scopes restored. It is not
claimed as a standalone Lake module. The new native collector keeps the accepted
selection and `Lean.collectAxioms` traversal; optimized audit adoption remains
UNADOPTED. All 3204 inherited maps, nine supplements, inherited 295 equation
and 41 congruence roots (including designated 287/41), thirteen original contexts
and twelve ordered projections are carried under exact identity checks. Fresh
private/generated/project/FsFltz/consumer roots and full-name overlaps require
explicit reconciliation. Only `propext`, `Classical.choice`, `Quot.sound` are
allowed. Accepted fixture-only corrections and failed/deferred history remain
part of the evidence chain.
