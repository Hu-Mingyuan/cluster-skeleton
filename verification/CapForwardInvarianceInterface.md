# Coordinate cap forward invariance

This lane proves `ClusterSkeleton.CoordinateCapForwardInvarianceTarget` with the
literal meaning of input artifact `b7781f1c-ed7a-49b9-bdbe-f37ac92f1d8e` (138348
bytes, SHA256 `3c755c2bbd537e235a13052b28c88ade18ebb9a8cb9a39d39dac27d995fcdf7a`).
The proposition and proof remain distinct declarations.

The base is accepted partner132 commit
`7767619011f6982227a168722ba0f7e3b6e8fb4e`, tree
`e7d1ede809f0d1f8778236419c413724a77f9c61`, with cap129 parent
`a37247b5d4c42c47d26e3c0d83d7b78c80eb0b0b`. Publication adds only this interface,
`ClusterSkeleton/CapForwardInvariance.lean`, and
`verification/CapForwardInvarianceConsumer.lean`: 135 entries. All 132 accepted
path/mode/blob/SHA identities and the allocated workspace's unrelated extras
are preserved. Neither the proof nor consumer imports `NativeCompleteFlow` or
root134/root137 composition.

## Mathematical contract

For any `Seed d` and proof `S.Unimodular`, use literal `S.Point` with its inherited
topology and `SmoothAtlas.charts S hdet`. The full integer matrix is skew and has
determinant one; only mutable arrows are acyclic. Frozen coordinates are nonzero
variables. For `ε > 0`, `κ ≥ 2*ε+1`, `δ > 0`, `η > 0`, let `γ : ℝ → S.Point` be
any genuine native integral curve of `GlobalLiouvilleField.Z S hdet ε κ hδ` on
`Ioi (t₀-η)`. One assumption `γ t₀ ∈ coordinateCap S` implies
`γ (t₀+t) ∈ coordinateCap S` for every `t ≥ 0`, including `t = 0` and arbitrary
shift `t₀`. There is no whole-curve cap or chart assumption, angular-equilibrium
premise, supplied propagation theorem, or cutoff/deep-radius assumption.

The proof splits on initial data. For an initially zero mutable original,
`coordinate_zero_iff` and `partner_zero_iff` propagate original and normalized
partner zero. `normalizedPartner_eq_zero_iff`, using the actual zero-locus
exchange denominator, recovers actual partner zero. For a nonzero strict
interior original, `coordinate_ne_zero` and `negative_log_laws` preserve positive
norm below one, and accepted `InteriorPartnerPropagation.propagate` supplies
actual partner zero. Mutable unit originals and all frozen originals use the
accepted native `unit_norm_forward`. Unit-boundary partners are unrestricted.
The two mutable alternatives then establish the actual product
`((1 - ‖aᵢ‖^2 : ℝ) : ℂ) * bᵢ = 0`.

## Declarations and consumers

The six source theorems are:

- `ClusterSkeleton.CapForwardInvariance.zero_forward`
- `ClusterSkeleton.CapForwardInvariance.interior_forward`
- `ClusterSkeleton.CapForwardInvariance.mutable_constraints_forward`
- `ClusterSkeleton.CapForwardInvariance.frozen_norm_forward`
- `ClusterSkeleton.CapForwardInvariance.forward`
- `ClusterSkeleton.coordinateCapForwardInvarianceTarget`

The consumer namespace is `CapForwardInvarianceConsumer`. Its theorem inventory is
`interiorPoint_mem`, `pair_unimodular`, `simultaneousPoint_mem`, `phase_unimodular`,
`phasePoint_mem`, `shallow_family_initial`, `full_cap_from_one_initial`,
`shifted_initial_endpoint`, `all_initial_zeros`, `nonzero_interior`,
`mutable_unit_boundary`, `frozen_unit`, `literal_carrier`, `a2_family_full_cap`,
`simultaneous_zeros_full_cap`, `independent_frozen_phases_full_cap`,
`shallow_collar_full_cap`, and `exact_target`.

Fixtures reproduce the accepted partner consumer's literal exchange points in a
new namespace. They include two simultaneous zero originals, the A₂ disk with a
unit mutable original having a nonzero partner, two independent variable frozen
phases, and the concrete shallow radius `exp (-ε)` with zero initial radial
cutoff. Consumers assert the full cap, along with relevant coordinate equations.
They assume the genuine curve, not its existence; this lane does not construct a
flow.

## Validation and retained provenance

Use targeted managed Lean checks of the new module and consumer with Lean 4.34.1,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`. Exact checked source, pass/fail status,
native output identities, and full per-declaration maps are recorded in the
source-bound delivery evidence. Compilation and source fidelity are separately
reviewed. A theorem is reported as compiled only under its passing receipt.

The consumer retains the accepted native per-root audit traversal, realizes
available equation theorems, selects every defining project/FsFltz declaration,
all private/generated/local consumer roots, and the nine required supplements.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Reconciliation
retains all 3732 accepted partner maps (including 3659 cap and original 3244),
compares every full-name overlap for exact axiom-set equality, and records all
fresh roots. All 13 original contexts/12 orders and equation/congruence contexts
remain separate: partner 657/41, cap 650/41, inherited 298/41 and 295/41, and
designated 287/41. Native contexts likewise remain separate: original
5182/36167/121006, inherited 5184/36188/121043, cap 5181/36095/84833, and partner
5190/36156/84948. Actual new import order and native/source/checker identities
must be measured, not copied from those historical contexts. Preserve inherited
failed/deferred/fixture provenance and complete archives. The optimized audit
remains UNADOPTED.

Root mission `df1a0cdf-af80-4485-9c04-b045ff0f3ffb`, through the existing root
integration owner and scheduler successor, retains shared imports and final
packaging. Same-flow specialization, compact-cap trapped inclusion, reverse
angular rigidity and partner constraints, both skeleton inclusions, audit
adoption, current provenance, and stage reconciliation are root-owned remaining
obligations. This lane does not claim the full skeleton theorem or phase/global
acceptance. No criterion is removed or weakened.
