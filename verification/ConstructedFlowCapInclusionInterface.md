# Constructed-flow cap inclusion

This batch specializes the accepted cap invariance theorem to
`NativeCompleteFlow.completeFlow S hdet hε hκ hδ`. Its exact input is accepted140,
commit `910e182d57fec92d3347d1ebda381cce373a5f6a`, tree
`b965fc5bd4d3f9388e5c37756655dcab0101100c`. The only new source files are the
ConstructedFlowCapInclusion module, consumer and this interface. No shared
imports or accepted proofs change; CompactInteriorRigidity is not a dependency.

`ClusterSkeleton.ConstructedFlowCapInclusionTarget` is the separate proposition
from the mission input. It quantifies over arbitrary dimension, seed,
unimodularity and parameters `0 < ε`, `2 * ε + 1 ≤ κ`, `0 < δ`, and asserts
`coordinateCap S ⊆ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow`.
Its witness is `ClusterSkeleton.constructedFlowCapInclusionTarget`.

The native all-real orbit is restricted to `Ioi (0 - 1)`.
`CapForwardInvariance.forward` applies with `t₀ = 0`, `η = 1` and one initial
cap point. The flow law at zero supplies that initial condition.
`isCompact_coordinateCap` and
`subset_trappedSet_of_isCompact_forwardInvariant` then give the inclusion.
There is no supplied complete flow, curve, invariance or whole-orbit cap premise.
The exact complex exchange carrier, inherited topology, native atlas, vector
field, full skew integer determinant-one matrix, mutable-only acyclicity and
nonconstant nonzero frozen variables are inherited unchanged.

The module declares these six theorems:

- `ClusterSkeleton.ConstructedFlowCapInclusion.integralCurveOn`
- `ClusterSkeleton.ConstructedFlowCapInclusion.forward`
- `ClusterSkeleton.ConstructedFlowCapInclusion.isForwardInvariant`
- `ClusterSkeleton.ConstructedFlowCapInclusion.subset_trappedSet`
- `ClusterSkeleton.ConstructedFlowCapInclusion.isCompact_forwardOrbit_closure`
- `ClusterSkeleton.constructedFlowCapInclusionTarget`

The consumer declares these fifteen theorems in namespace
`ConstructedFlowCapInclusionConsumer`:

- `actual_native_orbit`
- `one_initial_cap`
- `all_initial_zeros`
- `nonzero_interior`
- `mutable_unit_boundary`
- `frozen_unit`
- `compact_forward_closure`
- `liouvilleData_cap_inclusion`
- `liouvilleData_compact_forward_closure`
- `shifted_initial_cap`
- `a2_disk_trapped`
- `simultaneous_zero_trapped`
- `independent_frozen_phases_trapped`
- `shallow_collar_trapped`
- `exact_target`

All consumer curves are actual constructed orbits. The arbitrary-seed tests
retain simultaneous zeros, nonzero interior coordinates, unconstrained partners
on the mutable unit boundary and arbitrary frozen phases. Literal accepted A2,
simultaneous-zero and independent-frozen-phase families instantiate the inclusion;
the shallow-collar family has radius `exp (-ε)`. The two LiouvilleData consumers
use the exact existing `NativeFlowCapCompositionConsumer.liouvilleData` package,
whose complete flow is definitionally the same construction.

The consumer is a source-matched fragment, checked in a frozen integrated scratch
fixture. That fixture supplies the unchanged accepted
`NativeFlowCapCompositionConsumer` and `CapForwardInvarianceConsumer` bodies,
with their accepted file-scope adapters, before this consumer's exact body.
This avoids pretending the verification directory is a Lake library. The fixture
records source hashes, import order, scope adapters and generated declaration
attribution. The existing NativeCompleteFlowConsumer checked-fragment caveat
remains intact. The module and integrated consumer receive managed checks using
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`; exact receipts accompany delivery.

The full integrated audit uses the accepted exhaustive native collector, includes
every fresh project/FsFltz/private/generated/consumer declaration and preserves
all 4557 accepted per-root maps and their historical contexts, comparisons,
supplements, identity records, archives and failed/deferred/setup/fixture
provenance. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
The optimized audit remains unadopted. Exact current counts and source/native
identities belong to the source-bound audit evidence, not a predicted count here.

No proposition introduced by this batch remains without a witness. The reverse
inclusion, final literal skeleton equality, shared integration, provenance,
explicit audit-adoption decision and phase acceptance remain root-owned.
Compilation and mathematical acceptance are separate recorded decisions.
