# Constructed-flow reverse inclusion

This batch owns only `ClusterSkeleton/ConstructedFlowReverseInclusion.lean`,
`verification/ConstructedFlowReverseInclusionConsumer.lean`, and this interface.
Its base is accepted143 commit `05384a2bddbde6218bd0dec106947e99a527c455`, tree
`1ddfb475858d23d6f0de70798fc04177c5da1384`, acceptance artifact
`425e85b8-13f1-45e5-b16f-03a17adeec18`. All 143 paths, Git modes, blob IDs,
byte counts and SHA-256 hashes were independently verified in worker149's actual
allocation before editing. No accepted file required recovery. Existing extras,
including the separate forward-inclusion files, remain untouched and are excluded
from this publication. Historical physical/registered Git HEAD is not the accepted
source identity; no Git metadata was reset.

## Exact proposition and proof

`ClusterSkeleton.ConstructedFlowReverseInclusionTarget S hdet` is exactly

```lean
∀ {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ),
  trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow ⊆ coordinateCap S
```

The separate witness is `ClusterSkeleton.constructedFlowReverseInclusionTarget`.
The library theorem `ConstructedFlowReverseInclusion.trappedSet_subset_coordinateCap`
proves the inclusion directly. The only geometric assumptions are the original
`Seed` structure and its full integer determinant-one condition, together with the
displayed parameter inequalities. No flow, ODE, completeness, compactness, cap,
invariance, angular law or desired-conclusion premise is supplied.

The intermediate declarations in `ClusterSkeleton.ConstructedFlowReverseInclusion`
are `compact_forward_image`, `radial_and_frozen_restrictions`,
`initially_zero_partner`, `initially_nonzero_interior_partners`,
`interior_partner`, and `mutable_cap_product`.

The proof derives compactness of the nonnegative-time image from membership in
the independently defined trapped set. It restricts the same constructed flow's
native `isMIntegralCurve` to `Ioi (0 - 1)` for accepted compact interior rigidity.
This gives all original norm bounds and the unit norm of each nonzero variable
frozen coordinate. Nonzero strict-interior originals have both partners zero by
`CompactInteriorRigidity.initial_partners_zero`. Initially zero originals use
`ZeroStratumEscape.partner_eq_zero_of_mem_trappedSet`, with the same native ODE
restricted to `Ici 0`; that accepted theorem derives partner-growth escape on zero
strata. At unit original norm the cap factor is zero algebraically, without a
partner-zero restriction. These cases yield every mutable cap product.

The literal complex exchange carrier, inherited topology, native Mathlib/FsFltz
manifold/tangent/derivative/flow interfaces, full skew-symmetric integer matrix,
mutable-only acyclicity and independent cap/trapped definitions are unchanged.
No forward-inclusion theorem or branch is imported or required.

## Consumer contract and checking scope

The consumer is checked in an exact-source JOINT fixture after unchanged accepted143
consumer bodies. It uses the existing
`NativeFlowCapCompositionConsumer.liouvilleData` definition once, and proves its
flow is definitionally the actual `NativeCompleteFlow.completeFlow` flow.
Consumers cover arbitrary trapped points, the package's reverse inclusion,
initially zero originals, nonzero strict-interior originals, arbitrary complex
partners at unit boundary, frozen-unit consequences and the exact target witness.
Two accepted literal point families additionally test simultaneous zero/nonzero
originals with arbitrary input partner and independently variable frozen phases.
The family conclusions force `v = 0`, `z = -1`, and the appropriate frozen product
relation from actual trapped membership, without supplying these conclusions.

The earlier `NativeFlowRigidityCompositionConsumer` declarations remain JOINT-only
verification results. This batch does not import those scratch results as library
theorems. The new consumer likewise makes no standalone-compilation claim. Exact
fixture bytes, file-scope closures, cache resets, source keys and managed results
belong to the accompanying verification evidence; a checked fragment is not a
claim about a different standalone file.

Checks use pinned Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`. The evidence must preserve ALL 4614
accepted per-root maps, full inherited 4557/3836 and ancestor maps, nine
supplements, thirteen contexts/twelve comparisons, 826 equations/45 congruences,
and every fresh project/FsFltz/private/generated/consumer root. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. False order projections and all
failed/deferred/fixture/setup/synthetic-trace/source-key/archive qualifications
remain explicit. Native accepted143 counts 5276/36685/122355 and all historical
contexts remain distinct. The optimized audit is UNADOPTED; accepted native
collection and exact per-root comparison evidence remain authoritative.

## Boundary

The accompanying source-bound delivery records actual compiled declarations,
audit coverage, verified private publication, independent Astra/xhigh review,
bounded maintainer acceptance and collected actual terminal events. Those receipts,
not this interface text, establish verification and acceptance.

Root `df1a0cdf-af80-4485-9c04-b045ff0f3ffb`, through current145 then existing148,
retains sole shared-import, integration, recovery and final-packaging ownership.
This batch does not claim same-flow set equality, `LiouvilleSkeletonTarget`,
`FirstGeometricTarget`, current-provenance repair, optimized-audit adoption or
stage/phase/global acceptance. All original root and stage3–6 criteria, including
manifests `6a0e2320` and `26f582dc`, remain preserved. Root's separate accepted143
plus three forward-file composition proceeds independently.
