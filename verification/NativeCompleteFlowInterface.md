# Native complete Liouville flow

Mission 139 (`0385ecf0-f3bc-463b-b74b-8c1dc0dde130`) owns only
`ClusterSkeleton/NativeCompleteFlow.lean`, its consumer, and this interface.
The exact accepted parent is private126 commit
`8f481a8af5ff40f1b5ee77b140d575b9733fcf8a`, tree
`0df6605ce4c95e28813af08860ddac52828528e6`. Publication must preserve every
accepted path, mode, and blob and add only these three files, giving 129 entries.
The historical mirror HEAD is not the mathematical input. Unrelated audit
extras remain untouched; optimized audit adoption remains UNADOPTED.

## Mathematical interface

`NativeCompleteFlow.exists_global_integralCurve` constructs an all-real native
integral curve through every literal exchange point. Its field is exactly
`GlobalLiouvilleField.Z S hdet ε κ hδ`, its charts are
`SmoothAtlas.charts S hdet`, and its topology is the inherited subtype topology.
The hypotheses are `S.Unimodular`, `0 < ε`, `2*ε+1 ≤ κ`, and `0 < δ`.
No upper bound on δ is needed, so the original `δ < π` range is included.
The seed retains full integer skew-symmetry and determinant one, mutable-only
acyclicity, and independently variable nonzero frozen coordinates.

The existence proof considers symmetric lifetimes through the initial point.
If their supremum α were finite, accepted
`FiniteTimeConfinement.finite_time_compact_confinement` supplies a compact K
for horizon α, uniformly before any trial curve. The pinned
`CollarFlow.exists_compact_uniform_local_integralCurve` supplies a common
positive local lifetime on K. After shrinking it to η ≤ α, a trial curve
reaches both interior times ±(α−η/2). Both corresponding points are proved
to lie in K using confinement. Native interval uniqueness glues local curves
there, extending the trial curve beyond α in both directions, a contradiction.
Mathlib's native arbitrary-finite-interval assembly then gives an all-real
curve. This uses neither a uniform lifetime on the whole manifold nor endpoint
limits, a proper exhaustion, or an assumed complete flow.

`exists_completeLiouvilleFlow` chooses those proved solutions, derives the
addition law by native uniqueness, invokes the pinned joint smooth-dependence
theorem `CollarFlow.contMDiff_joint_of_isMIntegralCurve`, and constructs the
actual `FsFltz.Geometry.CompleteLiouvilleFlow`. Its native `Flow` has zero and
addition laws, its action is jointly `ContMDiff ∞`, and its chart equation is
obtained from `isMIntegralCurve_iff_chart_solves` for the same exact field.
`completeFlow` is a transparent noncomputable choice of that proved witness.

`exists_global_integralCurve_through` handles arbitrary initial time.
`exists_extension_Ioo` extends every native curve on `(a,b)` through any
interior `t₀`, agrees throughout `(a,b)`, and solves the native ODE at every
real time, including both omitted endpoints. It requires no endpoint values
of the old curve. Agreement follows from the pinned native interval uniqueness
theorem.

## Verification contract

The source-matched consumer checks the actual witness, native and chart ODE,
joint smoothness, zero/addition/inverse laws, arbitrary shifted times and both
time signs, genuine extension from `(5,9)` through 7 with derivatives at 5/9,
simultaneous zero coordinates and arbitrary partners including zero, a nonzero
coordinate with vanishing normalized denominator, variable frozen coordinates,
empty mutable types, dimension zero, and accepted finite-horizon confinement
on the produced global orbit on `univ`.

Accepted fixture ranges are reused verbatim in the combined private checker.
The consumer is a source-matched checking fragment, not claimed to be a
standalone Lake module. Exact theorem inventory and successful managed checks
must be reported in the final source-bound evidence. A drafted proof is not
reported as compiled before those checks.

Full verification carries all 3244 inherited per-root axiom maps, all nine
supplements, thirteen original contexts and twelve ordered projections,
298 equation and 41 congruence roots (including inherited 295/41 and designated
287/41). Every fresh project, FsFltz, private, generated, and consumer declaration
requires a per-root audit and exact full-name overlap equality. The source,
native outputs, checker, and dependency identities must be reconciled; inherited
5184 modules, 36188 physical identities and 121043 bindings include all original
121006 bindings. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Accepted fixture-only corrections and failed/deferred provenance are retained.

Final acceptance additionally requires independent substantive Astra/xhigh
review, verified exact-parent private publication, bounded maintainer acceptance,
and actual helper/maintainer execution and stop collection. The mission remains
open until all four criteria are fulfilled. This file itself is not an
acceptance receipt.

Root `df1a0cdf-af80-4485-9c04-b045ff0f3ffb` and its existing scheduler lineage
retain shared imports, integration, cap invariance, angular and partner
constraints, the full same-flow skeleton equality, and explicit audit adoption
and provenance. The coordinate cap and dynamical skeleton remain independently
defined. No sibling CapAngularTangency source is consumed.
