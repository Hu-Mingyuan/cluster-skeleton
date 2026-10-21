# Private joint dynamics consumer

This is a consistency and consumer composition of two separately accepted source
closures. Its inherited source is exactly angular103
`9e321dcf2031237c27c944e101f9900c4bd2b14c` /
`e1ac772888d066b81bf1832aaa6299254bbdd313` and escape109
`467f1561f713b91d7fffc47f02f6343108e8f24b` /
`bb0cb27f4b1984fa9cc3f72160ed981b19025c86`.
Their 100 common source entries agree; their union has 112 entries. The private
publication parent is the exact escape109 commit, with the three unchanged
angular additions and only `DynamicsCompositionConsumer.lean` and this document
added: 114 entries. Shared root imports and old proofs are unchanged.

## Mathematical contract

The generic dynamics statements use `S : Seed d`, whose full integer matrix is
skew-symmetric and whose mutable relation alone is acyclic, and the separate
`hdet : S.Unimodular` asserting determinant one of that full matrix.
`S.Point` is literally the subtype of complex original/partner coordinates
satisfying the exchange equations and nonzero frozen-coordinate conditions.
Its topology is the inherited subtype topology. `literal_carrier_and_frozen`
checks the continuous actual inclusion and the actual equations/nonvanishing.
There is no replacement carrier, topology, derivative, atlas, or vector field.

`native_zero_dynamics` starts with one genuine native `IsMIntegralCurveOn` of
`GlobalLiouvilleField.Z S hdet ε κ hδ` under `SmoothAtlas.charts S hdet` on
`Ici t₀`, with `ε > 0`, `κ ≥ 2*ε+1`, `0 < δ < π`, and one initially zero
original mutable coordinate. Its conclusion `ZeroCurveLaws` is proved, never
supplied as a premise. For every `t ≥ t₀` it gives:

- zero persistence from accepted `ZeroStratumInvariance.coordinate_zero_iff`;
- nonvanishing of the actual negative exchange monomial from accepted
  `ZeroStratumEscape.denominator_ne_zero` at the current point;
- equivalence of vanishing of the current and original **original** partners,
  obtained by the accepted normalized-partner zero equivalences;
- the exact squared-norm law
  `normSq b̃(t) = exp (2*(1+κ)*(t-t₀)) * normSq b̃(t₀)` and its native relative
  within-derivative, from accepted `ZeroStratumPartnerDynamics`;
- the accepted complex within-derivative
  `b̃' = (1+κ-I*ν)*b̃` for each selected center `p` satisfying `i ∈ p.zeroSet`
  and **pointwise** `γ t ∈ LocalPrimitive.neighborhood S ε κ δ p`.

No whole-curve or closure membership in one chart is a hypothesis. In
particular, the local coefficient may use a different center at different
times. `native_complex_differential` also writes the actual `mfderiv` evaluated
at precisely the same `Z`. The accepted drift definition uses the manifold of
`SmoothAtlas.presentation S hdet`; its chart is definitionally the chart in
the supplied curve.

`native_zero_escape` requires the nonzero **original** initial partner, derives
all preceding facts, and combines them with accepted eventual avoidance of every
compact subset of the actual carrier and noncompactness of the forward-image
closure. `original_partner_zero_persistence` covers the complementary zero
original-partner case. Neither theorem assumes a global continuous quotient or
growth of the raw partner. The inherited escape proof obtains quotient bounds
on compact zero slices using each point's own zero set.

`supplied_flow_joint_exclusion` uses the existing native `Flow ℝ S.Point` and
existing independently defined `trappedSet flow`. Its explicit orbit premise is
an `IsMIntegralCurveOn` for exactly `Z` on `Ici 0`. It constructs no flow and
asserts no completeness. `shifted_closed_endpoint` retains the actual relative
complex derivative at the included endpoint `s+τ` and the entire future law.

## Source-matched example contexts

The two accepted verification consumer files are checking files rather than
Lake library modules. To reuse their proved fixtures without editing the Lake
configuration or authoring duplicate examples, the generated joint checker
uses the union of their imports followed by their byte-identical declaration
bodies, including their original native audit commands, and the byte-identical
fresh consumer body. The checker manifest binds every input slice and the
whole generated checker. Thus the fixture-specific declarations in the fresh
file are compiled in that explicit context, not advertised as a standalone
Lake target. Ordered inherited import projections and native module/output
identities are checked separately.

The actual A₂ boundary family has arbitrary complex original partner `w`:
`a2_joint` proves the same joint laws for all `w`, zero-partner persistence for
`w=0`, and compact escape for `w≠0`. `simultaneous_joint` uses the accepted
four-coordinate seed with two simultaneously zero original coordinates,
one zero original partner, and a nonzero other partner. Both coordinates
satisfy the joint laws on the same curve. `variable_frozen_joint` leaves the
accepted frozen coordinate `z` independently arbitrary and nonzero, retains its
nonvanishing at every curve value, and combines the joint laws with escape.

`empty_mutable_joint` proves there is no mutable index and that the angular
coefficient is zero. `dimension_zero_joint` uses the accepted genuinely
constructed constant native curve and compact forward closure in dimension
zero; no mutable escape hypothesis exists there.

`a4_nonzero_correction_joint` reuses the accepted A₄ seed, boundary point
`p = a4Boundary w (-5) (π/8)`, determinant proof and `a4_nonvacuous` fixture.
At `ε=1`, `κ=3`, `δ=π/2`, its surviving correction at index 2 is proved nonzero.
For a supplied genuine exact-Z curve starting at that actual point, with
`w≠0`, the consumer simultaneously proves the joint laws, the complex relative
endpoint derivative and eventual avoidance of every compact set. It does not
assume a zero angular correction or solve a new A₄ ODE.

## Exact fresh theorem inventory

The fresh consumer contains exactly these 13 theorem declarations, all in
namespace `DynamicsCompositionConsumer`:

1. `native_zero_dynamics`
2. `native_complex_differential`
3. `native_zero_escape`
4. `original_partner_zero_persistence`
5. `supplied_flow_joint_exclusion`
6. `shifted_closed_endpoint`
7. `literal_carrier_and_frozen`
8. `a2_joint`
9. `simultaneous_joint`
10. `variable_frozen_joint`
11. `empty_mutable_joint`
12. `dimension_zero_joint`
13. `a4_nonzero_correction_joint`

`ZeroCurveLaws` is the sole fresh proposition definition;
`native_zero_dynamics` proves it under the stated hypotheses. Exact compilation status and source-bound
receipts are recorded in the private delivery packet, not inferred from this
inventory. No declaration here proves all-strata growth, existence of a complete
two-sided flow, cap invariance, or skeleton equality.

## Trust and ownership

The acceptance evidence must reconcile all 3033 inherited per-root native
transitive axiom maps (2910 escape, 2833 angular, 2710 exactly equal overlaps),
every fresh project/FsFltz/private/generated/consumer declaration, all nine
supplements, and the union of every inherited and fresh lazy equation. A source
union or a global axiom union is insufficient. The unchanged native
`Lean.collectAxioms` checker remains authoritative; the optimized audit is
UNADOPTED. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The delivery binds managed Lean 4.34.1 checks, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, FsFltz
`1a3d387cfacc746e25aad31e5b27b1803103e7cb`, all source/import/output/checker
identities and preserved inherited consumer coverage.

The root mission `df1a0cdf-af80-4485-9c04-b045ff0f3ffb`, through planner109
and existing scheduler successor111 `60571325-34e7-452e-a02c-34d8981017f2`,
retains sole shared-root import, final integration and packaging ownership and
all original root/stage3–6 obligations, including all-strata growth, complete
two-sided native flow, the full same-flow skeleton, provenance reconciliation,
audit adoption, and prior manifests `6a0e2320` / `26f582dc`. This bounded
composition does not accept those outcomes or block independent mathematics.
