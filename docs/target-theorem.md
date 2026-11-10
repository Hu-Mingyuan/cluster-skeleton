> Scope: this guide records the **weighted (skew-symmetrizable)** library at
> accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`. The
> superseded `D = I` baseline is kept only in the explicit
> baseline-versus-weighted comparisons of
> [`skeleton-audit.md`](skeleton-audit.md) and in its recovery section §1.11. The
> accepted-source manifest, the verifier run and the receipts for this source
> exist; see *Verification status* below.

# Definitions, formulation, and the proved target

The full mathematical statement is in [target-theorem.pdf](../target-theorem.pdf),
with editable source in [`tex/target-theorem.tex`](tex/target-theorem.tex). The
weighted geometric argument is [proof-blueprint.pdf](../proof-blueprint.pdf)
(source [`tex/proof-blueprint.tex`](tex/proof-blueprint.tex)); its step-to-module
map is [`proof-blueprint.md`](proof-blueprint.md) and the convention-by-convention
comparison is [`skeleton-audit.md`](skeleton-audit.md).

## Input and definitions

The input is the reference input of `tex/target-theorem.tex` §1, with **no**
specialization:

* an integral `d × d` exchange matrix `E`, **not** assumed skew-symmetric;
* a diagonal symmetrizer `D = diag(d_1,…,d_d)` with **arbitrary positive
  rational** entries;
* skew-symmetrizability `E_{ij} d_j = -(E_{ji} d_i)`, i.e. `K = E D̃` is
  skew-symmetric, where `K_{ij} = E_{ij} d_j`;
* a mutable set `M` whose block `E_{M,M}` is acyclic (no acyclicity on the full
  index set);
* unimodularity `det E = 1`, quantified as a separate hypothesis.

Frozen coordinates are variable nonzero complex numbers; no principal-coefficient
assumption is made. The exchange monomials use the reference's **column**
exponents, `P_i^± = ∏_j z_j^{[±E_{ji}]_+}`, so the space is literally the
reference's

```
X_E = {(z,z') ∈ ℂ^d × ℂ^M : z_i z_i' = P_i^+(z) + P_i^-(z) (i ∈ M), z_f ≠ 0 (f ∈ F)}
```

as the actual subtype of pairs `(a,b)` with the inherited topology.

| Declaration | Role |
| --- | --- |
| `Seed` | Input data: fields `E`, `mutable`, `D`, `D_pos`, `skewSymmetrizable`, `acyclic` |
| `Seed.K`, `Seed.K_transpose` | The weighted form matrix `K i j = (E i j : ℚ) * D j` and its skew-symmetry |
| `Seed.B` (`= Seed.Bexp = S.Eᵀ`) | The **exponent** matrix: `S.B i j = S.E j i` is the column exponent, by `rfl` (`Seed.B_apply`). It carries no skew-symmetry |
| `Seed.Unimodular` | `S.E.det = 1`; see the equality with the reference's `E ∈ GL_d(ℤ)` below |
| `Seed.Point` | Actual exchange-equation carrier with the column monomials |
| `coordinateCap` | Frozen norms equal one; mutable norms at most one and `(1 - ‖a_i‖²)b_i = 0` |
| `lambdaStratum S I` | The reference stratum `Λ_I`: `b_i = 0` and `‖a_i‖ ≤ 1` for mutable `i ∈ I`, `‖a_j‖ = 1` for `j ∉ I` |
| `Seed.Independent` | `I ⊆ S.mutable` and `S.E i j = 0` for all `i,j ∈ I` |
| `trappedSet` | Points with relatively compact forward orbit under a given native flow |
| `SmoothPresentation`, `LiouvilleData` | Interfaces specifying required witnesses and properties |
| `SmoothPresentation.logarithmicImaginaryValue` | `Im(½ Σ_{i,j} K_ij dlog a_i ∧ dlog a_j)`, the coefficient being the **rational** `K`, not `E` |
| `LiouvilleSkeletonTarget`, `FirstGeometricTarget` | Propositions expressing the goal |
| `SkewSeed`, `SkewSeed.toSeed` | The old skew-symmetric input and its weighted reading `E := B`, `D := 1`, `K = B` |
| `Examples.nonSkewSeed` | The reference's non-skew input of `tex/target-theorem.tex` §4 |

All are in namespace `ClusterSkeleton`. The actual space is nonempty
(`Seed.point_nonempty`, witness `Seed.unitPoint`: all `a_j = 1` and mutable
`b_i = 2`). Defining an interface does not construct an inhabitant.

**`Unimodular` is the reference hypothesis, not a strengthening.** The PDF states
`E ∈ GL_d(ℤ)` and then *derives* equality with `1`: "In fact `det E = 1`: a
nonsingular real skew-symmetric matrix has positive determinant, so
`det E = det K/det D̃ > 0`, while unimodularity gives `det E = ±1`"
(`tex/target-theorem.tex` §1). Given the `Seed` fields, `IsUnit S.E.det` and
`S.E.det = 1` therefore have the same models. The library records the weighted
consequences `Seed.det_K` (`det K = det E · ∏ d_i`),
`Seed.det_K_of_unimodular` (`det K = ∏ d_i`) and `Seed.isUnit_det_K`; the
baseline's `det B = 1` survives only as the integer-lattice fact
`Seed.B_det`. The implication `IsUnit S.E.det → S.Unimodular` is **not** a Lean
declaration and is taken on the PDF's authority — entry **N1** of the
[audit](skeleton-audit.md) §3.

## What the theorem proves

```lean
def ClusterSkeleton.FirstGeometricTarget : Prop :=
  ∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S

theorem ClusterSkeleton.FullSkeleton.firstGeometricTarget : FirstGeometricTarget
```

The quantifier is over an arbitrary weighted `Seed d` and the only hypothesis is
`S.Unimodular`. There is no `D = 1`, no skewness hypothesis on `E`, no
restriction on the mutable set, and no added hypothesis anywhere in the chain.

For every such input the construction supplies a smooth real manifold of
dimension `2d` on that fixed space, with smooth immersive coordinate inclusion
(`SmoothAtlas.inclusion_smooth`, `SmoothAtlas.inclusion_immersion`) and dense
initial torus (`dense_initialTorus`). It constructs a smooth real one-form `λ`
whose exterior derivative is symplectic on all of `Seed.Point`
(`GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha` on `Set.univ`,
nondegeneracy at every point including the zero locus) and agrees on the torus
with

```
Im ( (1/2) Σ_{i,j} (K i j) dlog(a_i) ∧ dlog(a_j) ) ,     K i j = (E i j : ℚ) * D j
```

i.e. with the reference's `im Ω_T` — **the same sign, no transpose and no extra
factor**; the coefficient is the weighted `K`, not the integral `E`
(`FullSkeleton.torus_anchor`, `GlobalTwoForm.omega_torus`).

It constructs the same Liouville field `ι_Z dλ = λ`
(`GlobalLiouvilleField.Z`, `GlobalLiouvilleField.contraction_exteriorDerivative`)
and its native smooth flow for all real times
(`NativeCompleteFlow.completeFlow`), and proves

**`trappedSet Φ = coordinateCap`**  (`FullSkeleton.trappedSet_eq_coordinateCap`).

The same equality is also available in the reference's stratified form,

```
trappedSet Φ = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val,
```

as `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`, obtained from the cap
equality and `coordinateCap_eq_iUnion_lambdaStratum`. The union runs over the
independent subsets of the mutable vertices; each `lambdaStratum S I` with
`I ⊆ S.mutable` is compact (`isCompact_lambdaStratum`). This is a restatement of
the same proved equality, not an additional claim.

On the chart side, the node charts have the explicit torus rank the reference
states: for independent `I`, `IndependentNodeChart.complementRank_eq_sub_two_mul_card`
proves `SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card`,
with `IndependentNodeChart.two_mul_card_le : 2 * I.card ≤ d`. In the weighted
setting the input of that computation is the reference statement itself: the rows
of `S.B = S.Eᵀ` indexed by `I` are the reference columns `c_i = E e_i`, and
`S.B⁻¹ = (E⁻¹)ᵀ` is the blueprint's "the integer inverse of `E` restricts to a
retraction" (`independent_rows_inverse_pairing`, `Seed.B_det`).

The quantifiers are `∀ input, ∃ smooth presentation, λ, Z, Φ, …`, exactly the
PDF's `∀(n,E,D̃,M) ∃(smooth structure, λ, Z, Φ)`. A flow, completeness, cap
invariance, and either skeleton inclusion are not extra hypotheses. The final
theorem chooses the admissible cutoff parameters `ε = 1`, `κ = 3`, `δ = 1`
(`FullSkeleton.liouvilleSkeletonTarget`, via
`liouvilleSkeletonTarget_of_parameters`).

| Declaration | Proof or construction |
| --- | --- |
| `SmoothAtlas.presentation` | Constructs the native manifold presentation |
| `FullSkeleton.liouvilleData` | Constructs the primitive, field, and complete flow package |
| `FullSkeleton.torus_anchor` | Checks the prescribed **weighted** torus two-form, coefficient `K` |
| `FullSkeleton.trappedSet_eq_coordinateCap` | Proves the equality for the same flow |
| `coordinateCap_eq_iUnion_lambdaStratum` | Proves the cap is the union of the strata `Λ_I` over independent `I` |
| `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` | Proves the stratified form of the same equality |
| `isCompact_lambdaStratum` | The reference's per-stratum compactness |
| `IndependentNodeChart.homeomorph`, `IndependentNodeChart.complementRank_eq_sub_two_mul_card` | The node chart `𝒩^I × (ℂ*)^{d-2\|I\|}` and its literal torus rank |
| `FullSkeleton.liouvilleSkeletonTarget` | Proves the seed-specific target |
| `FullSkeleton.firstGeometricTarget` | Proves the universally quantified weighted target |

The final declarations are in
[`FullSkeleton.lean`](../ClusterSkeleton/FullSkeleton.lean); their proposition is
in [`GeometryTarget.lean`](../ClusterSkeleton/GeometryTarget.lean). The strata are
defined and identified with the cap in
[`CapStrata.lean`](../ClusterSkeleton/CapStrata.lean), and the torus rank is in
[`IndependentNodeSmooth.lean`](../ClusterSkeleton/IndependentNodeSmooth.lean).
The weighted linear algebra that the dynamics use is
[`SymmetrizerAlgebra.lean`](../ClusterSkeleton/SymmetrizerAlgebra.lean) (Mathlib
only) and [`SeedAlgebra.lean`](../ClusterSkeleton/SeedAlgebra.lean) (specialized
to a `Seed`).

## What a reader must cite for the whole PDF statement

`LiouvilleSkeletonTarget` contains only density, the presentation and
`LiouvilleData` witnesses, the torus anchor and `trappedSet = coordinateCap`.
Theorem `thm:target` of `tex/target-theorem.tex` also asserts the stratified
union, compactness of each `Λ_I`, and the node-chart shape
`𝒩^I × (ℂ*)^{n-2|I|}` with `2|I| ≤ n`. These are separate theorems, and the
final consumer and any statement review must cite all of them, not
`FirstGeometricTarget` alone:

| PDF clause | Lean declaration(s) |
| --- | --- |
| items 1–3 and `Skel(Φ) = C_E` of `thm:target` | `FullSkeleton.firstGeometricTarget` / `liouvilleSkeletonTarget` |
| `C_E = ⋃_{I independent} Λ_I` | `coordinateCap_eq_iUnion_lambdaStratum`, `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` |
| "Each `Λ_I` in this union is compact" | `isCompact_lambdaStratum` (and `isCompact_coordinateCap` for the cap) |
| `U_I ≅ 𝒩^I × (ℂ*)^{n-2\|I\|}`, `2\|I\| ≤ n` | `IndependentNodeChart.homeomorph`, `IndependentNodeChart.complementRank_eq_sub_two_mul_card`, `IndependentNodeChart.two_mul_card_le` |

`coordinateCap_eq_iUnion_lambdaStratum` is flow-free, so the stratified form
follows for *any* witness the target's existential produces; a consumer never has
to reach inside the target to recover `NativeCompleteFlow.completeFlow`.

This split is inherited from the superseded baseline and is not a weighted
regression; it is recorded as finding **R4** in the [audit](skeleton-audit.md) §3,
together with the statement review's own citation list.

## `D = I` recovery and the non-skew instance

* **Recovery.** `SkewSeed` is the old skew-symmetric input and `SkewSeed.toSeed`
  its weighted reading with `E := B`, `D := 1`. Then
  `SkewSeed.toSeed_K : (S.toSeed).K i j = (S.B i j : ℚ)`: the weighted form
  coefficient at `D = 1` is *literally* the old integer matrix, with no sign
  change and no transpose, so the recovered Liouville field is not time-reversed.
  The carrier is the same set (`SkewSeed.carrier_set_eq`) and the canonical
  identification is `SkewSeed.pointHomeomorph`, with
  `SkewSeed.pointHomeomorph_val` by `rfl`. The old loci on the old carrier, their
  image/preimage identifications and the flow conjugation are
  `ClusterSkeleton/SkewSeedRecovery.lean`, described in
  [the recovery design note in Git history](https://github.com/Hu-Mingyuan/cluster-skeleton/blob/efb0d0d53fb2ee75f8934972f08cb0bb7a818a79/docs/weighted-recovery-plan.md); the packaged statement
  `SkewSeed.skeleton_recovery` is `ClusterSkeleton/SkewSeedSkeleton.lean`. Both are
  in the accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9` and are
  audit roots of the receipt. The [audit](skeleton-audit.md) §1.11
  gives the clause-by-clause breakdown, the elaboration evidence, and the recorded
  decision **not** to claim a transported smooth structure or a term identity of
  the recovered flow with the baseline's.
* **Non-skew instance.** `Examples.nonSkewSeed` is the PDF's
  `E = [[0,1,-1,0],[-2,0,0,-1],[1,0,0,0],[0,1,0,0]]`, `D = diag(1,2,1,2)`,
  `M = {0,1}` (zero-based), with `Examples.nonSkewSeed_unimodular`,
  `nonSkewSeed_not_skew`, `nonSkewSeed_entries`, `nonSkewSeed_weights_ne`,
  `nonSkewSeed_K_transpose` and `nonSkewSeed_det_K` all **proved**, not assumed.
  Applying the final theorem to it is the single line
  `FullSkeleton.firstGeometricTarget 4 Examples.nonSkewSeed Examples.nonSkewSeed_unimodular`,
  which is the definition of `nonSkewSeed_target_of_firstGeometricTarget`. The
  consumers `Examples.nonSkewSeed_liouvilleSkeletonTarget`,
  `nonSkewSeed_target_of_firstGeometricTarget`, `nonSkewSeed_side_checks`,
  `nonSkewSeed_trappedSet` and `nonSkewSeed_trappedSet_iUnion` are
  `ClusterSkeleton/Examples/NonSkewSkeleton.lean` in the accepted source commit
  `a575aa236b485672f0606bba6ebc80571671f8a9`, and all five are audit roots of the
  receipt. This consumer supplements, and never replaces, the universal theorem.

## Scope and trust boundary

This proves real smooth symplectic geometry, not algebraic smoothness or a
complex-manifold structure. Holomorphic extension of `Ω` itself, finite type, cap
products, cocores, and HMS are not claimed. The scope is the **weighted
unimodular** case with mutable acyclicity and variable frozen coordinates:
arbitrary positive rational `D`, `E` not assumed skew, column exponents, no
principal-coefficient statement. Both mathematical statement review and Lean
checking are necessary; a Lean build checks elaboration, not whether the
statements mean the intended mathematics. The statement-level comparison is
[`skeleton-audit.md`](skeleton-audit.md), whose inputs are the two delivered
semantic reviews of the weighted stages.

## Verification status

The weighted library is verified at accepted source commit
`a575aa236b485672f0606bba6ebc80571671f8a9`, receipts of 10 November 2026. A
managed `horizon-lean-check ClusterSkeleton` passed (9029 jobs, Lean 4.34.1 /
Lake 5.0.0, snapshot verified) and `python3 scripts/verify.py` then ended with
`FULL_GEOMETRIC_TARGET_VERIFIED`. The root import closure contains the whole
library. Only the foundational axioms `propext`, `Classical.choice` and
`Quot.sound` are permitted, and every audited root reports exactly those three.

What now exists for this source:

* the accepted-source manifest —
  [`../verification/accepted-library.json`](../verification/accepted-library.json)
  binds the 65 library files of commit `a575aa2…` by SHA-256;
* the receipt —
  [`../verification/publication-check.json`](../verification/publication-check.json)
  with `status: passed`, `dependency_worktrees_clean: true` and
  `source_stability_verified: true`: 65 modules, 1811 audited declarations, 72
  `#print axioms` roots, 73 hashed inputs;
* the four logs for this source —
  [`../verification/toolchain.log`](../verification/toolchain.log),
  [`../verification/build.log`](../verification/build.log),
  [`../verification/final-consumer.log`](../verification/final-consumer.log) and
  [`../verification/axioms.log`](../verification/axioms.log);
* the weighted statement review —
  [`../verification/statement-review.md`](../verification/statement-review.md),
  which also lists the residual notes (R4 and the one-place consumer, the node
  chart being a homeomorphism, R-N1 on the two carriers of the recovery, R5–R7).

This is a verified result, not an acceptance decision: accepting the phase and
the objective is the maintainer's call.
