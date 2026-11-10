# Mathematical statement review

Scope: independent reading of the generalized final target, its constructed
witnesses, the native geometric interfaces, and the geometric portion of the
supplied manuscripts `target-theorem.pdf` and `proof-blueprint.pdf`. This review
is separate from compilation and is not a claim of a line-by-line independent
reproof of the entire Lean library.

## Outcome

No hidden theorem-equivalent premise, no hidden skew-symmetry, `D = I` or
equal-weight assumption, no circular use of the desired skeleton equality, and no
weakening of the agreed first-stage real-geometric target was found.

- The input is the manuscript's: an integral exchange matrix `E` with no
  skewness hypothesis, an arbitrary positive rational diagonal symmetrizer `D`
  with `K = E·D` skew-symmetric, an arbitrary mutable set with acyclic mutable
  block, and unimodularity of the full matrix. `Seed.Unimodular` (`det E = 1`) is
  the manuscript hypothesis `E ∈ GL_n(Z)`, which forces `det E = 1`.
- `FullSkeleton.firstGeometricTarget : FirstGeometricTarget` is universally
  quantified over `(d, S)` with `S.Unimodular` as its only hypothesis and no
  instance argument. The concrete non-skew input of the manuscript is realized by
  `Examples.nonSkewSeed` with `nonSkewSeed_unimodular`, `nonSkewSeed_not_skew`
  and `nonSkewSeed_weights_ne`.
- The carrier is the actual exchange-equation subtype with inherited topology and
  the manuscript's **column** exponents `P_i^± = ∏_j z_j^{[±E_ji]_+}`. Frozen
  coordinates remain nonzero variables, and determinant one concerns the full
  matrix.
- The native real manifold has dimension `2*d`; the literal coordinate inclusion
  is proved smooth and immersive, and the node charts are constructed, not
  assumed.
- The logarithmic form in the target has coefficient `K = E·D` with the
  manuscript's factor `1/2` and sign; its imaginary part is the object proved
  nondegenerate and closed on the whole space, and equal to `Im Ω_T` on the dense
  initial torus.
- The primitive is the manuscript's `λ_ac = λ_tor + dH` with
  `λ_tor = uᵀ K dθ` and the weighted `H = Σ_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)`;
  its native exterior derivative is proved equal to the separately constructed
  global symplectic form.
- The field is determined by contraction with that primitive, `ι_Z dλ = λ`. The
  radial equations are weight-free because `d_i B_ij = −K_ij` cancels the weight,
  not because `d_i = 1`; the weight survives in the angular equation as
  `η̇_i = (1/d_i) ∂_{u_i} H`. Matrix inversion uses only `det K = ∏ d_i ≠ 0`.
- Actual native integral curves are extended in both time directions using proved
  finite-time confinement; the complete flow is chosen after existence is proved.
- The cap is defined by coordinate equations; the trapped set is defined by
  compact closure of forward orbits. The two inclusions concern the same
  constructed complete flow. The final theorem takes no supplied flow, cap
  invariance, completeness, or either set inclusion as a premise.
- Admissible cutoff parameters are instantiated by `(1,3,1)`; they do not
  specialize frozen coordinates. Nonemptiness is witnessed by `a=1, b=2`.
- **The `D = I` case is recovered as a theorem, with its geometry and its
  conventions.** `SkewSeed` is the accepted baseline's `Seed` structure verbatim
  (skew-symmetric integral `B`, acyclic mutable block, `det B = 1`), and
  `SkewSeed.toSeed` reads it as a weighted seed with `E := B` and `D = 1`, so
  the weighted form matrix is `K = B` itself: no transpose, no sign change, no
  extra factor, and therefore no time reversal of the Liouville flow. The two
  exchange monomials are interchanged with unchanged sum, so the two carriers
  are literally the same subset of the same ambient coordinate space
  (`SkewSeed.carrier_set_eq`) and the identity map on coordinates is a
  homeomorphism (`SkewSeed.pointHomeomorph`, whose `.val` identity is `rfl`).
  `SkewSeed.skeleton_recovery` is universally quantified over every
  skew-symmetric seed with `det B = 1` — its only hypothesis — and asserts, for
  one smooth presentation and one Liouville datum: density of the old initial
  torus on the old carrier; that the anchored two-form of that very datum is the
  old logarithmic form written with the old **integer** matrix `(B i j : ℂ)`
  (`SkewSeed.torus_anchor_old_matrix`,
  `SkewSeed.liouvilleData_torus_anchor_old_matrix`); and that the flow
  conjugate to that datum's complete flow — the same flow at the same times,
  read on the old carrier — has exactly the old coordinate cap `C_B` as its
  dynamical skeleton, in both the cap form and the stratified form
  `⋃_I Λ_I` over the old independence predicate
  (`SkewSeed.liouvilleData_trappedSet_conjFlow`, `…_iUnion`). Each old stratum
  and the old cap are compact (`SkewSeed.isCompact_lambdaStratum`,
  `SkewSeed.isCompact_coordinateCap`), and the baseline chart rank
  `d − 2|I|` holds for the old input by instantiation, because unimodularity and
  independence are the same propositions on both readings (`Iff.rfl`). The
  smooth structure enters **existentially**, through
  `LiouvilleSkeletonTarget S.toSeed`, exactly as `target-theorem.tex` quantifies
  it: no transported smooth structure on the old subtype and no term identity
  with the baseline library's constructed flow is claimed, and the recovery
  module's docstring and `docs/weighted-recovery-plan.md` §2 record that
  decision and its reason.
- **A genuinely non-skew input is covered by the same universal theorem.**
  `Examples.nonSkewSeed` is defined by the manuscript's literals
  `E = [[0,1,−1,0],[−2,0,0,−1],[1,0,0,0],[0,1,0,0]]`, `D = diag(1,2,1,2)`,
  `M = {0,1}` in Lean's zero-based indexing. `Examples.nonSkewSeed_side_checks`
  collects, in literal form and all proved, the three data, `det E = 1`,
  positivity of the weights, entrywise skew-symmetry of `K = E·D`, acyclicity of
  the mutable block in the orientation of the `Seed.acyclic` field, and the
  failure of skew-symmetry of `E` itself (`E 0 1 = 1` while `E 1 0 = −2`, with
  `D 0 ≠ D 1`, so no single rescaling makes `E` skew and the `D = I` library
  cannot express this input). The geometric statement for it is obtained by
  instantiating the universal theorem —
  `Examples.nonSkewSeed_target_of_firstGeometricTarget` applies
  `FullSkeleton.firstGeometricTarget` at `d = 4` — not by a separate argument,
  and no decision procedure outside the kernel is used: every declaration
  depends on exactly `propext`, `Classical.choice`, `Quot.sound`, and no
  `native_decide`, `decide +native` or `Lean.ofReduceBool` occurs in the
  library. This consumer **supplements** the quantified theorem;
  `FullSkeletonConsumer.original_general_target : FirstGeometricTarget` is
  unchanged.

The reviewed mathematical files are bound to exact hashes in
[`accepted-library.json`](accepted-library.json). The independent build and
axiom evidence is [`publication-check.json`](publication-check.json).

## What the target itself does and does not contain

`LiouvilleSkeletonTarget` contains density of the torus, the smooth presentation
with its immersive coordinate inclusion, the smooth primitive, the globally
nondegenerate closed two-form with the prescribed torus value, the smooth field
with `ι_Z dλ = λ`, the complete jointly smooth flow, and
`Skel(Φ) = C_E`. The manuscript's remaining clauses are proved separately and a
consumer must cite them explicitly:

| clause | declaration |
| --- | --- |
| `C_E = ⋃_{I independent} Λ_I` | `coordinateCap_eq_iUnion_lambdaStratum` (flow-free), `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` |
| each `Λ_I` compact | `isCompact_lambdaStratum` |
| `U_I ≅ N^I × (C*)^{n−2|I|}` | `IndependentNodeChart.homeomorph`, `…complementRank_eq_sub_two_mul_card` |
| `2|I| ≤ n` | `IndependentNodeChart.two_mul_card_le` |

## Exposition checks

The proof checks the full residual node block for nondegeneracy with the weighted
coefficients, the explicit smooth cutoffs, cancellation of the primitive at
simultaneous zeros, zero persistence before completeness, finite-time bounds
including positive frozen lower bounds, and both skeleton inclusions.

Cap invariance is proved by propagating the character equation and partner
vanishing, rather than inferred solely from tangency to a potentially singular
subset. The reverse inclusion treats nonzero interior coordinates and initially
zero coordinates separately. Compactness for normalized partners is applied on
the closed zero divisor, not assumed on an arbitrary open chart.

## Exact boundary

The theorem proves a real smooth Liouville structure with the prescribed weighted
torus form, a jointly smooth complete two-sided flow, and full trapped-set
equality, for every integral unimodular `E` and every positive rational diagonal
`D` with `E·D` skew. It does not assert a separately assembled complex-manifold
structure, algebraic smoothness, holomorphic extension, finite type, cap-product
descriptions, generalized cocores, Weinstein structure, an affine Kähler
comparison, or categorical HMS. It makes no claim for singular completions,
arbitrary cyclic seeds, or inputs without a unimodular completion.

The recovery of the `D = I` case is a statement about the old exchange-equation
subtype for its topological and dynamical conclusions — density of the old
torus, the forward-orbit skeleton identity in both forms, compactness of the old
cap and of each old stratum — and about the weighted reading `S.toSeed` of the
same ambient subset for the smooth presentation, the primitive, the two-form,
its nondegeneracy, the field and the completeness of the flow, which the
baseline target also quantifies existentially. The identification of the two
carriers is the identity map on ambient coordinates and is proved to be a
homeomorphism; it is not promoted to a diffeomorphism, so no charted or smooth
structure is asserted on the old subtype, and no equality of constructed terms
with the baseline library's atlas, primitive or flow is asserted.

The global flow is chosen after proving existence. It is not advertised as an
executable numerical flow algorithm.

The PDFs are mathematical expositions, not machine-checked documents. The
kernel-checked statements are the Lean declarations whose exact source and
dependency hashes are recorded by the verifier.

## Residual notes

These are recorded so that a maintainer reads the result in full view of them.
None is a defect; none requires a change to a Lean statement or proof.

- **R4 — the target does not contain the whole boxed identity.** `thm:target`
  reads `Skel(Φ) = C_E = ⋃_I Λ_I` with each `Λ_I` compact and the node charts;
  `LiouvilleSkeletonTarget` contains only the first equality. Every remaining
  clause is proved for every weighted seed, and
  `PdfTargetConsumer.pdf_target` (in `verification/FullSkeletonConsumer.lean`) now states all of them in
  **one** Lean type for an arbitrary unimodular `S : Seed d`, for the same
  presentation, Liouville datum and flow the target's existential produces. R4 is
  therefore a shape-of-the-statement note, not a coverage gap, but a reader of
  `FirstGeometricTarget` alone still does not see the stratified form.
- **The node chart is a homeomorphism, not an isomorphism of varieties.**
  `IndependentNodeChart.homeomorph` lands in `≃ₜ`; the manuscript's `N` is
  `{(x,y,t) : xy = 1+t, t ≠ 0}` and Lean's `Node` is its image `{(x,y) : xy ≠ 1}`
  under `t = xy − 1`, a bijection, so the sets agree. The smooth structure the
  target actually uses is carried separately by `IndependentNodeSmooth` and
  `SmoothAtlas`. The manuscript's own statement of this clause is structural, so
  this is presentational.
- **R-N1 — the `D = I` recovery is stated on two carriers.** The topological and
  dynamical conclusions are re-obtained literally on the old subtype `S.Point`
  (density of the old torus, the forward-orbit skeleton identity in both forms,
  compactness of the old cap and of each old stratum, over the old independence
  index set). The charted space and `IsManifold`, the inclusion smoothness and
  immersivity, the primitive, the two-form and its nondegeneracy, the field, the
  contraction equation and the flow's smooth action and ODE are obtained on the
  weighted reading `S.toSeed` of the same ambient subset, which the baseline
  target also quantifies existentially; the anchor clause quantifies over
  `initialTorus S.toSeed` while the density conjunct is on the old carrier, and no
  single Lean `Prop` is "the baseline target for `S : SkewSeed d`". The recovery
  module's docstring and `docs/weighted-recovery-plan.md` §2 state this and do not
  leave the old smooth structure implicitly claimed. The cheapest strengthening,
  if a maintainer wants the anchor on the old torus too, is roughly 12–20 lines
  from `SkewSeed.liouvilleData_torus_anchor_old_matrix` and
  `SkewSeed.pointHomeomorph_val`; a full `SmoothPresentation`-level transport along
  `pointHomeomorph` is roughly 300–600 lines and one new module. Neither is done
  here, because this mission changes no mathematical statement.
- **R-N2 — closed by this receipt.** The 17 `#print axioms` roots the recovery
  review named as missing are now in `AxiomAudit.lean`; the root list is 72, up
  from 25. Axiom *coverage* was never affected: the audit loop has always walked
  all declarations of all listed modules.
- **R5 — `PrimitiveCutoffs.rho_neg` / `vartheta_neg` are not in the library.**
  Both are true and one `simp` each, and both are needed only for a *pointwise*
  `D = I` statement, not for the weighted chain or for anything proved here.
- **R6 — `GlobalPrimitive.exists_global_primitive` is existential in the form**, so
  a consumer that needs the explicit primitive must use `GlobalPrimitive.alpha`
  together with `alpha_eq_eta`.
- **R7 — the stronger pointwise old-carrier claim is not made.** Stating it needs
  either the full transport of R-N1 or the missing cutoff lemmas of R5.
- **D1 and D2 are repaired** in the accepted source: the docstrings of
  `exchangeCharacter_eq_zpow_product` and `Seed.Point.outgoing_ne_zero` now state
  the column-exponent orientation that their statements prove.
- **N1 / G3 — unimodularity is taken on the manuscript's authority.** The baseline
  derived `det B = ±1 ⇒ det B = 1` from the Pfaffian identity for an integral skew
  matrix; the weighted `E` is not skew, and the manuscript's own derivation
  (`det K = det E · ∏ d_i > 0` forces `det E > 0`) is carried by no Lean
  declaration. A reviewer therefore reads `IsUnit E.det → S.Unimodular` as the
  manuscript's step, not as a Lean theorem.

## Verification state

Verified at commit `a575aa236b485672f0606bba6ebc80571671f8a9` (the accepted
library source), receipts of 10 November 2026: 65 modules, 1811 audited
declarations, 72 `#print axioms` roots each depending on exactly `propext`,
`Classical.choice`, `Quot.sound`, 73 hashed inputs. This records a verified
result and a completed review; it is not a statement that the phase or the
objective has been accepted, which is a maintainer's decision.

The statement-level reviews this file summarizes are
[`docs/reviews/final-statement-review.md`](../docs/reviews/final-statement-review.md)
and
[`docs/reviews/recovery-nonskew-review.md`](../docs/reviews/recovery-nonskew-review.md),
with the earlier
[`stage-a-semantic-audit.md`](../docs/reviews/stage-a-semantic-audit.md) and
[`stage-b-semantic-audit.md`](../docs/reviews/stage-b-semantic-audit.md).
