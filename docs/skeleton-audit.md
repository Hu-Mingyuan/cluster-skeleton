> Scope: this guide records the **weighted (skew-symmetrizable)** Lean library at
> accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`, whose root
> `ClusterSkeleton` builds with the pinned toolchain. Its citations of §1.1–§1.10
> were first checked against the stage-C tree
> `114d63939d72cfb5c81d6bd22dd0811e053805a3`, which the accepted source extends
> additively. The superseded `D = I`
> baseline appears only where it is explicitly compared with the weighted library
> — §1.2, §1.6, the three-column table §1.10, the change inventory §2.1 and the
> re-evaluated entries of §3 — and in the recovery section §1.11; everywhere it is
> labelled as the superseded library at `e62c101`. The accepted-source manifest,
> the verifier run and the receipts for this source exist and are bound to the
> accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`; see §5.

# Audit of the supplied skeleton proof against the Lean construction

Scope: the **weighted unimodular** case with **mutable acyclicity** and
**variable frozen coordinates**, i.e. the reference input of
`tex/target-theorem.tex` §1 with **no** specialization — an integral `E` that is
not assumed skew-symmetric, an arbitrary positive rational diagonal
`D̃ = diag(d_i)` with `K = E D̃` skew-symmetric, and `det E = 1`. Nothing below
restricts to `D̃ = I`, to principal coefficients, or to a fixed frozen value.

**Summary.** The supplied weighted proof has a Lean counterpart in
`ClusterSkeleton/*.lean` in the scope stated above. The final theorem is

```lean
def ClusterSkeleton.FirstGeometricTarget : Prop :=
  ∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S

theorem ClusterSkeleton.FullSkeleton.firstGeometricTarget : FirstGeometricTarget
```

with the stratified cap identity `coordinateCap_eq_iUnion_lambdaStratum` /
`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` and the explicit chart rank
`IndependentNodeSmooth.complementRank_eq_sub_two_mul_card`. Entries **G1** and
**G2** of §3 give the exact declarations; **G3** is an optional determinant
convention, outside the required statement. The convention comparisons
**N1–N9** require no additional Lean changes. **R4** is closed at consumer
level, with the statement-citation boundary recorded below; **R5–R7** remain
documented scope notes. The docstring defects **D1**, **D2** are closed in the
accepted source.

Four facts fix every sign in the weighted translation, and each of them is the
opposite of what the baseline recorded:

1. the exchange monomials are the reference's **column** monomials, literally —
   there is no monomial interchange left (§1.2);
2. the exchange ratio and the node character are the reference's, not their
   inverses: `exchangeCharacter = t_i`, `rowLog = +v_i`,
   `angle = +(η_i - π)`, `nodeLog = +Log(-t_i)` (§1.3, §1.4);
3. the logarithmic two-form and `λ_tor` carry the **weighted** coefficient
   `K = E D̃`, with the reference's sign (§1.5);
4. `H` carries the factor `d_i` in every summand, `H_Lean = +H_ref`, and the Lean
   primitive **adds** `dH` (§1.6).

Their joint consequence is the dynamics of §1.7: the weights cancel from the
radial equation and survive only in the angular one, as `η̇_i = (1/d_i) ∂_{u_i} H`.

Inputs compared:

* reference proof: [`tex/proof-blueprint.tex`](tex/proof-blueprint.tex) and
  [`tex/target-theorem.tex`](tex/target-theorem.tex) (the weighted mathematical
  target at `e62c101`, with final verification status and scope clarified for
  publication), with [`target-theorem.md`](target-theorem.md) and
  [`proof-blueprint.md`](proof-blueprint.md);
* Lean source: the accepted source commit
  `a575aa236b485672f0606bba6ebc80571671f8a9`, whose 65 library files are hashed
  in [`../verification/accepted-library.json`](../verification/accepted-library.json).
  The citations of §1.1–§1.10 were first checked against the stage-C tree
  `114d63939d72cfb5c81d6bd22dd0811e053805a3`, which the accepted source extends
  additively (the recovery modules, the skeleton package and the non-skew
  consumers are new files; `NodeCoordinates.lean`, `ZeroSet.lean` and
  `CapIndependence.lean` differ from it in docstrings only, mechanically verified
  code-identical), and re-checked against the accepted source;
* the two delivered weighted semantic reviews, whose convention tables are the
  backbone of §1.10:
  `docs/reviews/stage-a-semantic-audit.md` at commit
  `4fe163223e348afdd4e0214970c451b797bb06c8` (seed fields, column exponents,
  form coefficient and sign, the `SkewSeed` route, findings D1, D2, R1–R4) and
  `docs/reviews/stage-b-semantic-audit.md` at commit
  `08472e04e10e000f813ed9bbb4abe81a0aa0fc6a` (two-form and node coefficient,
  `beta`, `H` summand by summand, `alpha = beta + dH`, the hand derivation of
  the flow equations, findings R5–R7);
* the final statement review `docs/reviews/final-statement-review.md` at commit
  `24b7bef8aaea7fd098e8ccd10474502d5a7320fa` (the PDF-clause-to-declaration map
  of its item 6, the byte-level baseline diff of its item 7, and findings R4, A1,
  D1, D2), published while this rewrite was being written;
* the matrix-role analysis in this audit (all 152 matrix-role sites of the
  dynamics modules, roles (a)–(h)), and the proved recovery in
  `SkewSeedRecovery.lean` and `SkewSeedSkeleton.lean`.

**Verification method.** Declaration names and types were checked with
`lake env lean Scratch.lean` at the repository root in the pinned
Lean 4.34.1 / Lake 5.0.0 Mathlib and FsFltz environment, after
`lake build ClusterSkeleton` completed on the source commit above; the scratch
file was deleted before committing.

* **Names and types.** Every Lean declaration cited below was confirmed with
  `#check` at `114d639`. That pass corrected three citations inherited from the
  baseline: `logarithmicImaginaryValue` is
  `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue` (declared in
  `GeometryTarget.lean`, whose namespace is `ClusterSkeleton`), and
  `coordinateCap_strictCapIndices_independent`, `norm_eq_one_of_not_strict` and
  `independent_rows_inverse_pairing` are declared directly in namespace
  `ClusterSkeleton` by `CapIndependence.lean` and `NodeCoordinates.lean`.
* **Definitional claims.** Each quoted unfolding was confirmed by `rfl`: the
  **column** exponents of `positiveMonomial`/`negativeMonomial` and
  `S.B i j = S.E j i` (§1.1, §1.2), `S.K i j = (S.E i j : ℚ) * S.D j` (§1.1),
  `exchangeCharacter` and `normalizedPartner` (§1.3), `A`, `rowLog` (in all
  three of its spellings), `angle` and `nodeLog` (§1.4), the coefficient `K` and
  the factor `½` of `logarithmicImaginaryValue` (§1.5), the weighted `H` sum and
  `alpha = beta + dH` (§1.6), `LocalAngularDynamics.nu` as the inverse of the
  weighted `K` with its minus sign (§1.7), `radialLength`, `rho`, `vartheta`,
  `angularRadius` and `dominance` (§1.8), and the `coordinateCap`,
  `lambdaStratum` and `initialTorus` descriptions (§1.9). The constant
  identifications `a = κ` (`radial = A + κ` for `A ≤ -(2κ-2ε)`) and `δ₀ = 2ε`
  (`radial = 0` for `A ≥ -2ε`) follow from `radial_tail` and `radial_eq_zero`.
* **The sign argument.** Its ingredients are no longer parity facts about the
  cutoffs but the **column convention** itself: `rowLog = +v_i` and
  `angle = +(η_i - π)` hold literally (`rfl`, §1.4), so `ρ(v_i)` and `β(η_i)`
  need no evenness/oddness to match. The parity facts
  `rho (-x) = rho x` and `vartheta δ (-T) = -vartheta δ T` are still true and are
  still needed — but only for the `D = I` recovery of §1.11, where `H` really is
  negated. They are **not** Lean statements: finding **R5**.
* **The statements in part 3.** **G1** and **G2** are implemented in the weighted
  source with their baseline statements unchanged (both are purely ambient or
  purely integral, see the entries). Their proofs are not reproduced again here.

Compilation evidence: a managed `horizon-lean-check ClusterSkeleton` at the
accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9` completes with
status *passed*, return code 0, snapshot verified, toolchain Lean 4.34.1 / Lake
5.0.0, warnings only, and `python3 scripts/verify.py` then ends with
`FULL_GEOMETRIC_TARGET_VERIFIED`. The receipt records **65 modules, 1811 audited
declarations, 72 `#print axioms` roots** each depending on exactly `propext`,
`Classical.choice`, `Quot.sound`, and **73 hashed inputs**; §5 records the state
in full. The files
[`../verification/README.md`](../verification/README.md),
[`../verification/build.log`](../verification/build.log),
[`../verification/axioms.log`](../verification/axioms.log),
[`../verification/publication-check.json`](../verification/publication-check.json)
and
[`../verification/accepted-library.json`](../verification/accepted-library.json)
are bound to that commit and are evidence for the weighted theorem. Formal acceptance is recorded separately in
[archon-acceptance.json](../verification/archon-acceptance.json).

**Citation convention.** Declarations are cited as `File.name`, where `File` is
the module file under `ClusterSkeleton/`. The full Lean name is usually
`ClusterSkeleton.File.name`, but several files declare into a different
namespace, so the file prefix is a *location*, not always a name prefix:

* the files `Seed`, `ZeroSet` (see below), `CapSet`, `CapStrata`,
  `CapIndependence`, `CoordinateLoci`, `TrappedSet`, `InitialTorusDensity`,
  `GeometryTarget`, `GeometryNativeBridge`, `FormExtensionUniqueness`,
  `NodeCoordinates`, `NodeLogExtension`, `TorusChart`, `SmoothAtlas`,
  `LaurentCoordinates`, `IndependentLaurentCoordinates`,
  `IntegralBasisCompletion`, `IndependentNodeChart` and `SkewSeed` open the
  namespace `ClusterSkeleton` itself, so e.g. `CapStrata.lambdaStratum` is
  `ClusterSkeleton.lambdaStratum`, `CapIndependence.coordinateCap_strictCapIndices_independent`
  is `ClusterSkeleton.coordinateCap_strictCapIndices_independent`, and
  `GeometryTarget.SmoothPresentation.logarithmicImaginaryValue` is
  `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue`
  (`IndependentNodeChart.lean` opens the inner namespace
  `IndependentNodeChart` for its chart declarations);
* `ZeroSet.lean` declares into `ClusterSkeleton.Seed.Point`;
* `SkewSeedRecovery.lean` and `SkewSeedSkeleton.lean` declare into
  `ClusterSkeleton.SkewSeed` (so `SkewSeedSkeleton.skeleton_recovery` is
  `ClusterSkeleton.SkewSeed.skeleton_recovery`), and
  `Examples/NonSkewSkeleton.lean` into `ClusterSkeleton.Examples`;
* `IndependentNodeSmooth.lean` continues the namespace
  `ClusterSkeleton.IndependentNodeChart` (so
  `IndependentNodeSmooth.complementRank_eq_sub_two_mul_card` is
  `ClusterSkeleton.IndependentNodeChart.complementRank_eq_sub_two_mul_card`);
* `FiniteTimeConfinement.lean` also contains the namespace
  `ClusterSkeleton.CoordinateBounds` (cited as
  `FiniteTimeConfinement.CoordinateBounds.*`).

A few cited helpers are `private` in their file and are marked as such; a
proposed statement that needs one of them must either re-prove it or drop the
`private` modifier.

---

## 1. Convention map

Throughout, `u_j = log‖z_j‖`, `θ_j = arg z_j`, `c_i = E e_i`,
`v_i = c_i(u) = ∑_j E_{ji} u_j`, `η_i = c_i(θ)`, and `d_i = D i`.

### 1.1 Data and hypotheses

| Reference | Lean | Remark |
| --- | --- | --- |
| index sets `M ⊔ F`, `n = \|M\|+\|F\|` | `S.mutable : Finset (Fin d)` inside `Fin d`, `d = n` | `Seed.lean`; frozen = complement of `S.mutable`; Lean indices are zero-based |
| `E ∈ GL_n(ℤ)`, `D̃ = diag(d_1,…,d_n)` with `d_j ∈ ℚ_{>0}`, `K = E D̃`, `K^T = -K` | fields `Seed.E : Matrix (Fin d) (Fin d) ℤ`, `Seed.D : Fin d → ℚ`, `Seed.D_pos : ∀ i, 0 < D i`, `Seed.skewSymmetrizable : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)` | the field is the reference sentence "`E_{ij} d_j = -E_{ji} d_i`, rather than `E_{ij} = -E_{ji}`" verbatim; `E` is **not** skew |
| `K = E D̃`, i.e. `K_{ij} = E_{ij} d_j` | `Seed.K : Matrix (Fin d) (Fin d) ℚ`, `Seed.K i j = (S.E i j : ℚ) * S.D j` (`Seed.K_apply`, `rfl`) | right multiplication by the diagonal (column scaling), **not** `D̃ E`, which would give `d_i E_{ij}`. `Seed.K_transpose : S.Kᵀ = -S.K`, `Seed.K_skew` |
| `B = E_{M,M}` acyclic (no directed cycle of positive entries) | `Seed.acyclic : WellFounded (fun i j : S.Mutable => 0 < S.E i j)` | the arrow convention is `E i j > 0` for `i → j`; equivalence with the cycle formulation is `Seed.wellFounded_iff_no_directed_cycle`, and `Seed.acyclic_exponent` gives the same well-foundedness for `0 < S.B i j` (the orientation is irrelevant on the finite mutable type) |
| unimodular completion `E ∈ GL_n(ℤ)`; "in fact `det E = 1`" | `Seed.Unimodular S : S.E.det = 1` | see **N1**: the PDF *derives* `det E = 1` from `det K/det D̃ > 0` and `det E = ±1`, so this is not a strengthening. Consequences: `Seed.det_K` (`det K = det E · ∏ d_i`), `Seed.det_K_of_unimodular` (`= ∏ d_i`), `Seed.det_K_ne_zero`, `Seed.isUnit_det_K`; the integer fact `Seed.B_det : S.B.det = 1` |
| frozen `z_j` invertible variables | `Seed.Point` carries `∀ f ∉ S.mutable, p.a f ≠ 0` (`Seed.Point.frozen_ne_zero`); no frozen value is fixed | no principal coefficients |
| exchange relations `z_i z_i' = P_i^+ + P_i^-` | `p.a i * p.b i = S.positiveMonomial p.a i + S.negativeMonomial p.a i` | `Seed.Point.exchange`; the carrier is the actual complex point set with the inherited subtype topology, and it is nonempty (`Seed.point_nonempty`, `Seed.unitPoint`) |
| `𝒜(B̃)` closed in `ℂ^{2m} × (ℂ*)^f` | `CapSet.isClosed_ambientCap` (private), `FiniteTimeConfinement.CoordinateBounds.isClosed_ambientBox` (private) / `isCompact_coordinateBox` | the reference uses closedness only for compactness arguments; Lean proves exactly those |
| independence of `I ⊂ M`: `E_{ij} = 0` for all `i,j ∈ I` | `Seed.Independent I : I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.E i j = 0` (`rfl`) | includes the diagonal, which is automatic from `Seed.E_diag_zero`; `Seed.Independent.exponent_eq_zero` supplies the exponent orientation |

**The sign lemmas that replace `Seed.skew`.** The baseline `Seed` carried a field
`skew : ∀ i j, B i j = -B j i`, and the proofs used it for three distinct facts.
The weighted `Seed` has no such field; each fact is now a lemma derived from
`skewSymmetrizable` together with `D_pos`, which is exactly the blueprint
sentence

> Positivity of the `d_i` implies `E_{ii}=0` and
> `E_{ij}=0 ⟺ E_{ji}=0`, with opposite signs when nonzero. These are the sign
> properties used in the zero-set proof.

| fact used by the baseline's `skew` | weighted lemma |
| --- | --- |
| no loops, `B i i = 0` | `Seed.E_diag_zero`, `Seed.B_diag_zero` |
| an arrow reverses sign | `Seed.E_neg_of_pos`, `Seed.E_pos_of_neg`, `Seed.E_pos_iff_neg`, `Seed.B_pos_iff_neg` |
| vanishing is symmetric | `Seed.E_eq_zero_iff`, `Seed.E_ne_zero_iff`, `Seed.B_eq_zero_iff` |
| skew-symmetry of the **form** matrix | `Seed.K_transpose`, `Seed.K_skew`, `SeedAlgebra.Kreal_transpose`, `SeedAlgebra.sum_sum_K_antisymm` |

Field-level generality is available separately: `SymmetrizerAlgebra.E_diag_zero`,
`SymmetrizerAlgebra.E_eq_zero_iff` and `SymmetrizerAlgebra.E_pos_iff_neg` prove
the same facts for an arbitrary field from `0 < D i` alone, and
`SymmetrizerAlgebra.K`, `K_transpose`, `det_K` are the Mathlib-only originals of
`Seed.K` and its determinant.

`grep -rn "S.skew" ClusterSkeleton/*.lean` at `114d639` matches only
`S.skewSymmetrizable`.

### 1.2 Exchange monomials: the reference's column exponents, literally

Reference (`tex/target-theorem.tex` §1):

> Use *column* exchange exponents throughout:
> `P_i^±(z) = ∏_{j=1}^n z_j^{[±E_{ji}]_+}`.

Lean (`Seed.lean`), confirmed by `rfl`:

```
positiveMonomial a i = ∏ j, a j ^ (S.E j i).toNat
negativeMonomial a i = ∏ j, a j ^ (-S.E j i).toNat
```

`(S.E j i).toNat = [E_{ji}]_+` and `(-S.E j i).toNat = [-E_{ji}]_+`, so
`positiveMonomial = P_i^+` and `negativeMonomial = P_i^-` **literally**, and
`Seed.Point` is the reference's `X_E` on the nose.

**The baseline's "the two exchange monomials are interchanged" no longer
holds.** In the baseline the Lean `positiveMonomial` was `∏_j a_j^{[B_{ij}]_+}`,
which for skew `B` equals the reference's `P_i^-`; every statement using one
monomial separately had to be read through that interchange. There is no
interchange at `114d639`: the sum, each individual monomial, and their ratio are
the reference's. The one place where the swap still appears is the `D = I`
recovery, where `SkewSeed.toSeed_positiveMonomial` records that the *old*
library's two monomials are exchanged relative to the weighted reading (§1.11).

**The abbreviation `S.B`.** The exponent matrix is named

```
abbrev Seed.Bexp : Matrix (Fin d) (Fin d) ℤ := S.Eᵀ
abbrev Seed.B := S.Bexp                    -- so S.B i j = S.E j i by rfl (Seed.B_apply)
```

so `S.B i j` *is* the column exponent, and
`Seed.positiveMonomial_eq_prod_B : positiveMonomial a i = ∏ j, a j ^ (S.B i j).toNat`
is the same statement in the other spelling. Two consequences matter when
reading the source:

* `S.B` keeps its baseline *name* but denotes the **transpose** of the baseline's
  matrix; at `D̃ = I` it is `-K`. It is therefore correct in the exponent,
  adjacency, character and integer-lattice roles and **wrong** in the
  form-coefficient role. Stage A recorded this as risk R2 and the stage-B review
  discharged it by inventory: no form-coefficient site holds `S.B` at `6cdcef7`
  or later, and §1.5–§1.7 below cite `S.K` at every such site.
* `S.B i j` and `S.E j i` are definitionally equal at default transparency, so
  `exact`, `rfl` and `change` cross the identification while `rw` and
  `simp only` do not. `Seed.B_apply` is the bridge; stage C repaired nine proof
  sites that had relied on `simp` normalizing the old spelling.

**Orientation: `acyclic` versus `acyclic_exponent`.** The field is
`WellFounded (fun i j : S.Mutable => 0 < S.E i j)`, i.e. the PDF's arrow set
`i → j` with `B_{ij} > 0` restricted to `M`. The zero-set argument needs the
*other* orientation, `0 < S.B i j = 0 < S.E j i` ("`j` occurs in `P_i^+`"), which
is the blueprint's `B_{j_{r-1}i} > 0 ⇒ P_i^+(p) = 0` step; that is
`Seed.acyclic_exponent`, proved from the field by `Relation.transGen_swap`, and
it is what `ZeroSet` inducts on. Both orientations are equivalent to the PDF
hypothesis on the finite mutable type. The statement text of
`ZeroSet.Seed.Point.outgoing_ne_zero` is unchanged from the baseline while its
*meaning* is now about predecessors — see **D2**.

### 1.3 The exchange ratio is the reference character; node coordinates

```
exchangeCharacter p i = positiveMonomial p.a i / negativeMonomial p.a i     (rfl)
                      = ∏ j, p.a j ^ (S.E j i)        (exchangeCharacter_eq_zpow_product)
```

Reference: `t_i = z^{c_i} = P_i^+/P_i^-` with `c_i = E e_i`, i.e.
`t_i = ∏_j z_j^{E_{ji}}`. Hence

```
exchangeCharacter p i = t_i        (NOT 1/t_i; the baseline had the inverse)
rowLog p i            = +v_i = c_i(u)          (see 1.4)
```

Node data:

| Reference | Lean | Relation |
| --- | --- | --- |
| `x = z_i` | `p.a i` | equal |
| `y = z_i'/P_i^-` | `normalizedPartner p i = p.b i / negativeMonomial p.a i` (`rfl`, `i : S.Mutable`) | **equal**; the baseline's was `y/t_i` |
| `t = t_i` | `exchangeCharacter p i` (`i : Fin d`) | **equal**; the baseline's was `1/t_i` |
| `𝒩 = {xy = 1+t, t ∈ ℂ*}` | `IndependentNodeChart.Node = {uv : ℂ × ℂ // uv.1*uv.2 ≠ 1}`, equation `NodeCoordinates.normalized_node_equation : p.a i * normalizedPartner p i = 1 + exchangeCharacter p i` | **the reference node `x y = 1 + t` on the nose**, no longer in reciprocal coordinates |

The divisor conditions are the reference's directly: `t_i = -1 ⇔
exchangeCharacter = -1`, and `y = 0 ⇔ normalizedPartner = 0 ⇔ p.b i = 0` on an
independent locus, where both monomials are units
(`NodeCoordinates.positiveMonomial_ne_zero_on_independent_locus`,
`negativeMonomial_ne_zero_on_independent_locus`).

> **D1 (documentation defect at `114d639`, closed in the accepted source).** The old docstring of
> `NodeCoordinates.exchangeCharacter_eq_zpow_product` says "the reference's
> inverse character `1/t_i`", which is the *baseline's* relation and the opposite
> of what its own statement proves. See §3.

### 1.4 Torus logarithmic coordinates: every sign is the reference's

| Reference | Lean | Relation |
| --- | --- | --- |
| `u_j = log\|z_j\|` | `TorusCorrection.A S p j = Real.log ‖p.a j‖` (`rfl`), also `GlobalLiouvilleField.A` and `DominanceCutoff.logNorms`, which `PrimitiveLocalization` and `PrimitiveResidual` reuse | equal |
| `θ_j = arg z_j` | `Complex.arg (p.a j)`, used only through `TorusPrimitive.angleCovector` (`= Im(da_j/a_j)`) | equal |
| `v_i = log\|t_i\| = c_i(u) = ∑_j E_{ji} u_j` | `TorusCorrection.rowLog S p i = ∑ j, (S.B i j : ℝ) * A S p j`, and by `rfl` also `= ∑ j, (S.E j i : ℝ) * Real.log ‖p.a j‖` | **`rowLog = +v_i`** (the baseline's was `-v_i`); the three spellings `TorusCorrection.rowLog`, `PrimitiveLocalization.rowLog` and `PrimitiveResidual.logRow` agree by `rfl` |
| `η_i = arg t_i = c_i(θ)` | `Complex.arg (exchangeCharacter p i)` | `= +η_i` in `ℝ/2πℤ` |
| `η_i - π` (signed distance to the divisor) | `PrimitiveLocalization.angle p i = (Complex.log (-exchangeCharacter p i)).im` (`rfl`), `= Complex.arg (-exchangeCharacter p i)` by `Complex.log_im` | **`= +(η_i - π)`** |
| `Log(-t_i) = v_i + i(η_i-π)` | `PrimitiveLocalization.nodeLog p i = Complex.log (1 - p.a i * normalizedPartner p i)` (`rfl`, `i : S.Mutable`), `= Complex.log (-exchangeCharacter p i)` by the node equation | **`nodeLog = +Log(-t_i)`**; its real part is `rowLog` (`NativeNodePrimitive.node_real_logRow`) and its imaginary part is `angle` |
| `c_i(dθ) = dη_i` | `PrimitiveResidual.tau S hdet i p = ∑ j, (S.B i j : ℝ) • angleCovector j p` | `= +dη_i`, and this is *proved*, not asserted: `PrimitiveResidual.tau_eq_nodeAngle_differential` identifies it with `d(Im Log(1 - x_i y_i))` |

So **nothing changes sign** in passing to the Lean variables: `u`, `θ`, `v`,
`η-π`, `Log(-t)` and `dη` are all the reference's. This is the single largest
difference from the baseline, where `v`, `η-π` and `Log(-t)` were all negated and
two cutoff parities (`rho` even, `vartheta` odd) silently absorbed the
difference. Those parities are no longer load-bearing for the weighted
statements; they reappear only in the `D = I` recovery (§1.11) and are still
unstated in Lean (**R5**).

### 1.5 The logarithmic two-form: coefficient `K`, with the reference's sign

Reference (`tex/target-theorem.tex` §1, identically in `tex/proof-blueprint.tex`):

> `Ω_T = ½ ∑_{j,l} K_{jl} dlog z_j ∧ dlog z_l`

and `thm:target` item 2: "`ω = dλ` is nondegenerate and `ω|_T = im Ω_T`".

Lean (`GeometryTarget.SmoothPresentation.logarithmicImaginaryValue`, `rfl`):

```
Im ( (1/2) ∑ i ∑ j (S.K i j : ℂ) *
       ( (da_i v / a_i)(da_j w / a_j) - (da_i w / a_i)(da_j v / a_j) ) )
```

With the convention `(α ∧ β)(v,w) = α(v)β(w) - α(w)β(v)` this is term for term
`Im(½ ∑_{i,j} K_{ij} dlog a_i ∧ dlog a_j)`: the factor `½` is present as in the
reference, the first index of `K` sits on the first tangent slot exactly as the
reference's first `dlog` factor does, and the cast is of the **rational**
`K = E D̃`, not of `E`. **This is the reference form with the same sign, no
transpose and no extra factor** — the definite answer of stage-A review item 3,
cross-checked there three ways (the torus formula below, the node identity of the
next paragraph, and the index placement that makes the contraction of §1.7 come
out with the reference's signs).

The torus side is `GlobalTwoForm.matrixForm` with the same coefficient, and its
real expansion is proved:

```lean
theorem TorusPrimitive.matrixForm_real (v w : Fin d → ℂ) :
    GlobalTwoForm.matrixForm S ![v, w] =
      (∑ i, ∑ j, (S.K i j : ℝ) * (v i).re * (w j).im) -
      (∑ i, ∑ j, (S.K i j : ℝ) * (w i).re * (v j).im)
```

which is literally `(∑_{j,l} K_{jl} du_j ∧ dθ_l)(v,w)`, the blueprint's own line
"On the initial torus, `Im Ω = ∑_{j,l} K_{jl} du_j ∧ dθ_l`" (the reduction uses
only `K^T = -K`, i.e. `SeedAlgebra.sum_sum_K_antisymm`). The Lean side is pinned
by `GlobalTwoForm.omega_torus` and re-exported in the final theorem as
`FullSkeleton.torus_anchor`; closedness is `GlobalTwoForm.exteriorDerivative_omega`
and uniqueness of the extension is
`FormExtensionUniqueness.smoothAtlas_twoForm_extension_unique` and
`LocalFormGluing.existsUnique_smooth_gluing`.

`TorusPrimitive.beta` is `λ_tor`:

```lean
def beta := covectorForm _ (fun p => ∑ i, ∑ j, ((S.K i j : ℝ) * Real.log ‖p.a i‖) • angleCovector S hdet j p)
```

i.e. `∑_{j,l} K_{jl} u_j dθ_l = u^T K dθ`, with `u` on the **first** index and
`dθ` on the second, no factor `½` and no minus (`TorusPrimitive.evalOne_beta`,
whose docstring states exactly that); `TorusPrimitive.exteriorDerivative_beta`
proves `d beta = GlobalTwoForm.omega` on the initial torus, which also fixes the
library's exterior-derivative normalisation as
`d(∑ K_{ij} u_i dθ_j) = ∑ K_{ij} du_i ∧ dθ_j`, with no factor `2` or `½`.

**The node identity and the node coefficient.** The blueprint's node-chart
normal form rests on

> Indeed the `x_i` row is determined by `∑_j K_{ij} dlog z_j = -d_i dlog t_i`.

In Lean that row is `NodeTwoForm.row_outsideLog_weighted`:
`∑_{j ∉ I} (S.K i j : ℂ) * outsideLog … j t = -(S.D i : ℂ) * logParameter S I x (Sum.inl i) t`,
where `logParameter … (Sum.inl i)` is `dt_i/t_i` and
`IndependentNodeSmooth.rawParameters S I x (Sum.inl i) = x_i y_i - 1 = t_i`. It
holds precisely because `K i j = E i j * D j`. The resulting node term of
`NodeTwoForm.complexForm` is

```lean
∑ i : {i // i ∈ I}, (-(S.D i : ℂ) * (rawParameters S I x (Sum.inl i))⁻¹) • wedge (du S I i) (dv S I i)
```

i.e. `-∑_{i∈I} (d_i/t_i) dx_i ∧ dy_i`, which equals the blueprint's
`∑_{i∈I} d_i dlog t_i ∧ dlog x_i` because
`dlog t_i ∧ dlog x_i = t_i^{-1} dy_i ∧ dx_i` on `x_i y_i = 1+t_i`. The sign flip
relative to the baseline's `+(rawParameters …)⁻¹` is **forced** by
`K_{ij} = -d_i B_{ij}`; at a chart centre (`x_i = 0`, so `t_i = -1`) the block is
`+(S.D i : ℂ)` (`NodeTwoForm.complexForm_boundary`), consistent with
`-d_i/(-1) = +d_i`. The identification with `Im Ω` is proved, not inspected:
`NodeTwoForm.complexForm_torus` and `NodeTwoForm.localForm_torus` against
`logarithmicImaginaryValue` on the torus part of the node domain, and
`GlobalTwoForm.omega_eq_localForm` makes `omega` the common extension — the
blueprint's own "The local extensions agree on overlaps by density of the initial
torus".

**Weighted node nondegeneracy.** The blueprint writes the skew matrix in the node
coordinates as

```
( 0    -D_I   0  )
( D_I   A     B_0)
( 0    -B_0ᵀ  C  )
```

> It is nonsingular, so `C` is nonsingular, by eliminating the first two block
> rows … Pairing against the `y_i` directions, then the `s_a` directions, then
> the `x_i` directions proves nondegeneracy, using `d_i ≠ 0` and nonsingularity
> of `C`.

Lean matches it block by block:

| blueprint | Lean |
| --- | --- |
| `D_I` | `NodeNondegeneracy.weightProjection`, with `weightProjection i (Sum.inl i') = -(S.D i : ℂ)` on the diagonal and `0` on the complement index |
| the whole matrix | `NodeNondegeneracy.normalMatrix = Matrix.fromBlocks 0 weightProjection (-(weightProjection)ᵀ) complexResidual`, skew by `NodeNondegeneracy.normalMatrix_skew` |
| `-B_0ᵀ` | `NodeNondegeneracy.complexResidual_skew`, from `Seed.K_skew` |
| `Ω_0`, constant coefficients | `NodeTwoForm.residualMatrix = Tᵀ K_J T` with `NodeTwoForm.outsideBlock = S.K.submatrix …` — **rational**, while the integral `T = independentRowInverseMatrix` is unweighted |
| "eliminating the first two block rows … using `d_i ≠ 0`" | `SymmetrizerAlgebra.residualBlock_eq_zero_of_mulVec_eq_zero` with `δ i = -(S.D i : ℂ)` and `δ i ≠ 0` from `Seed.D_pos`; `NodeNondegeneracy.residualBlock_normalMatrix`, `normalMatrix_injective`, `isUnit_det_normalMatrix` |
| "so `C` is nonsingular" | `NodeNondegeneracy.complementMatrix_kernel`, `complementMatrix_isUnit` |
| the three pairings, in that order | `NodeNondegeneracy.complexForm_boundary_nondegenerate`, then `realForm_boundary_nondegenerate`, `localForm_boundary_nondegenerate`, `zeroSet_localForm_nondegenerate` |

Every division is by a nonzero `d_i`; this is what replaces the baseline's
`det B = 1`. On the torus block the corresponding fact is
`TorusNondegeneracy.complexMatrix` (entries `(S.K i j : ℂ)`) with
`complexMatrix_det : det = ∏ (S.D i : ℂ)` and
`isUnit_complexMatrix_det` — again `IsUnit`, never `= 1`. Nondegeneracy is
claimed on the **whole space**: `GlobalSymplectic.nondegenerate_omega` quantifies
over an arbitrary `p : S.Point` with no torus hypothesis, routing through that
point's own zero-set chart (`NodeNondegeneracy.zeroSet_chart_mem`), and
`GlobalSymplectic.isSymplecticOn_omega` is stated on `Set.univ`. Density alone
does not prove nondegeneracy at boundary points, and it is not used for it.

### 1.6 `H` with the weights, and `alpha = beta + dH`

Reference (`tex/proof-blueprint.tex`, proof of `thm:acyclic-skeleton`):

> `χ_i := ∏_{j∈M: B_{ji}≠0} ϑ(u_i − u_j)`,
> `H := ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)`,
> `λ_ac := λ_tor + dH`

Lean (`TorusCorrection.H`, `manuscript_formula`; `rfl`):

```
H ε κ δ p = ∑ i ∈ S.mutable, (S.D i : ℝ) *
    ( radial ε κ (A S p i) * dominance S ε i (A S p)
      * rho (rowLog S p i) * angular S δ p i )

alpha = TorusPrimitive.alpha S hdet H = beta + covectorForm (differentialCovector H)
```

Summand by summand (stage-B review item 3, re-confirmed here by `rfl`):

| reference factor | Lean factor | identification |
| --- | --- | --- |
| `d_i` | `(S.D i : ℝ)` | **present in every summand**, outside the whole product |
| `h(u_i)` | `PrimitiveCutoffs.radial ε κ (A S p i)` | §1.8; the argument is `u_i`, not `v_i` |
| `χ_i` | `DominanceCutoff.dominance S ε i (A S p)` | index set `S.B i j ≠ 0 ⟺ E_{ji} ≠ 0 ⟺ B_{ji} ≠ 0`, the reference's exactly (and symmetric anyway, `Seed.E_eq_zero_iff`) |
| `ρ(v_i)` | `PrimitiveCutoffs.rho (rowLog S p i)` | `rowLog = +v_i` **literally** (§1.4), so no evenness is needed |
| `β(η_i)` | `PrimitiveCutoffs.vartheta δ (arg (-exchangeCharacter p i))` | `arg(-t_i)` is the principal representative of `η_i - π` (§1.4), so no oddness is needed |

Hence, with no sign correction anywhere,

```
H_Lean = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i) = H_reference ,   literally,
alpha  = λ_tor + dH = λ_ac .
```

**Both of the baseline's sign inversions are gone, and the `-dH` that cancelled
them is gone with them.** In the baseline `rowLog = -v_i` and
`arg(-exchangeCharacter) = -(η_i-π)`, `rho` is even and `vartheta δ` is odd, so
`H_Lean = -H_ref`, and the baseline's `alpha = beta - dH` restored `λ_ac`. At
`114d639` the Lean primitive **adds** `dH`, definitionally (`TorusPrimitive.alpha`
is an `rfl`-level `+`, so it cannot drift), and `H_Lean` is `+H_ref`.

This is the one sign pair that the target's torus anchor **cannot** detect:
`alpha = beta ± dH` differ by an exact form, so `d alpha` — and hence the clause
`evalTwo (exteriorDerivative primitive) = logarithmicImaginaryValue` of
`LiouvilleSkeletonTarget` — is insensitive to it. The statement that does detect
it is `trappedSet = coordinateCap` itself, through the radial estimate
`u̇_i ≤ u_i - h(u_i) < 0`, which fails outright for the wrong sign. It was
therefore settled by derivation: stage-B review items 3 and 4, whose hand
computation is reproduced in §1.7, and whose result is cross-checked inside Lean
by `LocalPrimitive.eta_eq_torus` (see below).

**The node consistency check, with the weight outside.** The blueprint's local
rewriting is

> `v_i dθ_i − u_i dη_i + d((u_i+a)(η_i−π)) = v_i dθ_i + (η_i−π) du_i + a dη_i`

and its `H` near a node is (`eq:acyclic-H-near`)

> `H = ∑_{i∈I} d_i(u_i + a)(η_i − π) + H'`.

In Lean the per-index scalars are **unweighted** —
`PrimitiveLocalization.correction` is `h χ ρ β` for one index and
`PrimitiveLocalization.affineCorrection κ i p = (logNorms S p i + κ) * (nodeLog p i).im`
is `(u_i+κ)(η_i−π)` (`rfl`) — and *every* sum that consumes them supplies
`(S.D j : ℝ)`: `RegularCorrection.H_eq_sum`, `RegularCorrection.regularH`,
`RegularCorrection.singularH` (so `RegularCorrection.H_split` is
`eq:acyclic-H-near` with `RegularCorrection.surviving` the reference's index set
`{k ∈ M\I : B_{ik} = 0 ∀ i ∈ I}`), and `NativeNodePrimitive.block`. That is the
division of labour the reference prescribes, since its `d_i` sits outside the
per-index product.

`NodePrimitiveCancellation.cancellation` is the rewriting itself:
`A • dT - S • dθ - d((A+κ)T) = lambda κ`, with `A = u_i`,
`S = Re nodeLog = +v_i`, `T = Im nodeLog = +(η_i-π)`. So

```
lambda κ = -( v_i dθ_i - u_i dη_i + d((u_i+κ)(η_i-π)) ) ,
```

**minus** the reference's per-node primitive block (the baseline's `lambda` was
`+`, because its `S` and `T` were negated). The weight multiplies the whole
block: `NativeNodePrimitive.block κ I hI = covectorForm (fun q => ∑ i : I, (S.D i.val : ℝ) • lambda …)`,
which is the reference's `∑_{i∈I} d_i(…)` given the unweighted
`affineCorrection`. On the divisor, `NodePrimitiveCancellation.lambda_zero` and
`NativeNodePrimitive.lambda_boundary` give `lambda κ i q v = (1+κ)(y_i da_i(v)).im`,
the negative of the reference's
`Im(Log(1-z_iy_i)/z_i dz_i) + a d arg(1-z_iy_i) → -(1+a) Im(y_i dz_i)`; smooth
extension across `{z_i = 0}` with value `-y_i` is
`NodeLogExtension.nodeLogQuotient`, `nodeLogQuotient_zero`,
`analyticOnNhd_nodeLogQuotient`.

Consequently the local primitive is

```lean
def LocalPrimitive.eta (ε κ δ) (p) :=
  PrimitiveResidual.residual S hdet p.zeroSet
    - NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent
    + RegularCorrection.regularForm S hdet p.zeroSet ε κ δ
```

(the baseline read `residual + block - regularForm`; both flips move with
`alpha = beta + dH`), and `PrimitiveResidual.beta_decomposition` is
`eq:acyclic-ltor-split`

> `λ_tor = ∑_{i∈I} d_i(v_i dθ_i − u_i dη_i) + ∑_{j,l∈(M⊔F)\I} K_{jl} u_j dθ_l`

term for term, with the `I`-block carried by the factor `-(S.D i : ℝ)` and the
complementary block `PrimitiveResidual.residual` carrying `K`
(supporting identity `PrimitiveResidual.split_sum`, which uses independence
through `K i j = E i j · D j` and `E i j = 0` on `I`).

**The whole sign triple is machine-checked together.**
`LocalPrimitive.eta_eq_torus` proves
`eta S hdet ε κ δ p q = TorusCorrection.alpha S hdet ε κ δ q` on
`neighborhood ε κ δ p ∩ initialTorus S`. Flipping any one of the three signs —
`alpha`'s `+dH`, `eta`'s `-block`, `eta`'s `+regularForm` — breaks it, so this
Lean theorem is an internal consistency proof of §1.6, not a restatement.
`LocalPrimitive.eta_zero_partners` (`residual + regularForm` where all partners
vanish) is the matching statement on the divisor.

### 1.7 Liouville field and flow: weights cancel radially, survive angularly

* **Sign convention.** Reference: `ι_Z dλ = λ`. Lean `LiouvilleData.contraction`:
  `evalTwo (exteriorDerivative primitive) p (field p) v = evalOne primitive p v`,
  the **same** convention; uniqueness of the field is
  `LiouvilleData.field_eq_liouvilleVector`, the constructed field is
  `GlobalLiouvilleField.Z` (`= liouvilleVector (GlobalPrimitive.alpha …)`), and
  the torus-level statement is `TorusLiouvilleDynamics.contraction`.
* **The two contraction equations.** The blueprint splits
  `ι_Z Im Ω = λ_tor + dH` into

  > `K^T u̇ = K^T u + ∂_θ H`,  `−K θ̇ = ∂_u H`.

  In Lean the first is `TorusLiouvilleDynamics.radial_matrix_equation` (paired
  against `angularTangent j`) and the second is
  `TorusLiouvilleDynamics.angular_equation` (paired against `radialTangent i`),
  both read off `TorusLiouvilleDynamics.omega_real`, whose coefficient is
  `(S.K i j : ℝ)` in both sums.
* **`∂_θ H` and the weight cancellation.** Only `angular_i ≡ η_i - π` depends on
  `θ`, through `η_i = c_i(θ) = ∑_l (S.B i l) θ_l`, so with
  `a_i := h(u_i) χ_i ρ(v_i) β'(η_i)` (Lean's unweighted
  `TorusLiouvilleDynamics.amplitude` times `deriv (vartheta δ)`),

  ```
  ∂_{θ_l} H = ∑_{i∈M} d_i a_i (S.B i l) = -∑_i a_i K_{il} ,
  ```

  by `SeedAlgebra.K_eq_neg_D_mul_B` (`d_i B_{il} = -K_{il}`; the `ℝ`-cast of the
  row sum is `PrimitiveResidual.sum_K_row_real`). This is the blueprint's
  `∂_θ H = K ∑_i a_i e_i` paired over the other index, the two differing by
  `K^T = -K`. In Lean the step is the lemma

  ```lean
  theorem TorusLiouvilleDynamics.differential_H_angular_K … :
      differentialCovector … (TorusCorrection.H S ε κ δ) p (angularTangent S hdet p hp j) =
        -∑ i ∈ S.mutable, amplitude S ε κ i (TorusCorrection.A S p) *
          deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) * (S.K i j : ℝ)
  ```

  the weighted form `TorusLiouvilleDynamics.differential_H_angular` (each summand
  carrying `(S.D i : ℝ)`) being its `B`-spelling.
* **Radial equation: the baseline statement, unchanged.**

  ```lean
  theorem TorusLiouvilleDynamics.radial_matrix_equation … (j : Fin d) :
      (∑ i, (S.K i j : ℝ) * (logarithmicComponents … p i).re) =
        (∑ i, (S.K i j : ℝ) * TorusCorrection.A S p i) -
        ∑ i ∈ S.mutable, amplitude S ε κ i (TorusCorrection.A S p) *
          deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) * (S.K i j : ℝ)
  ```

  This is the baseline statement with `S.B ↦ S.K` at all three occurrences and
  the **same minus sign**; **no `(S.D i : ℝ)` appears**, because the weight of
  each `H` summand was absorbed by `d_i B_{ij} = -K_{ij}` before the
  cancellation. Cancelling `K^T` — by `SeedAlgebra.Kreal_vecMul_injective`, which
  needs only `SeedAlgebra.isUnit_det_Kreal`, **not** a determinant equal to `1` —
  gives `TorusLiouvilleDynamics.real_logarithmicComponents` and then

  ```lean
  theorem mutable_radial_equation … (hi : i ∈ S.mutable) :
      (logarithmicComponents … p i).re = TorusCorrection.A S p i -
        PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) *
          DominanceCutoff.dominance S ε i (TorusCorrection.A S p) *
          PrimitiveCutoffs.rho (TorusCorrection.rowLog S p i) *
          deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i))

  theorem frozen_radial_equation … (hi : i ∉ S.mutable) :
      (logarithmicComponents … p i).re = TorusCorrection.A S p i
  ```

  which are **byte-identical to the baseline statements** and are `eq:acyclic-flow`

  > `u̇_j = u_j (j∈F)`,  `u̇_i = u_i − h(u_i) χ_i ρ(v_i) β'(η_i) (i∈M)`

  verbatim. Three independent reasons make them survive the generalization
  unchanged: the weights cancel; `rowLog` is `+v_i`, so
  `rho (rowLog …)` is `ρ(v_i)` literally rather than through evenness; and
  `arg(-exchangeCharacter p i)` is `+(η_i-π)`, so `deriv (vartheta δ) (…)` is
  `β'(η_i)` literally rather than through evenness of `vartheta'`. The glued
  statements are `GlobalLiouvilleField.mutable_radial_equation` /
  `frozen_radial_equation` / `frozen_radial_equation_torus`.
* **Angular equation: this is where the weight lives.**

  ```lean
  theorem TorusLiouvilleDynamics.angular_equation … (i : Fin d) :
      (∑ j, (S.K i j : ℝ) * (logarithmicComponents … p j).im) =
        -differentialCovector … (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i)

  theorem TorusLiouvilleDynamics.angular_equation_row … (i : Fin d) :
      (S.D i : ℝ) * (∑ j, (S.B i j : ℝ) * (logarithmicComponents … p j).im) =
        differentialCovector … (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i)
  ```

  The **minus** in the `K` form is the consequence of `alpha = beta + dH`; the
  second statement is the first rewritten by `SeedAlgebra.sum_K_row`
  (`∑_j K_{ij} x_j = -d_i ∑_j B_{ij} x_j`) and, since
  `∑_j (S.B i j) (…)_{im} = c_i(θ̇) = η̇_i`, it is `eq:acyclic-angle-flow`

  > `η̇_i = (1/d_i) ∂_{u_i} H`

  with the reference's `+`. The logarithmic-germ forms are
  `TorusLiouvilleDynamics.angular_equation_logarithmic`,
  `angular_equation_partial_deriv` and
  `GlobalLiouvilleField.angular_equation_partial_deriv`, all with `S.K` on the
  left and a leading minus on the right. The second half of
  `eq:acyclic-angle-flow`, `v̇_i = v_i - ∑_{k∈M} B_{ki} a_k`, is the `S.B`-row sum
  of the radial equation and needs no matrix algebra (role (d) of
  the matrix-role analysis in this audit §1.7).
* **`θ̇ = -K^{-1} ∂_u H`** is not stated separately; see **N4**. The identities
  that make it readable are in `SeedAlgebra`, each the Lean form of a blueprint
  line:

  | blueprint | Lean (`SeedAlgebra`, with `SymmetrizerAlgebra` originals) |
  | --- | --- |
  | `K e_i = d_i c_i`, `d_i c_i = K e_i` | `K_mulVec_single` (`SymmetrizerAlgebra.K_mulVec_single`) |
  | `∑_j K_{ji} u_j = d_i ∑_j E_{ji} u_j = d_i v_i` | `sum_K_col` (`SymmetrizerAlgebra.sum_K_col`) |
  | `∑_l K_{il} dθ_l = -d_i dη_i` | `sum_K_row` (`SymmetrizerAlgebra.sum_K_row`) |
  | `c_i^T K^{-1} = -e_i^T/d_i`, `c_i(K^{-1}x) = -x_i/d_i` | `c_inv_K`, `vecMul_Ecol_inv_Kreal`, `Breal_mulVec_inv_K` (`SymmetrizerAlgebra.vecMul_E_col_inv_K`, `sum_E_col_mul_inv_mulVec`) |
  | `d_i B_{ij} = -K_{ij}` | `K_eq_neg_D_mul_B`, `K_transpose_eq_D_mul_B` |
  | converting a `K`-system into the `B`-system | `Kreal_mulVec_eq_iff` |
  | `det K = det E ∏ d_i = ∏ d_i > 0`, only `IsUnit` used | `det_Kreal`, `det_Kreal_of_unimodular`, `isUnit_det_Kreal`, `Kreal_mul_inv`, `Kreal_inv_mulVec`, `Kreal_mulVec_inv`, `Kreal_vecMul_injective`, `Kreal_mulVec_injective` |
  | the **integer** inverse of `E`, `det = 1`, unweighted | `det_Breal`, `isUnit_det_Breal`, `Breal_vecMul_injective`, `exists_inverse_bound_Breal` |
* **Near a node.** `BoundaryTangency.local_H_radial` is `eq:acyclic-H-near`
  differentiated:
  `∂_{u_i} H = (S.D i : ℝ) * (PrimitiveLocalization.nodeLog q i).im`, i.e.
  `d_i(η_i - π)`. Combined with the `1/d_i` of `angular_equation_row` the weight
  cancels, so its consumer `BoundaryTangency.nodeLog_drift_torus` /
  `nodeLog_drift` keeps the baseline statement `Z nodeLog_i = nodeLog_i` — which,
  since `nodeLog = +Log(-t_i)`, is `eq:acyclic-divisor-flow`'s
  `ṫ_i = t_i Log(-t_i)` with the reference's sign, and
  `BoundaryTangency.deep_radius` is `u̇_i = -κ`, the reference's `u̇_i = -a` with
  `a = κ`. The divisor and partner rates
  `ZeroStratumInvariance.normSq_drift` (`Z|z_i|² = -2κ|z_i|²`) and
  `NormalizedPartnerNormDrift.normSq_drift_zero` (`Z|y_i|² = 2(1+κ)|y_i|²`) are
  **weight-free** and byte-unchanged from the baseline.
* **Masked and glued dynamics.** Off the torus the angular components are
  obtained by inverting the full weighted matrix:

  ```lean
  def LocalAngularDynamics.nu (ε κ δ) (p q) : Fin d → ℝ :=
    Matrix.mulVec (SeedAlgebra.Kreal S)⁻¹ (fun i => -LocalAngularDynamics.angularRhs S ε κ δ p q i)
  ```

  (`rfl`), with `LocalAngularDynamics.angularRhs` the masked `∂_{u_j} H`, each
  summand carrying `(S.D i : ℝ)` and its zero-stratum branch being
  `d_i(η_i - π)`. Only `isUnit_det_Kreal` is used. The two inverse identities are
  `AllStrataGrowth.full_matrix_nu_equation`
  (`∑_k K_{jk} ν_k = -angularRhs_j`) and
  `AllStrataGrowth.row_nu_equation` (`d_j ∑_k B_{jk} ν_k = angularRhs_j`), the
  pair that lets every baseline argument of the form "`∑_j B_{ij} x_j` after an
  inversion" transport unchanged. Accordingly
  `LocalAngularDynamics.nu_eq_torus`, `nu_eq_logarithmicComponents`,
  `nu_smooth`, `angularRhs_eq_radial`, `AllStrataGrowth.nu_center_growth`,
  `partner_drift_growth` and
  `InteriorPartnerPropagation.differential_character_of_unit_neighbors` all keep
  their baseline statements, while `AllStrataGrowth.angularRhs_center` and
  `InteriorPartnerPropagation.angularRhs_eq_self_of_unit_neighbors` gain the
  explicit `(S.D i : ℝ)`.
* **The uniform inverse bound** that the growth estimates use is
  `TorusLiouvilleDynamics.full_matrix_inverse_bound`, now stated with
  `(S.K i j : ℝ)` and proved in one term by
  `SeedAlgebra.exists_inverse_bound_Kreal`; the baseline's
  `R`/`det = 1`/`R⁻¹`/one-norm block is gone. This is one of the three places
  where `det B = 1` was replaced (the others being
  `real_logarithmicComponents` and `LocalAngularDynamics.nu`).

### 1.8 Cutoff dictionary — unchanged, and weight-free

Every cutoff is **unchanged from the baseline**, in statement and in meaning: the
reference's cutoff clauses contain no `d_i`, and the weights enter `H` only as the
outer factor of §1.6. The one change of reading is that `rho` and
`deriv (vartheta δ)` are now applied to the reference's own arguments `v_i` and
`η_i - π` rather than to their negatives, so their parities are no longer needed
(§1.4).

| Reference | Lean | Correspondence and properties |
| --- | --- | --- |
| `h ≤ 0`, `0 ≤ h' ≤ 1`, `u - h(u) < 0` on `u<0`, `h(u) = u+a` for `u ≤ -L`, `h = 0` near `[0,∞)` | `PrimitiveCutoffs.radial ε κ A = -radialLength ε κ * transitionPrimitive ((-A-2ε)/radialLength ε κ)`, `PrimitiveCutoffs.radialLength ε κ = 2*(κ-2ε)` (`rfl`) | `radial_nonpos`, `radial_deriv_nonneg`, `radial_deriv_le_one`, `radial_gt`, `radial_tail` (`radial = A + κ` for `A ≤ -radialLength-2ε`), `radial_eq_zero` (`= 0` for `A ≥ -2ε`), `radial_abs_le`/`radial_linear_growth` (`\|h(u)\| ≤ \|u\|+L`) |
| `a` | `κ` | from `radial_tail`; also the divisor rate `Z\|z_i\|² = -2κ\|z_i\|²` |
| `L` | `2κ - 2ε` (`= radialLength ε κ + 2ε`) | tail threshold of `radial` |
| `δ₀` with `h = 0` on `(-δ₀,∞)` | `2ε` | `radial_eq_zero` |
| `L > a > 0` | `0 < ε`, `2ε + 1 ≤ κ` | gives `a = κ > 0`, `L - a = κ - 2ε ≥ 1 > 0`, and `1 + κ > 0` for the partner rate |
| `ρ ∈ C_c^∞(ℝ,[0,1])`, `ρ = 1` near `0` | `PrimitiveCutoffs.rho x = Real.smoothTransition (2 - x^2)` (`rfl`) | `rho_eq_one` (`\|x\| ≤ 1`), `rho_eq_zero` (`\|x\| ≥ 2`), `rho_compactSupport`. Applied to `rowLog = +v_i`, so the evenness that the baseline needed is not used here (it is used in §1.11) |
| `β ∈ C^∞(ℝ/2πℤ)`, `supp β ⊂ (π-ε,π+ε)`, `β(η)=η-π` near `π`, `(η-π)β ≥ 0`, `β' ≤ 1` | `PrimitiveCutoffs.vartheta δ T = Real.arcsin (Real.sin T) * PrimitiveCutoffs.angularWindow δ T` (`rfl`), applied to `T = arg(-exchangeCharacter) = +(η-π)` | `vartheta_periodic`, `vartheta_representative_independent` (no angle lift is chosen — this replaces the reference's "lift in `(-ε,ε)`"), `vartheta_eq_self` (`= T` near `0`), `vartheta_support_principal` with radius `angularRadius δ = min (δ/2) (π/4)` (`rfl`), `vartheta_local_sign` (`T·ϑ(T) ≥ 0`), `vartheta_deriv_le_one` |
| `ε` of `supp β ⊂ (π-ε,π+ε)`, `0<ε<π` | `angularRadius δ` | **name collision**: the reference's `ε` is the angular support radius, the Lean `ε` is the dominance separation width. They are unrelated |
| `ϑ : ℝ → [0,1]` nonincreasing, `=1` on `(-∞,-1]`, `=0` on `[0,∞)` | `DominanceCutoff.chi ε x` | `chi_eq_one_iff` (`x ≤ -ε`), `chi_eq_zero_iff` (`x ≥ -ε/2`), `exists_chi`; Lean's cutoff vanishes already at `-ε/2`, a strictly stronger localization |
| `χ_i = ∏_{j∈M, B_{ji}≠0} ϑ(u_i-u_j)` | `DominanceCutoff.dominance S ε i A = ∏_{j ∈ mutableNeighbors S i} chi ε (A i - A j)` (`rfl`), `DominanceCutoff.mutableNeighbors S i = S.mutable.filter (S.B i · ≠ 0)` | `S.B i j ≠ 0 ⟺ E_{ji} ≠ 0 ⟺ B_{ji} ≠ 0`, the reference's index set exactly; `dominance_eq_one_of`, `dominance_eq_zero_iff` |
| `χ_iχ_j = 0` when `B_{ij} ≠ 0` | `DominanceCutoff.adjacent_exclusion` | identical statement; its input `Seed.B_eq_zero_iff` replaces the baseline's `skew` |
| the reference's `W` (all plateaus active) | `PrimitiveLocalization.region`/`neighborhood`, `PrimitiveLocalization.plateaus`, `adjacent_dominance_zero` | §**N9** |
| final admissible constants | `ε = 1`, `κ = 3`, `δ = 1` in `FullSkeleton.liouvilleSkeletonTarget` | gives `a = 3`, `L = 4`, `δ₀ = 2`, angular radius `min(1/2, π/4) = 1/2`; `GlobalPrimitive.exists_global_primitive` additionally exhibits `(1, 3, π/2)` |

### 1.9 Cap description — unchanged, and convention-free

Lean (`CapSet.coordinateCap`, `rfl`):

```
coordinateCap S = {p | (∀ f ∉ S.mutable, ‖p.a f‖ = 1) ∧
                       ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧ ((1 - ‖p.a i‖^2 : ℝ) : ℂ) * p.b i = 0}
```

This is **literally** the reference's `C_E = {|z_f| = 1 (f∈F), |z_i| ≤ 1,
(1-|z_i|²)z_i' = 0 (i∈M)}` of `tex/target-theorem.tex` §2. Likewise

```
lambdaStratum S I = {p | (∀ i : S.Mutable, (i:Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧
                         (∀ j, j ∉ I → ‖p.a j‖ = 1)}
initialTorus S    = {p | ∀ j, p.a j ≠ 0}
trappedSet flow   = {x | IsCompact (closure (flow.forwardOrbit x))}
```

are the reference's `Λ_I`, `T = {z_1⋯z_n ≠ 0}` and `Skel(Φ)`, with the closure in
the subtype topology ("The closure is taken in the actual exchange space").

**All four are stated purely in ambient coordinates `p.a`, `p.b`, so the weighted
generalization changes nothing about them.** They contain no exchange matrix, no
monomial, no character and no weight; the convention change of §1.2–§1.4 is
invisible to them, and their statements are byte-unchanged from the baseline.
What *did* change is the carrier they live on: `Seed.Point` is now the column
convention's exchange space. The stratified identity
`coordinateCap_eq_iUnion_lambdaStratum` and the compactness lemmas
`isClosed_lambdaStratum`, `isCompact_lambdaStratum`, `isCompact_coordinateCap`
are correspondingly unchanged, and their only seed-dependent input is
independence of the realized index set
(`CapIndependence.coordinateCap_strictCapIndices_independent`), whose proof now
inducts on `Seed.acyclic_exponent`. Entry **G1** of §3 records the history.

### 1.10 Consolidated table: baseline Lean / reference / weighted Lean

"Baseline Lean" is the accepted `D = I` library at commit `e62c101`, as certified
by the previous revision of this guide; "reference" is
`tex/target-theorem.tex` / `tex/proof-blueprint.tex`; "weighted Lean" is
`114d639`. This table is the merge of the convention tables of the two delivered
semantic reviews (stage-A item 7 at `4fe1632`, stage-B item 8 at `08472e0`),
re-checked against the delivered source. **It is the only place in this guide
where the baseline conventions are stated, and they are stated as history.**

| role | baseline Lean (`e62c101`) | reference (PDF) | weighted Lean (`114d639`) |
| --- | --- | --- | --- |
| exchange matrix | `S.B`, skew by the field `S.skew` | `E ∈ GL_n(ℤ)`, **not** skew; `K = E D̃` skew | `S.E` (not skew), `S.D`, `S.K i j = (E i j : ℚ) * D j`; `S.skew` is gone, replaced by the lemmas of §1.1 |
| exponent matrix | rows `S.B i j` | columns `[±E_{ji}]_+` | `S.B i j := S.E j i` (`S.B = S.Eᵀ`, `Seed.B_apply` by `rfl`) |
| `P_i^+` | `∏ j, a j ^ (B i j).toNat` = reference `P_i^-` (**interchanged**) | `∏_j z_j^{[E_{ji}]_+}` | `∏ j, a j ^ (E j i).toNat` = reference `P_i^+`, **no interchange** |
| carrier | reference variety of `B`, monomials swapped | `X_E` | `X_E` literally |
| `t_i` | `exchangeCharacter p i = 1/t_i` | `t_i = P_i^+/P_i^- = z^{c_i}`, `c_i = E e_i` | `exchangeCharacter p i = t_i` (docstring corrected in the accepted source: **D1 closed**) |
| node partner `y` | `normalizedPartner = y/t_i` | `y = z_i'/P_i^-` | `normalizedPartner = y` |
| node equation | `x·(y t) = 1 + 1/t` (reciprocal node) | `x y = 1 + t` | `NodeCoordinates.normalized_node_equation`, the reference node |
| `v_i` | `rowLog = ∑_j B_{ij} u_j = -v_i` | `v_i = log\|t_i\| = c_i(u) = ∑_j E_{ji} u_j` | `rowLog = +v_i` (text unchanged, meaning flipped) |
| `η_i - π` | `arg(-exchangeCharacter) = -(η_i-π)`, `nodeLog = -Log(-t_i)` | `η_i = arg t_i = c_i(θ)`, `Log(-t_i) = v_i + i(η_i-π)` | `angle = +(η_i-π)`, `nodeLog = +Log(-t_i)` |
| `dη_i` | `tau = -dη_i` | `c_i(dθ) = dη_i` | `PrimitiveResidual.tau = +dη_i` (proved: `tau_eq_nodeAngle_differential`) |
| form coefficient | `(S.B i j : ℂ)`, `= K_{ij}` since `B` skew | `Ω_T = ½ ∑_{j,l} K_{jl} dlog z_j ∧ dlog z_l` | `(S.K i j : ℂ)` / `(S.K i j : ℝ)` at every form site: `SmoothPresentation.logarithmicImaginaryValue`, `GlobalTwoForm.matrixForm`, `TorusNondegeneracy.complexMatrix`, `NodeTwoForm.outsideBlock`, `TorusPrimitive.beta`, `PrimitiveResidual.residual`. **No form site holds `S.B`** |
| form sign | `= +Im Ω` | `ω\|_T = im Ω_T` | `= +Im Ω` (`matrixForm_real`, `localForm_torus`) |
| form determinant | `det B = 1` | `det K = det E ∏ d_i = ∏ d_i > 0` | `Seed.det_K_of_unimodular`, `SeedAlgebra.det_Kreal_of_unimodular`, `isUnit_det_Kreal`, `TorusNondegeneracy.complexMatrix_det`; only `IsUnit` is ever used |
| node coefficient | `+(rawParameters …)⁻¹ • wedge du dv` | `Ω = ∑_{i∈I} d_i dlog t_i ∧ dlog x_i + Ω_0` | `-(S.D i : ℂ) * (rawParameters S I x (Sum.inl i))⁻¹`; the flip is forced by `K_{ij} = -d_i B_{ij}` |
| node residual block | `Tᵀ B_J T`, integral | `Ω_0`, constant coefficients | `NodeTwoForm.residualMatrix = Tᵀ K_J T`, **rational**; `T` unchanged and integral |
| node normal form | `[[0,-P,0],[P,A,B_0],[0,-B_0ᵀ,C]]`, `P` the unweighted row projection | `[[0,-D_I,0],[D_I,A,B_0],[0,-B_0ᵀ,C]]` | `NodeNondegeneracy.normalMatrix` with `weightProjection i (Sum.inl i') = -(S.D i : ℂ) δ_{ii'}` — entry for entry |
| nondegeneracy domain | `∀ p : S.Point` | nondegenerate on `𝒜(B̃)` | `GlobalSymplectic.nondegenerate_omega (p : S.Point)`, `isSymplecticOn … Set.univ` — the whole space |
| `λ_tor` | `beta = ∑_{i,j} (B i j) u_i dθ_j` | `λ_tor = u^T K dθ` | `beta = ∑_{i,j} (S.K i j : ℝ) u_i dθ_j`; no `½`, no minus, `u` on the first index |
| `H` | `H_Lean = -H_ref`, no `d_i` | `H = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)` | `TorusCorrection.H` with `(S.D i : ℝ)` in every summand; **`H_Lean = +H_ref`** |
| primitive | `alpha = beta - dH_Lean = λ_ac` | `λ_ac = λ_tor + dH` | `alpha := beta + covectorForm (differentialCovector H)` — `+`, definitionally |
| per-index scalar / affine germ | `correction`, `affineCorrection`, unweighted | `h(u_i)χ_iρ(v_i)β(η_i)`, `(u_i+a)(η_i-π)` | unchanged and **unweighted**; every consumer supplies `(S.D j : ℝ)` |
| node primitive block | `lambda κ = +`(reference block) | `v dθ - u dη + d(hρβ)` | `lambda κ = -`(reference block); `block = ∑_{i∈I} (S.D i : ℝ) • lambda_i` |
| local primitive | `eta = residual + block - regularForm` | `λ_ac` near a node | `eta = residual - block + regularForm`; cross-checked by the proved `eta_eq_torus` |
| `eta` on `{y_i = 0}` | `residual - regularForm` | extension vanishes at `y_i = 0` | `eta_zero_partners : residual + regularForm` |
| radial flow | `u̇_i = u_i - hχρβ'` with `S.B`; `real_logarithmicComponents` inverts `B` using `det B = 1` | `eq:acyclic-flow`, `eq:acyclic-radial` | `mutable_radial_equation` / `frozen_radial_equation` **byte-unchanged**; `radial_matrix_equation` is `S.B ↦ S.K` at all three sites with the minus preserved; the inversion is of `Kreal` through `isUnit_det_Kreal` |
| angular flow | `∑_j (S.B i j)(…).im = +∂_{u_i}H` | `η̇_i = (1/d_i) ∂_{u_i} H` | `angular_equation`: `∑_j (S.K i j)(…).im = -∂_{u_i}H`; `angular_equation_row`: `d_i ∑_j (S.B i j)(…).im = +∂_{u_i}H` |
| `∂_θ H`, `∂_u H` | `differential_H_angular` / `_radial`, unweighted | `∂_θ H = K a` | both gain `(S.D i : ℝ)` per summand; `differential_H_angular_K` is the `K`-spelling with the leading minus; the exponent row stays `S.B` |
| `∂_{u_i} H` at a node | `local_H_radial = (nodeLog q i).im` | `∂_{u_i}H = d_i(η_i-π)` | `BoundaryTangency.local_H_radial = (S.D i : ℝ) * (nodeLog q i).im`; its consumer `nodeLog_drift_torus` is unchanged, the `d_i` cancelling against `angular_equation_row` |
| masked angular inverse | `nu = B⁻¹.mulVec angularRhs`, `det B = 1` | `θ̇ = -K^{-1}∂_u H`, `c_i(K^{-1}x) = -x_i/d_i` | `nu = (SeedAlgebra.Kreal S)⁻¹.mulVec (fun i => -angularRhs …)`; `isUnit_det_Kreal` only; `full_matrix_nu_equation`, `row_nu_equation` |
| uniform inverse bound | local `R`, `det R = 1`, one-norm calc block | — | `full_matrix_inverse_bound` stated with `S.K`, proved by `SeedAlgebra.exists_inverse_bound_Kreal` in one term |
| integer inverse | `S.B⁻¹`, `det B = 1` | `E^{-1}` restricts to a retraction; `c_i` extend to a basis | `S.B⁻¹ = (E⁻¹)ᵀ`, `Seed.B_det`, `SeedAlgebra.det_Breal`, `exists_inverse_bound_Breal` — unweighted, and now the literal blueprint statement |
| divisor and partner rates | `-2κ`, `2(1+κ)` | `-2a`, `2(1+a)` | **weight-free and byte-unchanged**: `ZeroStratumInvariance.normSq_drift`, `NormalizedPartnerNormDrift.normSq_drift_zero` |
| acyclicity | `WellFounded (0 < S.B i j)` | arrows `B_{ij} > 0` on `M` acyclic | field on `0 < S.E i j`; `Seed.acyclic_exponent` bridges to `0 < S.B i j` |
| `Unimodular` | `S.B.det = 1` | `E ∈ GL_n(ℤ)`, hence `det E = 1` | `S.E.det = 1` (+ `Seed.B_det` for the old consumers) |
| cutoffs, cap, strata, torus, trapped set | — | — | **unchanged in statement and meaning** (§1.8, §1.9) |
| parity of the cutoffs | load-bearing for the `H` sign | `ρ` even, `β` odd near `π` | not needed for the weighted statements; needed for §1.11 and still unstated: **R5** |

### 1.11 The `D = I` recovery

The old input is `SkewSeed d` (fields `B`, `mutable`, `skew`, `acyclic`) and its
weighted reading is

```lean
def SkewSeed.toSeed : Seed d where
  E := S.B;  mutable := S.mutable;  D := fun _ => 1;  …
```

so `E := B`, **not** `E := Bᵀ`. That choice is the only one of the two that
recovers the old theorem, and the reason is the form sign:

* `SkewSeed.toSeed_K : (S.toSeed).K i j = (S.B i j : ℚ)` — the weighted form
  coefficient at `D = 1` is *literally* the old integer matrix. Since the
  baseline's `logarithmicImaginaryValue` used `(S.B i j : ℂ)` with the
  reference's sign (§1.5 of the previous revision of this guide, and §1.10
  above), the weighted form at `D = 1, E := B` is pointwise the old form. No
  sign flip, hence no time reversal — and `trappedSet` is a *forward*-orbit
  condition, not invariant under time reversal, so `E := Bᵀ` (giving `K = -B`)
  would have destroyed exactly the clause the recovery is about.
* The price is that the two monomials swap
  (`SkewSeed.toSeed_positiveMonomial`), which costs nothing because the exchange
  equation uses only their sum (`SkewSeed.toSeed_monomial_sum`): the carriers are
  the same subset of the ambient space (`SkewSeed.carrier_set_eq`) and the
  canonical identity map is a homeomorphism `SkewSeed.pointHomeomorph` with
  `SkewSeed.pointHomeomorph_val` by `rfl`. Hence every predicate of the target
  phrased in ambient coordinates — `initialTorus`, `coordinateCap`,
  `lambdaStratum` and relative compactness of forward orbits — transports
  verbatim, and `SkewSeed.toSeed_independent_iff`, `SkewSeed.toSeed_unimodular_iff`
  are `Iff.rfl`.

**What is pointwise equal, and what is not.** At `D = 1`, `beta` is **equal** to
the baseline's, `H` is **exactly negated**, and `alpha` is therefore **equal** —
not merely equal up to an exact form. The negation of `H` is where the cutoff
parities are genuinely used: `rho` is even and `rowLog` flips sign, `vartheta δ`
is odd and `arg(-exchangeCharacter)` flips sign, and `exchangeCharacter` inverts.
This is the stage-B review's item 7, and it means the recovery can claim more
than the bare existential: by uniqueness of the Liouville vector
(`LiouvilleData.field_eq_liouvilleVector`) the field, the flow and hence the
trapped set are the baseline's. What is **not** available is a Lean term equality
of `Form 1`: the two libraries' atlases differ (the baseline's node coordinates
were `(z_i, z_i'/P_i^+, 1/t_i)`, the weighted ones are the reference's
`(z_i, z_i'/P_i^-, t_i)`), so `Tangent p` is not literally the same type.
Finding **R7**.

**The statement, in the reviews' (a)+(b)+(c) shape.** Clauses (b) and (c) are
delivered in `ClusterSkeleton/SkewSeedRecovery.lean` at commit
`e7a6d9637ac0acec71639a71731f1d6ca27e2e0c` (branch `weighted/recovery-scaffold`;
the module is **not** in the tree at `114d639`), documented in
the proved recovery in `SkewSeedRecovery.lean` and `SkewSeedSkeleton.lean`:

| clause | content | status |
| --- | --- | --- |
| (a) | `LiouvilleSkeletonTarget S.toSeed` from `FullSkeleton.liouvilleSkeletonTarget` and `SkewSeed.toSeed_unimodular` | delivered as `SkewSeed.liouvilleSkeletonTarget` in the accepted source, and an audit root |
| (b) | `SkewSeed.torus_anchor_old_matrix`: `logarithmicImaginaryValue` written with the old integer `S.B` — the clause that certifies "no sign flip" | delivered at `e7a6d96` |
| (c) | the old loci on the old carrier `SkewSeed.initialTorus`, `SkewSeed.coordinateCap`, `SkewSeed.lambdaStratum`; their membership, preimage and image identifications (`mem_*_iff`, `preimage_*`, `image_*`); `SkewSeed.coordinateCap_eq_iUnion_lambdaStratum`, `isCompact_lambdaStratum`, `isCompact_coordinateCap`; the flow conjugation `SkewSeed.conjFlow`, `conjFlow_apply`, `pointHomeomorph_conjFlow`, `forwardOrbit_conjFlow` (+ preimage and image forms), `trappedSet_conjFlow`, `image_trappedSet_conjFlow`, and `trappedSet_conjFlow_eq_coordinateCap` | delivered at `e7a6d96` |

**Checked here.** The whole module `ClusterSkeleton/SkewSeedRecovery.lean` as it
stands at `e7a6d96` was re-elaborated unchanged, as a scratch file at the
repository root, against the weighted tree at `114d639`: it compiles with no
error, so clauses (b) and (c) are statements about the delivered weighted
library, not about the stage-A tree they were written on. In the same scratch
file, the two compositions that close the recovery were elaborated:

```lean
-- (a)
example (hdet : S.Unimodular) : LiouvilleSkeletonTarget S.toSeed :=
  FullSkeleton.liouvilleSkeletonTarget S.toSeed (S.toSeed_unimodular hdet)

-- (a) + (c): the old stratified skeleton identity, on the OLD carrier
example (hdet : S.Unimodular) :
    ∃ Φ : Flow ℝ S.Point,
      trappedSet Φ = SkewSeed.coordinateCap S ∧
      trappedSet Φ =
        ⋃ I : {I : Finset (Fin d) // S.Independent I}, SkewSeed.lambdaStratum S I.val := by
  obtain ⟨-, P, L, -, hcap⟩ :=
    FullSkeleton.liouvilleSkeletonTarget S.toSeed (S.toSeed_unimodular hdet)
  refine ⟨SkewSeed.conjFlow S L.completeFlow.flow, ?_, ?_⟩
  · exact SkewSeed.trappedSet_conjFlow_eq_coordinateCap S _ hcap
  · rw [SkewSeed.trappedSet_conjFlow_eq_coordinateCap S _ hcap,
      SkewSeed.coordinateCap_eq_iUnion_lambdaStratum S]

-- (b) + the weighted torus anchor: on the recovered torus, d(primitive) is the OLD form
example … : evalTwo (exteriorDerivative (FullSkeleton.liouvilleData S.toSeed … ).primitive) p v w =
    (½ ∑ i ∑ j (S.B i j : ℂ) * (…)).im := by
  rw [FullSkeleton.torus_anchor S.toSeed … p hp]
  exact SkewSeed.torus_anchor_old_matrix S _ p v w
```

All three elaborate. So the recovery closes with **no mathematical gap**.

**The packaged statement in the accepted source.** The module
`ClusterSkeleton/SkewSeedSkeleton.lean` (namespace `ClusterSkeleton.SkewSeed`) is
part of the accepted source commit
`a575aa236b485672f0606bba6ebc80571671f8a9`, together with
`ClusterSkeleton/SkewSeedRecovery.lean` and the import of
`ClusterSkeleton.SkewSeedRecovery` and `ClusterSkeleton.SkewSeedSkeleton` into
`ClusterSkeleton.lean`. Every declaration below is an audit root of the
receipt:

| declaration | content |
| --- | --- |
| `SkewSeedSkeleton.liouvilleSkeletonTarget` | clause (a): `LiouvilleSkeletonTarget S.toSeed` |
| `SkewSeedSkeleton.dense_initialTorus` | density of the **old** initial torus |
| `SkewSeedSkeleton.liouvilleData_torus_anchor_old_matrix` | clause (b) for the constructed datum: `d(primitive)` on the recovered torus, written with the old integer `S.B` |
| `SkewSeedSkeleton.liouvilleData_trappedSet_conjFlow`, `liouvilleData_trappedSet_conjFlow_iUnion` | the old skeleton identity and its stratified form on the **old** carrier |
| `SkewSeedSkeleton.skeleton_recovery_of_parameters`, `SkewSeedSkeleton.skeleton_recovery` | the packaged recovery statement, the second at `ε = 1, κ = 3, δ = 1` |

`skeleton_recovery` reads: for every `SkewSeed d` with `S.Unimodular` — the old
library's hypothesis and the only hypothesis — the old initial torus is dense,
and there exist a smooth presentation of the exchange space and a Liouville datum
on it whose anchored two-form is `Im(½ ∑_{i,j} (S.B i j : ℂ) dlog a_i ∧ dlog a_j)`
(the **old integer** matrix) and whose complete flow, read on the old carrier
along `pointHomeomorph`, has exactly `C_B = ⋃_I Λ_I` as its dynamical skeleton.
Its docstring states that the smooth structure is existential and that no
transported smooth structure and no term identity with the baseline's constructed
flow is claimed — i.e. the route decided in
the proved recovery in `SkewSeedRecovery.lean` and `SkewSeedSkeleton.lean` §2 and the constraint of
**R7**.

**Checked here.** `SkewSeedRecovery.lean` concatenated with
`SkewSeedSkeleton.lean`, elaborated as a scratch file: no error, no `sorry`. In
the accepted source both modules are built as part of
`lake build ClusterSkeleton` and every statement listed above is reported by the
axiom audit with exactly `propext`, `Classical.choice`, `Quot.sound`.

**The recorded smooth-structure decision.** Recovery is stated directly for
`S.toSeed`, with the old loci and the old trapped set transported along
`pointHomeomorph` as *topological* objects. **No transported smooth structure is
claimed**, and no `SkewSeed.transportPresentation` is delivered. The reason,
recorded in the proved recovery in `SkewSeedRecovery.lean` and `SkewSeedSkeleton.lean` §2: Mathlib
supplies the charted-space push-forward along a local homeomorphism but no
`IsManifold`/`HasGroupoid` transport for it, so the `smooth` field of
`SmoothPresentation` would need a from-scratch groupoid-compatibility proof for
the conjugated atlas plus transports of `inclusion_smooth` and
`inclusion_immersion` — a separate construction, not a corollary of
`pointHomeomorph_val = rfl`. It is also not needed: what
`tex/target-theorem.tex` §5 pins is "the exchange space, the sign of the form,
and the same-flow skeleton identity", and (b) pins the form sign, (c) the
exchange space and the skeleton set, and (a) supplies the existential smooth
structure exactly as the PDF quantifies it. Correspondingly, **the old smooth
structure must not be claimed anywhere**, and term identity of the recovered flow
with the baseline's constructed flow is not claimed either.

---

## 2. Step table

`hdet : S.Unimodular`, `hε : 0 < ε`, `hκ : 2*ε+1 ≤ κ`, `hδ : 0 < δ` are the
standing Lean hypotheses — unchanged from the baseline, and **no hypothesis was
added anywhere for the weighted case**. "At least as strong" is judged in the
weighted scope of this audit. Steps are the steps of
`tex/proof-blueprint.tex`.

| # | Reference step | Lean declaration(s) (`File.name`) | Status in the weighted scope |
| --- | --- | --- | --- |
| 0 | Weighted input: `E ∈ GL_n(ℤ)` not skew, `D̃` positive rational, `K = E D̃` skew, mutable block acyclic; "Positivity of the `d_i` implies `E_{ii}=0` and `E_{ij}=0 ⟺ E_{ji}=0`" | `Seed`, `Seed.K`, `Seed.K_transpose`, `Seed.K_skew`, `Seed.E_diag_zero`, `Seed.E_pos_iff_neg`, `Seed.E_eq_zero_iff`, `Seed.acyclic_exponent`, `Seed.wellFounded_iff_no_directed_cycle`, `Seed.det_K`, `Seed.det_K_of_unimodular`, `Seed.isUnit_det_K`, `Seed.B_det`; field-level `SymmetrizerAlgebra.K`, `SymmetrizerAlgebra.K_transpose`, `SymmetrizerAlgebra.det_K`, `SymmetrizerAlgebra.E_diag_zero`, `SymmetrizerAlgebra.E_eq_zero_iff`, `SymmetrizerAlgebra.E_pos_iff_neg` | present; §1.1. The sign facts are **proved from `D_pos`**, not assumed, and are strictly more general than the baseline's `skew` field |
| 1 | Lemma (i): `{i ∈ M : z_i(p)=0}` is independent (acyclic maximal-path argument) | `ZeroSet.Seed.Point.outgoing_ne_zero`, `ZeroSet.Seed.Point.matrix_eq_zero_of_coordinates_zero`, `ZeroSet.Seed.Point.zeroSet_independent` | present; **stronger**: proved by `S.acyclic_exponent.induction` for arbitrary multiplicities, without unimodularity, and includes the diagonal. The hypothesis `0 < S.B i j` is now the reference's own `B_{ji} > 0 ⇒ P_i^+(p) = 0` (§1.2); see **D2** for the stale name |
| 2 | Lemma (ii): `U_I ≅ 𝒩^I × (ℂ*)^{m+f-2\|I\|}` with `(x,y,t) = (z_i, z_i'/P_i^-, t_i)` | `CoordinateLoci.candidateChartLocus`, `isOpen_candidateChartLocus`; `NodeCoordinates.normalized_node_equation`, `NodeCoordinates.independent_rows_inverse_pairing`, `NodeCoordinates.independent_rows_linearIndependent`; `IntegralBasisCompletion.SplitIntegerRows.splittingEquiv`; `IndependentNodeChart.forward`, `backward`, `homeomorph`; `IndependentNodeSmooth.basis_cardinality`, `complementRank_eq_sub_two_mul_card`, `two_mul_card_le`, `modelEquiv`; `IndependentLaurentCoordinates.independentRowLaurentHomeomorph`; `LaurentCoordinates.monomialHomeomorph` | present, and now in the reference's **own** node coordinates rather than the reciprocal ones (§1.3). `complementRank_eq_sub_two_mul_card` makes the exponent literal: gap **G2**. Its input `independent_rows_inverse_pairing` is now the blueprint sentence exactly — the rows of `S.B = S.Eᵀ` indexed by `I` are the columns `c_i = E e_i`, and `S.B⁻¹ = (E⁻¹)ᵀ` is "the integer inverse of `E` restricts to a retraction". The ring-theoretic part (`𝒪(U_I)` presentation) is deliberately absent: **N2** |
| 3 | Lemma (iii): the `U_I` cover `𝒜(B̃)` | `ZeroSet.Seed.Point.exists_independent_nonvanishing_locus`, `CoordinateLoci.exists_independent_candidateChartLocus`, `CoordinateLoci.iUnion_independent_candidateChartLocus`, `NodeNondegeneracy.zeroSet_chart_mem` | present; equal strength |
| 4 | Exchange model `𝒜(B̃) = ℂ[z,z',z_F^{±1}]/(z_iz_i'-P_i^+-P_i^-)` (BFZ III, Cor. 1.21) | no counterpart (by design): `Seed.Point` is the actual complex point set with inherited topology; `CapSet.isClosed_ambientCap`, `FiniteTimeConfinement.CoordinateBounds.isCompact_coordinateBox` supply the only consequences used | **N2**: no Lean change needed |
| 5 | Smooth atlas on the actual variety; "The node charts are smooth, and their coordinate maps are the actual exchange coordinates" | `SmoothAtlas.rawChart`, `chart`, `contDiffOn_transition`, `smooth`, `inclusion_smooth`, `inclusion_immersion`, `presentation`; `GeometryNativeBridge.SmoothPresentation.inclusion_isDiffImmersionAt`; `InitialTorusDensity.dense_initialTorus` | present and **stronger** than the reference's remark: the inclusion is proved smooth and immersive, not assumed. Unaffected by the weights (the atlas is built from the integral `E` through `IntegralBasisCompletion`) |
| 6 | `Ω = ½∑K_{jl} dlog z_j ∧ dlog z_l`; the weighted node form `∑_{i∈I} d_i dlog t_i ∧ dlog x_i + Ω_0`, the row `∑_j K_{ij} dlog z_j = -d_i dlog t_i`, the block matrix `[[0,-D_I,0],[D_I,A,B_0],[0,-B_0ᵀ,C]]` and nondegeneracy "using `d_i ≠ 0` and nonsingularity of `C`" | `GeometryTarget.SmoothPresentation.logarithmicImaginaryValue`; `GlobalTwoForm.matrixForm`, `matrixForm_apply`, `omega`, `omega_eq_localForm`, `omega_torus`, `exteriorDerivative_omega`; `TorusPrimitive.matrixForm_real`; `TorusNondegeneracy.complexMatrix`, `complexMatrix_det`, `isUnit_complexMatrix_det`; `NodeTwoForm.complexForm`, `complexForm_torus`, `complexForm_boundary`, `localForm`, `localForm_torus`, `outsideBlock`, `residualMatrix`, `row_outsideLog_weighted`; `NodeNondegeneracy.weightProjection`, `normalMatrix`, `normalMatrix_skew`, `complexResidual_skew`, `residualBlock_normalMatrix`, `normalMatrix_injective`, `isUnit_det_normalMatrix`, `complementMatrix_kernel`, `complementMatrix_isUnit`, `complexForm_boundary_nondegenerate`, `localForm_boundary_nondegenerate`, `zeroSet_localForm_nondegenerate`; `SymmetrizerAlgebra.residualBlock_eq_zero_of_mulVec_eq_zero`, `isUnit_det_residualBlock`; `LocalFormGluing.existsUnique_smooth_gluing`; `GlobalSymplectic.nondegenerate_omega`, `isSymplecticOn_omega`; `FormExtensionUniqueness.smoothAtlas_twoForm_extension_unique` | present as a **real** smooth closed nondegenerate extension of `Im Ω` with the **weighted** coefficient, unique by torus density, nondegenerate at every point (§1.5). The reference's holomorphic `Ω` itself is not constructed: **N3**. The blueprint's normal-form argument is implemented block for block, with `d_i ≠ 0` from `Seed.D_pos` replacing `det B = 1` |
| 7 | `λ_tor = u^T K dθ` | `TorusPrimitive.angleCovector`, `beta`, `evalOne_beta`, `alpha`, `evalOne_alpha`, `matrixForm_real`, `exteriorDerivative_beta`; `TorusCorrection.alpha`, `evalOne_alpha`, `exteriorDerivative_alpha` | present with the weighted coefficient and the reference's sign and index placement (§1.5) |
| 8 | Split of `λ_tor` over an independent `I` (`eq:acyclic-ltor-split`), with the factor `d_i` on the `I`-block | `PrimitiveResidual.split_sum`, `beta_decomposition`, `residual`, `tau`, `tau_eq_nodeAngle_differential`, `logRow`, `node_argument`, `sum_K_row_real`; `NativeNodePrimitive.lambda_torus`, `block_torus` | present and literal (§1.6): the `I`-block is `∑_{i∈I} d_i(v_i dθ_i - u_i dη_i)`, the complementary block carries `K`, and `tau = +dη_i` is proved rather than read |
| 9 | `χ_i`; `H = ∑_{i∈M} d_i h(u_i)χ_iρ(v_i)β(η_i)`; `λ_ac = λ_tor + dH` | `DominanceCutoff.dominance`, `mutableNeighbors`, `adjacent_exclusion`; `TorusCorrection.A`, `rowLog`, `angular`, `H`, `manuscript_formula`, `contMDiffOn_H`, `alpha`; `TorusLiouvilleDynamics.amplitude`, `logarithmicHamiltonian`, `H_logarithmic_identity`, `fderiv_logarithmicHamiltonian`, `differential_H`, `differential_H_angular`, `differential_H_angular_K`, `differential_H_radial`; `RegularCorrection.H_eq_sum` | present with `(S.D i : ℝ)` in every summand, `H_Lean = +H_ref` and `alpha = beta + dH = λ_ac` (§1.6). `differential_H`, `differential_H_angular`, `differential_H_radial`, `logarithmicHamiltonian`, `fderiv_logarithmicHamiltonian` and `AllStrataGrowth.angularRhs_center` are the statements that gained the weight |
| 10 | Near-divisor form of `H` (`eq:acyclic-H-near`) and smooth extension of `λ_ac` over `W` | `PrimitiveLocalization.region`, `region_mem_nhds`, `neighborhood`, `plateaus`, `adjacent_dominance_zero`, `correction`, `affineCorrection`, `correction_eq_affine`, `correction_eventuallyEq`, `correction_mfderiv_eq`, `rowLog_eq_log_re`, `neg_character_node`; `RegularCorrection.surviving`, `regularH`, `singularH`, `H_split`, `H_eventuallyEq`, `regularForm`, `regularForm_smooth`, `literal_formula`; `NodePrimitiveCancellation.lambda`, `cancellation`, `cancellation_oneForm`, `lambda_zero`, `numerical_sign`; `NodeLogExtension.nodeLogQuotient`, `nodeLogQuotient_zero`, `analyticOnNhd_nodeLogQuotient`, `contDiffAt_nodeLogQuotient_zero`; `NativeNodePrimitive.nodeMap`, `node_real_logRow`, `locus`, `lambda`, `block`, `lambda_boundary`, `contDiffAt_block_inChart`; `LocalPrimitive.eta`, `locallySmooth_eta`, `differential_H_eq_sum`, `singularH_eq_sum`, `eta_eq_torus`, `eta_zero_partners`, `local_cover`, `agree_on_torus`, `covers`; `GlobalPrimitive.alpha`, `alpha_eq_eta`, `isSmoothForm_alpha`, `alpha_eq_torus`, `eq_alpha_of_torus`, `exteriorDerivative_alpha`, `nondegenerate_exteriorDerivative_alpha`, `isSymplecticOn_exteriorDerivative_alpha`, `exists_global_primitive` | present; the weight sits on the whole per-node block (`block`), the per-index scalars staying unweighted, and the three signs `alpha`/`eta`/`eta_zero_partners` moved together (§1.6). `eta_eq_torus` is the internal cross-check. `GlobalPrimitive.exists_global_primitive` is existential in the form, so the near-node shape must be consumed through `alpha_eq_eta`: **R6** |
| 11 | Flow equations `eq:acyclic-flow`, `eq:acyclic-angle-flow` for `u`, `θ`, `η`, `v`; `K^T u̇ = K^T u + ∂_θ H`, `-K θ̇ = ∂_u H` | `TorusLiouvilleDynamics.Z`, `contraction`, `omega_real`, `radialTangent`, `angularTangent`, `logarithmicComponents`, `angular_equation`, `angular_equation_row`, `radial_matrix_equation`, `real_logarithmicComponents`, `radialCorrection`, `mutable_radial_equation`, `frozen_radial_equation`, `angular_equation_logarithmic`, `angular_equation_partial_deriv`; `GlobalLiouvilleField.Z`, `contraction_exteriorDerivative`, `Z_eq_torus`, `logarithmicComponents`, `L`, `L_eq_logarithmicComponents`, `mutable_radial_equation`, `frozen_radial_equation`, `frozen_radial_equation_torus`, `angular_equation_partial_deriv`, `L_eq_A_of_collar`, `L_eq_A_of_nonneg`, `L_negative_bound`; `LocalAngularDynamics.angularRhs`, `nu`, `angularRhs_eq_radial`, `nu_eq_torus`, `nu_eq_logarithmicComponents`, `nu_smooth`, `coordinate_drift`, `partner_drift`; `AllStrataGrowth.full_matrix_nu_equation`, `row_nu_equation`; `SeedAlgebra.sum_K_row`, `sum_K_col`, `K_mulVec_single`, `c_inv_K`, `Breal_mulVec_inv_K`, `Kreal_mulVec_eq_iff` | present; the weights cancel from the radial equations (which are byte-unchanged) and survive in the angular equation as `1/d_i` (§1.7). Lean proves them for the **glued global** field and extends off the torus by density, which the reference does only pointwise on `W` |
| 12 | Radial bound `\|u̇_j\| ≤ C(1+\|u_j\|)`, `C = (1+max\|β'\|)(1+L)`, and `u̇_i ≤ u_i - h(u_i)` on `{u_i<0}` | `PrimitiveCutoffs.radial_abs_le`, `radial_linear_growth`; `TorusLiouvilleDynamics.amplitude_abs_le`, `real_components_growth`, `imaginary_components_growth`, `full_matrix_inverse_bound`, `dominance_partial_bound`, `amplitude_partial_bound`, `logarithmic_linear_growth`; `GlobalLiouvilleField.logarithmic_linear_growth`, `L_negative_bound`; `NativeRadialOrbit.amplitude_abs_le_radial`, `uniform_radial_error_bound`, `L_eq_A_sub_radial_mul_c`; `AllStrataGrowth.R`, `radial_growth`, `uniform_growth`, `integralCurve_growth`, `angularRhs_center`, `angularRhs_center_bound`, `nu_center_growth`, `partner_drift_growth`; `ScalarOrbitDynamics.RadialEquation`, `radial_velocity_le`, `radial_affine_bound`, `radial_antitone`, `radial_tendsto_atBot`, `radial_eq_exp_of_nonneg` | present; **stronger**: one constant bounds radial *and* angular components *and* the partner drift, uniformly over all zero strata. The only weighted change is that the angular half now goes through `S.K` and `SeedAlgebra.exists_inverse_bound_Kreal` instead of a `det = 1` block, and `angularRhs_center` carries `(S.D i : ℝ)` |
| 13 | Divisor flow `Z\|z_i\|² = -2a\|z_i\|²`, `ṫ_i = t_i Log(-t_i)`, invariance of `{z_i=0}` (`eq:acyclic-divisor-flow`) | `BoundaryTangency.deep_radius_torus`, `deep_radius`, `local_H_radial`, `nodeLog_drift_torus`, `nodeLog_drift`, `nodeProduct_drift`, `zero_coordinate_tangent`, `coordinate_tangent`, `row_real_drift_torus`; `ZeroStratumInvariance.normSq_drift`, `normSq_hasDerivWithinAt`, `coordinate_zero_iff`, `zeroSet_eq`, `coordinate_ne_zero_iff` | present with `a = κ`; **stronger**: zero/nonzero persistence is proved in **both** time directions on an arbitrary preconnected domain. `local_H_radial` is the one statement that gained `(S.D i : ℝ)`; its consumer `nodeLog_drift_torus` is unchanged because that weight cancels against `angular_equation_row`, so `ṫ_i = t_i Log(-t_i)` and `Z\|z_i\|² = -2κ\|z_i\|²` are **weight-free**, exactly as the blueprint has them |
| 14 | Partner flow `Z\|y_i\|² = 2(1+a)\|y_i\|²` on `{z_i=0}` and the general `Z log\|y_i\| = Re φ(t_i)+a` (`eq:acyclic-partner-flow`) | `NormalizedPartnerNormDrift.partner_smooth`, `differential_partner`, `quotient_smooth`, `partner_drift_of_ne_zero`, `normSq_drift_of_ne_zero`, `normSq_drift`, `normSq_drift_zero`, `normSq_hasDerivWithinAt`, `normSq_hasDerivWithinAt_zero`; `ZeroStratumPartnerDynamics.exp_law_of_hasDerivWithinAt`, `normSq_eq_exp_mul`, `partner_zero_iff`, `partner_ne_zero_iff`, `strictMonoOn_normSq` | present with `a = κ`, **weight-free and byte-unchanged**; **stronger**: the exponential law holds on arbitrary preconnected time sets in both directions |
| 15 | Completeness of `Z` (a maximal curve with finite `τ_±` leaves every compact set) | `FiniteTimeConfinement.radial_component_bound`, `normalizedPartner_norm_le`, `logarithmic_component_bound`, `fixed_mask_log_bound`, `uniform_original_bounds`, `finite_time_compact_confinement`, `bounded_horizon_closure`, `CoordinateBounds.coordinateBox`, `CoordinateBounds.isCompact_coordinateBox`; `NativeCompleteFlow.exists_global_integralCurve`, `exists_completeLiouvilleFlow`, `completeFlow`, `exists_extension_Ioo` | present and **byte-unchanged**; **stronger**/different route: finite-horizon confinement into a precomputed compact set plus a uniform local lifetime yields a genuine two-sided `Flow` with joint smoothness: **N5** |
| 16 | Inclusion (i) `Skel(Z) ⊂ ⋃_I Λ_I` | `ScalarOrbitDynamics.frozen_log_orbit`, `trapped_frozen_norm_eq_one`; `NativeRadialOrbit.radialEquation`, `negative_log_laws`, `nonnegative_log_law`, `positive_log_law`, `original_norm_le_one_of_mem_trappedSet`, `frozen_norm_eq_one_of_mem_trappedSet`, `trapped_radial_restrictions`; `CompactInteriorRigidity.row_single`, `amplitude_single_deep`, `characterCoefficient_eq_one_deep`, `sin_mul_vartheta_nonneg`, `angular_scalar_eq_neg_one_of_tendsto`, `angular_scalar_eq_neg_one_backward`, `interior_norm_tendsto_zero`, `interior_matrix_eq_zero`, `negativeMonomial_norm_eq_one`, `character_eq_neg_one_initial`, `initial_partners_zero`, `compactInteriorRigidityTarget`; `ZeroStratumEscape.compact_zero_slice_bound`, `partner_eq_zero_of_mem_trappedSet`, `not_mem_trappedSet`; `ConstructedFlowReverseInclusion.trappedSet_subset_coordinateCap`, `constructedFlowReverseInclusionTarget` | present, conclusion stated as `⊆ coordinateCap`; independence of the limiting index set is `CapIndependence.coordinateCap_strictCapIndices_independent` / `CompactInteriorRigidity.interior_matrix_eq_zero`, and the set-level reconciliation with `⋃_I Λ_I` is `CapStrata.coordinateCap_eq_iUnion_lambdaStratum` (**G1**). Every **statement** in this row is unchanged from the baseline (verified declaration by declaration, §2.1): the weighted work here was proof-only, where `S.skew` became `Seed.B_eq_zero_iff`/`B_diag_zero` and `simp` had to be replaced by `show`/`unfold` at the `S.B i j` ⟷ `S.E j i` transparency boundary. The angular rigidity route differs from the reference's monotonicity argument: **N6** |
| 17 | Inclusion (ii) `Λ_I ⊂ Skel(Z)` (`Λ_I` compact and forward invariant) | `CapSet.coordinateCap`, `coordinateCap_norm_a_le`, `coordinateCap_b_eq_zero`, `coordinateCap_norm_b_le`, `isCompact_coordinateCap`; `CapIndependence.coordinateCap_outgoing_not_interior`, `coordinateCap_strictCapIndices_independent`, `norm_eq_one_of_not_strict`; `CapAngularTangency.norm_eq_one_of_not_strict`, `normalizedPartner_eq_zero_of_interior`, `exchangeCharacter_eq_neg_one_of_interior`, `angular_eq_zero_of_interior`, `radial_and_deriv_zero`, `nu_eq_zero`, `coordinate_drift_eq_zero_of_unit`; `InteriorPartnerPropagation.unit_norm_forward`, `neighbors_unit_forward`, `angularRhs_eq_self_of_unit_neighbors`, `differential_character_of_unit_neighbors`, `character_eq_neg_one_forward`, `propagate`, `interiorPartnerPropagationTarget`; `CapForwardInvariance.zero_forward`, `interior_forward`, `mutable_constraints_forward`, `frozen_norm_forward`, `forward`, `coordinateCapForwardInvarianceTarget`; `TrappedSet.trappedSet`, `mem_trappedSet_of_forwardOrbit_subset`, `subset_trappedSet_of_isCompact_forwardInvariant`; `ConstructedFlowCapInclusion.integralCurveOn`, `forward`, `isForwardInvariant`, `subset_trappedSet`, `isCompact_forwardOrbit_closure`, `constructedFlowCapInclusionTarget` | present; **stronger**: compactness and forward invariance are proved for the whole cap at once (hence for the whole union, by `CapStrata.coordinateCap_eq_iUnion_lambdaStratum`; per-stratum compactness is `CapStrata.isCompact_lambdaStratum`), and the trapped set is defined purely dynamically. `angularRhs_eq_self_of_unit_neighbors` gained `(S.D i : ℝ)`; its consumer `differential_character_of_unit_neighbors` is unchanged, the weight cancelling through `row_nu_equation` |
| 18 | Theorem `thm:acyclic-skeleton`: a Liouville form of `Im Ω` with `Skel = ⋃_I Λ_I`, for **every** weighted input | `GeometryTarget.SmoothPresentation`, `LiouvilleData`, `LiouvilleSkeletonTarget`, `FirstGeometricTarget`; `InitialTorusDensity.dense_initialTorus`; `FullSkeleton.trappedSet_eq_coordinateCap`, `trappedSet_eq_iUnion_lambdaStratum`, `liouvilleData`, `liouvilleData_flow`, `torus_anchor`, `liouvilleData_trappedSet`, `liouvilleSkeletonTarget_of_parameters`, `liouvilleSkeletonTarget`, `firstGeometricTarget` | present as `trappedSet completeFlow.flow = coordinateCap S` for the same constructed flow, with `ε = 1, κ = 3, δ = 1`, and in the stratified form of `eq:acyclic-skeleton`. `FullSkeleton.lean` is **byte-unchanged** from the baseline: the quantifier is now over an arbitrary weighted `Seed d` with `S.Unimodular` as the only hypothesis |
| 19 | `tex/target-theorem.tex` §4: the explicit non-skew input, and recovery of the `D̃ = I` specialization | `Examples.nonSkewSeed`, `nonSkewSeed_unimodular`, `nonSkewSeed_not_skew`, `nonSkewSeed_entries`, `nonSkewSeed_weights_ne`, `nonSkewSeed_K_transpose`, `nonSkewSeed_det_K`; `Examples.a2Seed`, `a2Seed_unimodular`, `a2Seed_D_eq_one`, `a2Seed_K_eq`; `SkewSeed`, `SkewSeed.toSeed`, `toSeed_K`, `toSeed_positiveMonomial`, `toSeed_monomial_sum`, `carrier_set_eq`, `pointHomeomorph`, `pointHomeomorph_val`, `toSeed_independent_iff`, `toSeed_unimodular_iff`; at `e7a6d96`: `SkewSeedRecovery`'s clauses (b) and (c) (§1.11) | the inputs and the recovery scaffolding are present and all hypothesis facts are **proved**; the two consumer lines — the `nonSkewSeed` instantiation and recovery clause (a) — typecheck at `114d639` and are **declarations in the accepted source** as `Examples.nonSkewSeed_target_of_firstGeometricTarget` and `SkewSeed.liouvilleSkeletonTarget`, both audit roots: **R4** and §1.11 |

### 2.1 Which statements actually changed shape

Mechanically determined for this guide by comparing every declaration header
(name, binders and type, up to the `:=`) between `e62c101` and `114d639`, module
by module. The result is the complete list; **every other statement in the
library is unchanged, and no declaration anywhere lost or gained a hypothesis.**

| module | statements whose type changed | added |
| --- | --- | --- |
| `Seed` | the structure `Seed` itself (fields `B, skew` → `E, D, D_pos, skewSymmetrizable`) | 32, including `B`/`Bexp`/`B_apply`, `K`/`K_apply`/`K_transpose`/`K_skew`, the sign lemmas `E_diag_zero`, `E_pos_iff_neg`, `E_eq_zero_iff` (+ `B`-spellings), `K_eq_neg_D_mul_B`, `sum_K_row_eq`, `B_det`, `det_K`, `det_K_of_unimodular`, `isUnit_det_K`, `positiveMonomial_eq_prod_B`, `negativeMonomial_eq_prod_B`, `Independent.exponent_eq_zero`, `acyclic_exponent` |
| `ZeroSet` | `matrix_eq_zero_of_coordinates_zero` (conclusion `S.B i j = 0` → `S.E i j = 0`, interderivable by `Seed.E_eq_zero_iff`) | — |
| `NodeCoordinates` | `exchangeCharacter_eq_zpow_product` (`∏ a_j^{S.B i j}` → `∏ a_j^{S.E j i}`, `rfl`-level) | — |
| `CapIndependence` | — | `norm_eq_one_of_not_strict` (a flow-module-free alias of the `CapAngularTangency` lemma) |
| `SymmetrizerAlgebra`, `SeedAlgebra` | — (new modules) | the whole weighted linear algebra of §1.7 |
| `TorusLiouvilleDynamics` | `omega_real`, `angular_equation`, `radial_matrix_equation`, `angular_equation_logarithmic`, `angular_equation_partial_deriv` (`S.B ↦ S.K`, with the minus of §1.7 on the angular ones); `differential_H`, `differential_H_angular`, `differential_H_radial`, `fderiv_logarithmicHamiltonian` (each summand gains `(S.D i : ℝ)`); `full_matrix_inverse_bound` (hypothesis restated with `S.K`) | `angular_equation_row`, `differential_H_angular_K` |
| `GlobalLiouvilleField` | `angular_equation_partial_deriv` (the glued form) | — |
| `BoundaryTangency` | `local_H_radial` (`= (S.D i : ℝ) * (nodeLog q i).im`) | — |
| `AllStrataGrowth` | `angularRhs_center` (gains the weight), `full_matrix_nu_equation` (`S.B ↦ S.K`, `+` → `-`) | `row_nu_equation` |
| `InteriorPartnerPropagation` | `angularRhs_eq_self_of_unit_neighbors` (gains the weight) | — |
| `CompactInteriorRigidity`, `CapAngularTangency`, `NativeRadialOrbit`, `LocalAngularDynamics` | **none** | — |
| every remaining dynamics, cap, confinement and assembly module | **none** | — |

Definitions whose *body* changed while their type did not are not in that table
and are exactly the ones §1.5–§1.7 discuss:
`GeometryTarget.SmoothPresentation.logarithmicImaginaryValue`,
`GlobalTwoForm.matrixForm`, `TorusPrimitive.beta`, `TorusPrimitive.alpha`,
`PrimitiveResidual.residual`, `TorusNondegeneracy.complexMatrix`,
`NodeTwoForm.complexForm`/`outsideBlock`/`residualMatrix`,
`NodeNondegeneracy.normalMatrix`, `TorusCorrection.H`,
`RegularCorrection.regularH`/`singularH`, `NativeNodePrimitive.block`,
`LocalPrimitive.eta`, `TorusLiouvilleDynamics.logarithmicHamiltonian`,
`LocalAngularDynamics.angularRhs` and `LocalAngularDynamics.nu`.

Two byte-level facts were checked directly against `e62c101` rather than taken
from a handoff: `ClusterSkeleton/FullSkeleton.lean` is **byte-identical**, and
the statements of `TorusLiouvilleDynamics.mutable_radial_equation`,
`frozen_radial_equation` and `real_logarithmicComponents` are **byte-identical**
to the baseline's.

The reference's own closing demands in `tex/target-theorem.tex` §5
("Acceptance requires the quantified weighted theorem, recovery of the old
specialization, the non-skew example above, full library and final consumer
compilation, and a transitive axiom audit…") are met by rows 18 and 19 for the
first three; the last two are verification artifacts and are now **produced** for
this source — the full library and final-consumer compilation and the transitive
axiom audit are the receipt of §5.

---

## 3. Gap and note list, re-evaluated for the weighted library

Every entry of the baseline list (**G1**–**G3**, **N1**–**N9**) is re-evaluated
below for the weighted setting and marked *kept*, *restated* or *retired*, with
the reason. The findings of the two delivered weighted semantic reviews are added
as **D1**, **D2**, **R4**–**R7** and **A1**, with the original observations at
`114d639` distinguished from their final status. **D1**, **D2** and **A1** are
closed; **R4** is closed at consumer level. **R5–R7** remain scope notes rather
than unmet acceptance criteria. The original ordering is retained for citations.

### R4 (closed at consumer level; citation boundary retained) — the full PDF theorem assembles separate proved clauses

*Source.* Stage-A review item 5, risk R4 (`4fe1632`).

*Content.* `LiouvilleSkeletonTarget` contains only density, the presentation and
`LiouvilleData` witnesses, the torus anchor and `trappedSet = coordinateCap`.
Theorem `thm:target` also asserts `C_E = ⋃_I Λ_I`, compactness of each `Λ_I`, and
the node-chart shape `𝒩^I × (ℂ*)^{n-2|I|}` with `2|I| ≤ n`. In the library these
are the separate `CapStrata.coordinateCap_eq_iUnion_lambdaStratum`,
`CapStrata.isCompact_lambdaStratum`, `IndependentNodeChart.homeomorph` and
`IndependentNodeSmooth.complementRank_eq_sub_two_mul_card` / `two_mul_card_le`,
all proved at `114d639`. The split is inherited from the accepted baseline and is
not a weighted regression, but **the final consumer and any statement review must
cite all four**, not `FirstGeometricTarget` alone. The clause-to-declaration map
of [`target-theorem.md`](target-theorem.md) is the list to cite.

One convenience of the stratified clause, noted by the final statement review:
`CapStrata.coordinateCap_eq_iUnion_lambdaStratum` is **flow-free**, so the
stratified form follows for *any* witness the target's existential produces; a
consumer never has to reach inside the target to recover
`NativeCompleteFlow.completeFlow`.
`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` is the packaged form for the
canonical witness, with `FullSkeleton.liouvilleData_flow` being `rfl`.

*The consumer side has since been landed.* Roadmap acceptance check 3 asks for a
**consumer** instantiating the final theorem on the non-skew input. At `114d639`
the line

```lean
theorem Examples.nonSkewSeed_target : LiouvilleSkeletonTarget Examples.nonSkewSeed :=
  FullSkeleton.liouvilleSkeletonTarget Examples.nonSkewSeed Examples.nonSkewSeed_unimodular
```

typechecks (verified in scratch, in both the `FirstGeometricTarget`-applied and
the direct form) but is not a declaration there. The accepted source commit
`a575aa236b485672f0606bba6ebc80571671f8a9` contains the module
`ClusterSkeleton/Examples/NonSkewSkeleton.lean`, with
`Examples.nonSkewSeed_side_checks` (the roadmap's side conditions in literal
form: the three data, `det E = 1`, positivity, entrywise skew-symmetry of `E·D`,
acyclicity of the mutable block, and the failure of skew-symmetry of `E`),
`Examples.nonSkewSeed_liouvilleSkeletonTarget`,
`Examples.nonSkewSeed_target_of_firstGeometricTarget` (the same statement read
off the quantified theorem at `d = 4`), `Examples.nonSkewSeed_trappedSet` and
`Examples.nonSkewSeed_trappedSet_iUnion`. All five are audit roots of the
receipt. Recovery clause (a) is likewise landed, as
`SkewSeed.liouvilleSkeletonTarget` (§1.11).

*Status.* **Closed at consumer level; retained as a citation discipline.** The
clause split is real and nothing is wrong or unproved. In the accepted source the
consumer lines exist as declarations, every separate clause
(`coordinateCap_eq_iUnion_lambdaStratum`, `isCompact_lambdaStratum`,
`isClosed_lambdaStratum`, `IndependentNodeChart.homeomorph`,
`complementRank_eq_sub_two_mul_card`, `two_mul_card_le`) is an audit root of the
receipt, and
`verification/FullSkeletonConsumer.lean`'s `PdfTargetConsumer.pdf_target` states
all of the clauses in **one** Lean type for an arbitrary unimodular seed, for the
same presentation, Liouville datum and flow the target's existential produces.
What remains is only that a reader of `FirstGeometricTarget` alone still does not
see the stratified form, so a statement review must cite the four theorems or
that one consumer.

### R6 (open, consumption discipline) — `exists_global_primitive` says nothing about the near-node shape

*Source.* Stage-B review item 6, risk R6 (`08472e0`).

*Content.* `GlobalPrimitive.exists_global_primitive` is existential in the
one-form `theta`, so no near-node identity can be extracted from it; the node
identity `alpha = residual - block + regularForm` lives in
`GlobalPrimitive.alpha_eq_eta` together with `LocalPrimitive.eta` /
`eta_zero_partners`, which are theorems about the *constructed*
`GlobalPrimitive.alpha`. The existential is nevertheless sharp enough for the
target, because its clause
`∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p` plus
density plus `GlobalPrimitive.eq_alpha_of_torus` determine `theta` uniquely.
Nothing in the module says anything about behaviour at infinity, and nothing
needs to: the blueprint's only global growth input is `|u̇_j| ≤ C(1+|u_j|)`, which
is `PrimitiveCutoffs.radial_linear_growth` plus step 12 of §2.

*Status.* **Open as a discipline, not a defect.** Consumers must take the
primitive from `GlobalPrimitive.alpha` with `alpha_eq_eta`, and a reviewer must
cite `alpha_eq_eta` alongside `exists_global_primitive`. Optional minimal change:
add the clause
`(∀ p q, q ∈ LocalPrimitive.neighborhood S ε κ δ p → theta q = LocalPrimitive.eta S hdet ε κ δ p q)`
to the existential.

### R5 (open, cheap) — the two cutoff parities are true, used, and unstated

*Source.* Stage-B review item 3, risk R5 (`08472e0`).

*Content.* `rho (-x) = rho x` and `vartheta δ (-T) = -vartheta δ T` are both
true (each closes by one `simp` in a scratch file) and neither is a statement in
`ClusterSkeleton/PrimitiveCutoffs.lean`: `grep` finds no
`rho_neg`/`rho_even`/`vartheta_neg`/`vartheta_odd` at `114d639` or in the
accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`. They are **not**
needed for the weighted chain — §1.4 made the arguments of `rho` and `vartheta`
the reference's own, so §1.6 and §1.7 use no parity at all. They *are* needed for
the pointwise `D = I` statement of §1.11, where `H` really is negated.

*Status.* **Open.** Minimal fix, additive and changing no statement:

```lean
theorem PrimitiveCutoffs.rho_neg (x : ℝ) : rho (-x) = rho x
theorem PrimitiveCutoffs.vartheta_neg (δ T : ℝ) : vartheta δ (-T) = -vartheta δ T
```

Consequence if not landed: the recovery can be proved only at the level of the
existential target (which is what §1.11 does and what the reference quantifies),
not as the stronger pointwise identity of primitives.

### R7 (open, scope wording) — the recovery is an existential, and the smooth structure must not be implied

*Source.* Stage-A review item 4 risk R1, sharpened as stage-B risk R7
(`08472e0`).

*Content.* At `D = 1` the weighted `beta` equals the baseline's, `H` is exactly
negated and `alpha` is equal, so the recovered field, flow and trapped set are
the baseline's. But that is an equality of the **coordinate evaluation formulas**,
not a Lean term equality of `Form 1`: the atlases differ (reciprocal versus
reference node coordinates), so `Tangent p` is not the same type.
`SkewSeed.pointHomeomorph` is a homeomorphism, not a diffeomorphism.

*Status.* **Open as a wording constraint, settled as a route.** Recovery is
stated for `S.toSeed` directly, with the old loci transported topologically; no
smooth structure is transported and none is claimed, per the recorded decision in
the module docstrings of `SkewSeedRecovery.lean` and `SkewSeedSkeleton.lean`,
and §1.11 above. Any
future text must not upgrade "the same flow" to a Lean term identity.

### D1 (closed in the accepted source) — `exchangeCharacter_eq_zpow_product`'s docstring asserted the opposite of its statement

*Declaration.* `NodeCoordinates.exchangeCharacter_eq_zpow_product`
(`ClusterSkeleton/NodeCoordinates.lean`, docstring immediately above the
theorem). Reported first in the stage-A review (`4fe1632`), again in the stage-B
review (`08472e0`), and **still present at `114d639`**.

*Content.* The docstring reads "the reference's inverse character `1/t_i`"; the
statement it documents proves `exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i)`,
which is `z^{c_i} = t_i` (§1.3). The sentence is the *baseline's* relation, which
the column convention inverted. It matters because this is the first file a
reader re-deriving a sign consults, and taken at face value it reproduces the
baseline's cancellation and yields `alpha = beta - dH`, i.e. a reversed Liouville
field — the one error the weighted reviews were commissioned to rule out. The
tree is self-contradictory here: the docstrings of `TorusPrimitive.alpha`,
`TorusCorrection.H` and `LocalPrimitive.eta` all state the correct relation.

*Status.* **Closed** in the accepted source commit
`a575aa236b485672f0606bba6ebc80571671f8a9`. Its docstring now opens "The exchange
ratio is the Laurent monomial with the actual signed **column** of `E`, i.e. the
reference character `t_i` itself, not its inverse", records that the baseline's
was `1/t_i`, and states that `normalizedPartner` is the reference's
`y = z_i'/P_i^-`. No statement changed: with comments stripped and whitespace
normalized, `NodeCoordinates.lean` is character-for-character identical to its
`114d639` version.

### D2 (closed in the accepted source) — `outgoing_ne_zero` is about incoming arrows

*Declarations.* `ZeroSet.Seed.Point.outgoing_ne_zero` and
`CapIndependence.coordinateCap_outgoing_not_interior`.

*Content.* `Seed`'s own docstring fixes the arrow convention as "`E i j > 0` for
an arrow from `i` to `j`". The hypothesis `0 < S.B i j` is `0 < S.E j i`, i.e. an
arrow `j → i`: `j` is a **predecessor** of `i`. The statements are correct and
match the blueprint (`B_{j_{r-1}i} > 0` forces `P_i^+(p) = 0`); only the name and
the first clause of the docstring are stale, and the second sentence of the
docstring already says the right thing.

*Status.* **Closed** in the accepted source commit
`a575aa236b485672f0606bba6ebc80571671f8a9` (docstrings only; the names are
deliberately kept because renaming ripples into other modules). The docstring of
`Seed.Point.outgoing_ne_zero` now spells out that `0 < S.B i j` is the column
exponent condition `0 < S.E j i`, hence an arrow `j → i`, and that the name is
retained from the baseline. `ZeroSet.lean` and `CapIndependence.lean` are
likewise code-identical to their `114d639` versions with comments stripped.

### A1 (closed by the receipt) — `verification/AxiomAudit.lean` had stopped covering four modules

*Source.* Final statement review item 8, defect A1
(`24b7bef8aaea7fd098e8ccd10474502d5a7320fa`).

*Content.* The `modules` array of `verification/AxiomAudit.lean` is
byte-identical to `e62c101` and lists the 58-module baseline inventory. The four
modules new at `114d639` — `ClusterSkeleton.SkewSeed`,
`ClusterSkeleton.SymmetrizerAlgebra`, `ClusterSkeleton.SeedAlgebra`,
`ClusterSkeleton.Examples.NonSkew` — are therefore not audited, and because the
loop errors only on a *listed* module with zero declarations, the audit would
still pass while silently under-covering four of the library's modules. The
review lists the module names to add and the `#print axioms` roots the weighted
theorem needs, including the `Seed`, `SeedAlgebra` and `SymmetrizerAlgebra`
facts, the separate clauses of **R4**, and — once landed — the recovery theorem
and the non-skew consumer.

*Status.* **Closed.** In the accepted source the `modules` array of
`verification/AxiomAudit.lean` has **65** entries and is exactly the set of files
`ClusterSkeleton/**/*.lean` (checked programmatically; symmetric difference
empty), so no module is silently uncovered, and `scripts/verify.py` independently
compares the audited module set with the library file set. The `#print axioms`
root list grew from 11 at `e62c101`, through 25 at the final-assembly commit, to
**72**: it now carries the `Seed`, `SeedAlgebra` and `SymmetrizerAlgebra` facts,
every separate clause of **R4**, the recovery theorem
`SkewSeed.skeleton_recovery` with the old-carrier compactness roots, and the
non-skew consumer `Examples.nonSkewSeed_target_of_firstGeometricTarget`; the last
two are additionally required by name in `scripts/verify.py`, so they cannot drop
out of a future receipt. Every one of the 72 roots reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

### G1 — **closed, and unaffected by the weights**: the cap is stated as `⋃_{I independent} Λ_I`

*Kept, with its scope statement re-derived.* The declarations are
`CapStrata.lambdaStratum`, `lambdaStratum_subset_coordinateCap`,
`coordinateCap_subset_lambdaStratum_strictCapIndices`,
`coordinateCap_eq_iUnion_lambdaStratum`, `isClosed_lambdaStratum`,
`isCompact_lambdaStratum` and
`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`, all present at `114d639` with
their baseline statements.

*Why the weights change nothing here.* All seven statements are phrased purely in
ambient coordinates `p.a`, `p.b` (§1.9) and contain no matrix, monomial,
character or weight. The only seed-dependent input is independence of the
realized index set, `CapIndependence.coordinateCap_strictCapIndices_independent`,
whose proof now inducts on `Seed.acyclic_exponent` instead of `S.acyclic`;
independence itself is not needed for either inclusion, only to index the union
by the reference's family. The baseline's proof sketches are therefore not
reproduced again in this revision.

### G2 — **closed, and now the literal blueprint statement**: the node-chart torus exponent

*Kept and strengthened in reading.* `IndependentNodeSmooth.complementRank_eq_sub_two_mul_card`
(`SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card`)
and `IndependentNodeSmooth.two_mul_card_le` (`2 * I.card ≤ d`), both in namespace
`ClusterSkeleton.IndependentNodeChart`, both taking only `hdet : S.Unimodular`
and `hI : S.Independent I`.

*What changed in the weighted setting.* Nothing in the statements; the
*justification* became the reference's own. Their input
`NodeCoordinates.independent_rows_inverse_pairing` now says that the rows of
`S.B = S.Eᵀ` indexed by `I` are the reference's columns `c_i = E e_i`, with
`S.B⁻¹ = (E⁻¹)ᵀ` the blueprint's integral retraction; the baseline reached the
same statement only through skewness of `B`. The computation is integral and
unweighted (role (f)): it uses `Seed.B_det : S.B.det = 1`, not `det K`.

### G3 — **restated**: unimodularity as `det E = 1` versus `E ∈ GL_n(ℤ)`

*Restated for the weighted seed; still optional and still low priority.* The
hypothesis is now `Seed.Unimodular : S.E.det = 1` and the reference's is
`E ∈ GL_n(ℤ)`. The baseline's reason for their coincidence (the Pfaffian identity
`det B = Pf(B)²` for integral skew `B`) **no longer applies**, because `E` is not
skew. The weighted reason is the PDF's own derivation, quoted in **N1**:
`det K = det E · ∏ d_i` with `K` a nonsingular rational skew matrix forces
`det E > 0`, and `det E = ±1` then gives `det E = 1`. The adaptable statement is

```lean
-- target module: ClusterSkeleton/Seed.lean (definition) + the use sites
def Seed.UnimodularUnit {d : ℕ} (S : Seed d) : Prop := IsUnit S.E.det

theorem Seed.unimodular_iff_isUnit_det {d : ℕ} (S : Seed d) :
    S.Unimodular ↔ S.UnimodularUnit
```

The forward direction is immediate. The converse needs positivity of the
determinant of a nonsingular real skew-symmetric matrix, which Mathlib does not
currently provide. Every downstream use already goes through a unit —
`NodeCoordinates.independent_rows_inverse_pairing` via `Seed.B_det`, and the
whole weighted dynamics via `SeedAlgebra.isUnit_det_Kreal` and
`TorusNondegeneracy.isUnit_complexMatrix_det` — so replacing the field would be
mechanical once the equivalence exists. Priority remains low: the two hypotheses
have the same models on the weighted input.

### N1 — **restated**: why `det E = 1` is the reference hypothesis

*The baseline reason is retired, the conclusion is kept.* Baseline: for integral
skew-symmetric `B` of even size `det B = Pf(B)²` and for odd size `det B = 0`, so
`det B = ±1 ⇒ det B = 1`. That argument is unavailable for the weighted `E`,
which is not skew. The weighted argument is the PDF's:

> In fact `det E = 1`: a nonsingular real skew-symmetric matrix has positive
> determinant, so `det E = det K/det D̃ > 0`, while unimodularity gives
> `det E = ±1`.

So `Seed.Unimodular : S.E.det = 1` is **not** a strengthening of `E ∈ GL_n(ℤ)` on
this input. Two remarks, both recorded by the stage-A review and neither a
defect: no Lean declaration carries this derivation, so a reviewer takes
`IsUnit S.E.det → S.Unimodular` on the PDF's authority (the cheap mitigation is a
docstring citation on `Seed.Unimodular`; the full Lean statement is **G3**); and
for odd `d` the pair `Seed d` + `Unimodular` is contradictory
(`det K = det E · ∏ d_i ≠ 0` while an odd skew matrix has determinant `0`), so
the weighted target is vacuous in odd ambient dimension — equally true of the PDF
input.

### N2 — **kept**: the algebraic exchange model

Unchanged by the weights. The reference uses `eq:acyclic-exchange-model` (BFZ III,
Cor. 1.21) twice: to derive the chart of Lemma (ii), and to know that `𝒜(B̃)` is
closed in `ℂ^{2m} × (ℂ*)^f`. Lean takes the actual complex solution set as its
carrier (`Seed.Point`, inherited topology), constructs the chart directly
(`IndependentNodeChart.forward`/`backward`/`homeomorph`, with
`IntegralBasisCompletion` replacing the Laurent-ring argument), and proves
exactly the needed closedness/compactness statements
(`CapSet.isClosed_ambientCap` (private),
`FiniteTimeConfinement.CoordinateBounds.isClosed_ambientBox` (private),
`isCompact_coordinateBox`). Formalizing the presentation would add no step of the
skeleton proof. The weighted change is only that the presentation is now the
reference's column-exponent one.

### N3 — **kept**: holomorphic `Ω` versus real `Im Ω`

Unchanged by the weights. Lean constructs the **real** smooth closed nondegenerate
extension of `Im Ω` (`GlobalTwoForm.omega`, `GlobalSymplectic.*`), anchored on the
dense initial torus and unique there
(`FormExtensionUniqueness.smoothAtlas_twoForm_extension_unique`,
`LocalFormGluing.existsUnique_smooth_gluing`). The skeleton theorem uses only
`Im Ω`, and `tex/target-theorem.tex` excludes holomorphic extension from the
claim. The weighted node computation is nevertheless carried out on the
**complex** node form `NodeTwoForm.complexForm` and then pushed to the real one,
which is where the coefficient `-d_i/t_i` of §1.5 lives. No holomorphic statement
is claimed.

### N4 — **restated**: the `θ̇ = -K^{-1}∂_u H` form of the flow

*Kept, with the weighted inverse identities now named.* The reference writes the
angular equation with `K^{-1}` and needs `c_i(K^{-1}x) = -x_i/d_i` to read `η̇_i`
and `v̇_i` off `θ̇`. Lean obtains both equations directly from the contraction
identity, by pairing `Im Ω` against `TorusLiouvilleDynamics.radialTangent i` and
`angularTangent j` (`angular_equation`, `radial_matrix_equation`), so no inverse
of `K` enters there, and `angular_equation_row` performs the reference's
`c_i`-pairing by `SeedAlgebra.sum_K_row` rather than by inverting. Where an
inversion genuinely happens — `real_logarithmicComponents`,
`full_matrix_inverse_bound`, `LocalAngularDynamics.nu` — it is an inversion of
`SeedAlgebra.Kreal` through `isUnit_det_Kreal`, and the reference's identity
itself is available as `SeedAlgebra.c_inv_K` /
`SeedAlgebra.vecMul_Ecol_inv_Kreal` / `SeedAlgebra.Breal_mulVec_inv_K` (field
version `SymmetrizerAlgebra.vecMul_E_col_inv_K`). **The baseline's statement of
this entry is now false** and is retired: Lean no longer inverts `B` with
`det B = 1` in the dynamics; `det B = 1` survives only in the integral chart
computation (**G2**). Nothing is missing.

### N5 — **kept**: route to completeness

Unchanged by the weights, and byte-unchanged in Lean. The reference argues that a
maximal integral curve with finite `τ_±` must leave every compact set. Lean
proves finite-horizon confinement into a compact set chosen before the curve
(`FiniteTimeConfinement.finite_time_compact_confinement`,
`bounded_horizon_closure`) and combines it with a uniform local lifetime on
compacts, obtaining a genuine two-sided `Flow` with joint smoothness
(`NativeCompleteFlow.exists_completeLiouvilleFlow`, `completeFlow`). At least as
strong as the reference's conclusion, and what `LiouvilleData` requires.

### N6 — **kept**: angular rigidity without the sign of `∂_{u_i}χ_i`

Unchanged by the weights, and byte-unchanged in Lean except for the `S.skew` →
`Seed.B_diag_zero`/`B_eq_zero_iff` proof repairs. For `i ∈ I∖I_0` the reference
shows `|η_i-π|` is nondecreasing, using `h' ≥ 0`, `h ≤ 0`, `ρ ≥ 0`,
`∂_{u_i}χ_i ≤ 0` and `(η-π)β(η) ≥ 0`. Lean splits this into (a) the deep regime,
where the coefficient is **exactly** `1`
(`CompactInteriorRigidity.amplitude_single_deep`,
`characterCoefficient_eq_one_deep`, using `Seed.B_diag_zero` and
`CompactInteriorRigidity.row_single`) with the monotone-distance argument
`angular_scalar_eq_neg_one_of_tendsto` whose only sign input is
`CompactInteriorRigidity.sin_mul_vartheta_nonneg` (the lift-free form of
`(η-π)β(η) ≥ 0`), and (b) backward Gronwall uniqueness on the compact collar for
an **arbitrary continuous** coefficient
(`InteriorPartnerPropagation.angular_scalar_eq_neg_one`,
`CompactInteriorRigidity.angular_scalar_eq_neg_one_backward`). It therefore needs
no sign hypothesis on `∂_{u_i}χ_i` and covers coefficients of either sign.

### N7 — **kept**: generic cutoffs versus one explicit family

Unchanged by the weights: the reference's cutoff clauses contain no `d_i`. The
theorem is an existence statement, so one admissible family suffices; Lean fixes
the explicit family of §1.8, proves each required property
(`PrimitiveCutoffs.*`, `DominanceCutoff.*`) and records existence lemmas
(`DominanceCutoff.exists_chi`). The quantitative hypothesis `2ε+1 ≤ κ` is the
Lean form of `L > a > 0` with a uniform margin;
`FullSkeleton.liouvilleSkeletonTarget` discharges it with `ε = 1, κ = 3, δ = 1`.

### N8 — **kept**: angular representative/lift

Unchanged by the weights. The reference fixes "the lift in `(-ε,ε)` on this arc".
Lean never chooses a lift: `PrimitiveCutoffs.vartheta δ` is `2π`-periodic
(`vartheta_periodic`, `vartheta_representative_independent`) and is applied to
`Complex.arg (-exchangeCharacter)`, with the sign facts proved through
`Complex.norm_mul_sin_arg` rather than through a branch. This removes a side
condition rather than adding one. The weighted change is only that the argument
is now `+(η-π)` instead of `-(η-π)` (§1.4).

### N9 — **kept**: the `W` and `O` neighborhoods

Unchanged by the weights. The reference's `W` (all plateaus active near a divisor
point) and `O` (`z_i ≠ 0`, neighbors not deep) are the open sets
`PrimitiveLocalization.region`/`neighborhood` and
`LocalPrimitive.neighborhood`, with the plateau conclusions
`PrimitiveLocalization.plateaus` ("`ρ(v_i)=1`, `β(η_i)=η_i-π`, `u_i ≤ -L`,
`h(u_i)=u_i+a`, `χ_i=1`") and `PrimitiveLocalization.adjacent_dominance_zero`
("`χ_j = 0` there"), and membership `region_mem_nhds`,
`LocalPrimitive.mem_neighborhood`, `covers`. The reference's "by density"
extensions off the torus are performed by explicit continuity-plus-density
arguments on these open sets, e.g. in `BoundaryTangency.nodeLog_drift`,
`ZeroStratumInvariance.normSq_drift`,
`NormalizedPartnerNormDrift.normSq_drift`.

### Retired baseline entries

* The baseline summary's "three sign and duality facts" (interchanged monomials,
  inverted character, `H_Lean = -H_ref` with `alpha = beta - dH`) is **retired in
  full**: all three are false for the weighted library. Their replacements are
  the four facts of the summary above.
* The baseline **N4** sentence "the only inversion Lean performs is on the radial
  components … via `det B = 1`" is **retired**: see **N4** above.
* The baseline's reliance on `rho` even and `vartheta` odd to match `H` is
  **retired** for the weighted statements and survives only in §1.11 (**R5**).

---

## 4. Scope statements

* **The claim is weighted.** Every correspondence above is stated for an
  arbitrary positive rational `D` and an integral `E` that is **not** assumed
  skew-symmetric, with `K = E D̃` skew. The Lean `Seed` has no skewness field:
  `Seed.skew` does not exist, and the sign facts it used to supply are the lemmas
  of §1.1, derived from `skewSymmetrizable` and `D_pos`. The final theorem
  `FullSkeleton.firstGeometricTarget` quantifies over every `Seed d` with
  `S.Unimodular`, and no step of this audit restricts `D`, assumes all weights
  agree, or assumes `E` skew.
* **Column exponents.** The exchange monomials are the reference's
  `P_i^± = ∏_j z_j^{[±E_{ji}]_+}` literally (§1.2), so `Seed.Point` is the
  reference's `X_E` on the nose. The internal abbreviation `S.B := S.Eᵀ` is a
  notational convenience for the exponent, adjacency, character and
  integer-lattice roles only; the form coefficient is `S.K` everywhere (§1.5,
  §1.10). The reference's alternative permission ("or supply a proved convention
  equivalence") is not used for the exchange space, which is definitionally the
  column-convention one; the form-sign half of that sentence is discharged by
  §1.5.
* **Mutable acyclicity and variable frozen coordinates are retained** everywhere
  (`Seed.acyclic`, and `Seed.Point`'s `∀ f ∉ S.mutable, p.a f ≠ 0`). No step
  suggests removing either, and **no principal-coefficient assumption** appears
  on either side: no frozen value is fixed.
* **Unimodularity is retained** (`Seed.Unimodular : S.E.det = 1`), as a separate
  hypothesis quantified in `FirstGeometricTarget`; see **N1** and **G3**.
  Intermediate lemmas proved without it are strictly stronger. The unimodular
  completion is part of the input; existence of such a completion for every
  exchange matrix is **not** asserted, exactly as the reference says.
* **Not claimed:** holomorphic extension of `Ω` itself, finite type, generalized
  cocores, cap products, categorical mirror symmetry (**N3**); singular
  completions; arbitrary cyclic seeds; any statement about odd ambient dimension
  beyond vacuity (**N1**); a transported smooth structure on the old carrier or a
  term identity of the recovered flow with the baseline's constructed flow
  (§1.11, **R7**); and anything about the behaviour of the primitive at infinity
  (**R6**).
* **This audit is a statement-level comparison.** A Lean build checks
  elaboration, not whether the statements mean the intended mathematics; that
  judgement is the two delivered semantic reviews cited above, and this document
  records their conclusions with the declarations they apply to. Nothing here
  re-derives a sign a review already settled, and every sign it does state was
  re-checked by `rfl` or `#check` at `114d639` and again, name by name, against
  the accepted source (§Verification method).
* **The `D = I` baseline is history.** It appears only where it is explicitly
  compared with the weighted library (§1.2, §1.6, §1.10, §2.1 and the
  re-evaluated entries of §3) and in the recovery section §1.11, and in every
  case it is labelled as the superseded library at `e62c101`. The weighted target
  is never restated as `D = I`.

---

## 5. Verification status

The weighted library is **verified** at accepted source commit
`a575aa236b485672f0606bba6ebc80571671f8a9`, receipts of 10 November 2026. A
managed `horizon-lean-check ClusterSkeleton` reported status *passed*, return
code 0, snapshot verified, 9029 jobs, toolchain Lean 4.34.1 / Lake 5.0.0,
warnings only, with the pinned Mathlib `d13f23b7…` and FsFltz `1a3d387c…`.
`python3 scripts/verify.py` then ran as a replay of that up-to-date tree and
ended with `FULL_GEOMETRIC_TARGET_VERIFIED`.

What exists for this source:

* the accepted-source manifest —
  [`../verification/accepted-library.json`](../verification/accepted-library.json)
  binds commit `a575aa2…` with the SHA-256 of each of its **65** library files,
  and names the four review documents;
* the receipt —
  [`../verification/publication-check.json`](../verification/publication-check.json),
  `status: passed`, `dependency_worktrees_clean: true`,
  `source_stability_verified: true`, recording **65 modules**, **1811 audited
  declarations** (`TOTAL_AUDITED`), **72 `#print axioms` roots** and **73 hashed
  inputs**, with the SHA-256 of every input and of the four logs;
* the transitive axiom log —
  [`../verification/axioms.log`](../verification/axioms.log). Every one of the 72
  roots reports exactly `propext`, `Classical.choice`, `Quot.sound`, and none
  reports "does not depend on any axioms". Across all 1811 audited declarations
  every axiom set is a subset of that allowlist (1703 all three, 87 `propext`, 18
  `propext` + `Quot.sound`, 3 none, 2 `Quot.sound`), and both generated
  declarations are present and conforming;
* the build and final-consumer compilation —
  [`../verification/build.log`](../verification/build.log),
  [`../verification/final-consumer.log`](../verification/final-consumer.log) (a
  successful Lean check can produce an empty log) and
  [`../verification/toolchain.log`](../verification/toolchain.log);
* the weighted statement review —
  [`../verification/statement-review.md`](../verification/statement-review.md),
  installed from Appendix B of the final statement review together with the
  recovery review's replacement paragraphs, with the residual notes (**R4** and
  the one-place consumer, the node chart being a homeomorphism with the smooth
  structure carried by `IndependentNodeSmooth`/`SmoothAtlas`, **R-N1** on the two
  carriers of the recovery, **R5**–**R7**, **N1**/**G3**);
* the expanded module list and root list of `verification/AxiomAudit.lean` —
  finding **A1** is closed, and `verification/FullSkeletonConsumer.lean` gained
  `PdfTargetConsumer.pdf_target`, which states every published clause in one
  Lean type (finding **R4**).

The recovery module `ClusterSkeleton/SkewSeedRecovery.lean`, the skeleton package
`ClusterSkeleton/SkewSeedSkeleton.lean` and the consumer module
`ClusterSkeleton/Examples/NonSkewSkeleton.lean`, together with their imports into
`ClusterSkeleton.lean`, are part of the accepted source and are built by
`lake build ClusterSkeleton`; their statements are audit roots of the receipt.
Their names in this guide are the accepted source's.

Still open, and deliberately not claimed anywhere in this guide: **R5** (the two
cutoff parities are not Lean statements), **R6**, **R7** and **R-N1** (the
recovery is stated on two carriers, with the smooth structure existential), and
**N1**/**G3** (the manuscript's derivation of `det E = 1` from
`det K = det E · ∏ d_i > 0` is carried by no Lean declaration). None requires a
change to a statement proved here.

**Archon accepted the formalization phase and completed the run.** The
[acceptance record](../verification/archon-acceptance.json) preserves the
source-bound decision and its scope notes. The superseded baseline receipts at
`4c02c1e5bbc68907552632344ae04017d82a30b4` are replaced, not retained.
