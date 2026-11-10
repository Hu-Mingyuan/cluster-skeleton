# Stage B semantic audit: do the weighted two-form, `H`, `alpha = beta + dH` and the node primitive mean the mathematics of `proof-blueprint.tex`?

Independent **statement** review (not a build check) of stages B1 and B2 of
objective `7d3240fc-f412-49c4-88c8-a9d1a5a1bdaf` revision 2 (acceptance check 5),
mission `e6bc9a42-022f-4f21-a67d-470449b0d726`.

* Reviewed source: commit `6cdcef797a431e838e6b6f55a98f03d4200a9ab9` (branch
  `weighted/stage-b2`), chain
  `e62c101 -> de58cd2 (A) -> 03111ac (SymmetrizerAlgebra) -> c679eb1 (B1) -> 6cdcef7 (B2)`.
* Reference: `docs/tex/proof-blueprint.tex`, `docs/tex/target-theorem.tex`,
  `docs/roadmap.md`, `docs/skeleton-audit.md` §1.2–1.6 (the accepted `D = I`
  baseline), `docs/reviews/stage-a-semantic-audit.md` @ `4fe1632`,
  `docs/weighted-stage-c-map.md` §4 @ `ee47a57`.
* Worker handoffs read, then verified independently and **not** relied on:
  obligation `b5fa33df` (B1, assignment `fdaadca8`) and `7debf436`
  (B2, assignment `1131554f`).
* Review branch: `weighted/stage-b-audit`. The stage B2 objects are not present
  in this checkout and the remote is not reachable with agent credentials, so
  the tree was reproduced per path through
  `GET /api/v3/repositories/5d09d029-…/file?commit_oid=6cdcef79…&path=…`,
  on top of `37994c9` (the earlier byte-exact reproduction of the stage A tree
  `de58cd2`). Reproduction commit `eb356ed`. Exactly **15** paths differ between
  `de58cd2` and `6cdcef7` — the six stage-B1 modules `DominanceCutoff`,
  `GlobalTwoForm`, `NodeNondegeneracy`, `NodeTwoForm`, `Seed`,
  `TorusNondegeneracy`, the added `SymmetrizerAlgebra`, and the eight stage-B2
  modules `TorusPrimitive`, `PrimitiveResidual`, `TorusCorrection`,
  `PrimitiveLocalization`, `RegularCorrection`, `NativeNodePrimitive`,
  `LocalPrimitive`, `GlobalPrimitive`. For each of the 15 the recomputed git
  blob hash equals the API `blob_oid`; the remaining 77 paths were queried and
  reported a `blob_oid` identical to the stage A tree, so the tree of `eb356ed`
  equals the tree of `6cdcef7`. (The repository API exposes no tree listing —
  `agent schema --section routes` has only `repository_head` and
  `repository_file` — so a path added by B1/B2 outside `git ls-tree -r de58cd2`
  would not appear here; `ClusterSkeleton/SeedAlgebra.lean` and
  `docs/weighted-stage-c-map.md` were probed explicitly and are **absent** at
  `6cdcef7`.)
* **No Lean file is modified or added by this review.** Claims marked
  **[elab]** were machine-checked in a scratch file `Scratch.lean` at the
  repository root with `lake env lean Scratch.lean`; the file was deleted before
  committing and its content is reproduced in Appendix A. As a by-product,
  `lake build ClusterSkeleton.GlobalPrimitive ClusterSkeleton.RegularCorrection
  ClusterSkeleton.GlobalSymplectic ClusterSkeleton.NodeNondegeneracy` on the
  reproduced tree completes successfully (2914 jobs, warnings only), which
  independently confirms B2's build claim for the delivered chain.

## Verdict summary

| # | Item | Verdict |
| --- | --- | --- |
| 1 | Weighted two-form, node coefficient, nondegeneracy (B1) | **PASS** |
| 2 | `TorusPrimitive.beta` versus `λ_tor`, and `d beta = Im Ω` (B2) | **PASS** |
| 3 | `TorusCorrection.H` versus `H = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)` | **PASS** — `H_Lean = +H_ref`, definite (**RISK R5**) |
| 4 | `alpha := beta + dH`, and the Liouville field by hand | **PASS** — `alpha = λ_ac`; `eq:acyclic-flow` verbatim, **no extra sign** |
| 5 | Node block, `eta = residual − block + regularForm`, extension across `z_i = 0` | **PASS** |
| 6 | `GlobalPrimitive`'s final statement | **PASS** (**RISK R6**: no near-node / infinity clause inside the existential) |
| 7 | `D = I` specialization versus the `e62c101` baseline | **PASS** — `beta` **equal**, `H` **negated**, `alpha` **equal** (**RISK R7**) |
| 8 | Convention table | **delivered** below |

**No URGENT-DEFECT.** The two signs that the torus anchor cannot see are both
right: `H_Lean = +H_ref` and `alpha = beta + dH`, and they are mutually
consistent with the third sign that moves with them, `LocalPrimitive.eta =
residual − block + regularForm`. The hand derivation of §4 reproduces
`eq:acyclic-flow` and `eq:acyclic-angle-flow` with no residual sign and with the
weights `d_i` cancelling exactly where the blueprint says they do. The Liouville
field has the blueprint's direction.

Findings, with the downstream stage each affects:

| id | kind | declaration | stage |
| --- | --- | --- | --- |
| D1 | DEFECT (docstring asserts the opposite of its statement; carried over from the stage A audit, **still present** at `6cdcef7`) | `ClusterSkeleton.exchangeCharacter_eq_zpow_product` | C (reading hazard only) |
| R5 | RISK (the parity facts pinning the `H` sign are nowhere stated in Lean) | `PrimitiveCutoffs.rho`, `PrimitiveCutoffs.vartheta` | C, integration |
| R6 | RISK (acceptance scope) | `GlobalPrimitive.exists_global_primitive` | C |
| R7 | RISK (recovery claim needs the smooth-structure transport) | `SkewSeed.pointHomeomorph` consumers | C |

No DEFECT requires a change to any B1 or B2 **statement**. D1 is a stage-A
docstring that stage B2 was forbidden to touch, and stage B2's own docstrings
(`TorusPrimitive.alpha`, `TorusCorrection.H`, `LocalPrimitive.eta`,
`PrimitiveResidual.beta_decomposition`) now say the correct thing, so the tree
is self-contradictory in exactly the file a stage-C worker reads first.

---

## 1. Weighted two-form, node coefficient and nondegeneracy (B1) — PASS

### 1a. The global form coefficient is `K`, with the PDF's sign

#### Lean (`ClusterSkeleton/GlobalTwoForm.lean:230-238`)

```lean
def matrixForm : (Fin d → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.imCLM.compContinuousAlternatingMap
    (((1 / 2 : ℂ) • ∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℂ) •
      wedge (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj j)).restrictScalars ℝ)

theorem matrixForm_apply (v : Fin 2 → (Fin d → ℂ)) :
    matrixForm S v = ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
      (S.K i j : ℂ) * (v 0 i * v 1 j - v 1 i * v 0 j)).im
```

```lean
def complexMatrix : Matrix (Fin d) (Fin d) ℂ := fun i j => (S.K i j : ℂ)   -- TorusNondegeneracy.lean:29
theorem complexMatrix_det (hdet : S.Unimodular) :
    (complexMatrix S).det = ∏ i, (S.D i : ℂ)                               -- :35
theorem isUnit_complexMatrix_det (hdet : S.Unimodular) :
    IsUnit (complexMatrix S).det                                           -- :47
```

#### Blueprint (`proof-blueprint.tex`, "Skeleton in the acyclic case")

> `Ω = ½ ∑_{j,l} K_{jl} d log z_j ∧ d log z_l`, `λ_tor = u^T K dθ`.
> "On the initial torus, `Im Ω = ∑_{j,l} K_{jl} du_j ∧ dθ_l`."
> (`target-theorem.tex` §1: `det E = 1`, so `det K = det E · ∏ d_j = ∏ d_j > 0`.)

#### Judgement

`wedge a b v = a (v 0) * b (v 1) - a (v 1) * b (v 0)`
(`NodeTwoForm.lean:43`, **[elab]** by `rfl`), so `matrixForm` is term-for-term
`Im(½ ∑_{i,j} K_{ij} dlog a_i ∧ dlog a_j)`: the `½` is present as in the PDF, the
first index of `K` sits on the first slot exactly as the PDF's first `dlog`
factor does, and the cast is of the **rational** `K = E D̃`, not of `E`. Its real
expansion is proved:

```lean
theorem matrixForm_real (v w : Fin d → ℂ) :                 -- TorusPrimitive.lean:115
    GlobalTwoForm.matrixForm S ![v, w] =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (v i).re * (w j).im) -
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (w i).re * (v j).im)
```

which is literally `(∑_{j,l} K_{jl} du_j ∧ dθ_l)(v,w)`, i.e. the blueprint's own
torus formula, **with the same sign, no transpose and no extra factor**. I
re-derived the reduction independently: with `K^T = -K` (`Seed.K_skew`), writing
`X_i = du_i(v)`, `Y_i = dθ_i(v)` and `X'`, `Y'` for `w`,
`Im(½∑_{i,j}K_{ij}(ζ_i(v)ζ_j(w) − ζ_i(w)ζ_j(v))) = ∑_{i,j}K_{ij}(X_iY'_j + Y_iX'_j)`,
and relabelling the second sum by `i ↔ j` with `K_{ji} = −K_{ij}` turns it into
`∑K_{ij}X_iY'_j − ∑K_{ij}X'_iY_j`. **[elab]** `matrixForm_apply` and
`matrixForm_real` both elaborate at the `K` coefficient on the published commit.
The determinant clause is the weighted replacement of the baseline's
`det B = 1`, and it is the right one: `∏ d_i ≠ 0` by `D_pos`, and the PDF
*derives* `det E = 1` rather than assuming it. **PASS.**

**Stage-A risk R2 is discharged.** Every surviving `S.B` occurrence in the six
B1 and eight B2 modules was inventoried (`grep -n 'S\.B'`); each is an
exponent/character row (role (d): `PrimitiveResidual.tau`/`logRow`,
`TorusCorrection.rowLog`, `PrimitiveLocalization.rowLog`,
`RegularCorrection.literal_formula`, the `∏ x_j ^ S.B i j` sites of
`PrimitiveResidual`), an adjacency test (role (b): `DominanceCutoff.mutableNeighbors`,
`RegularCorrection.surviving`, the `∃ i ∈ p.zeroSet, S.B i j ≠ 0` hypotheses), an
integer-lattice pairing (role (f): `NodeTwoForm.row_inverse`, `row_outsideLog`), or
one side of a `K ↔ B` conversion lemma (`Seed.K_eq_neg_D_mul_B`,
`PrimitiveResidual.sum_K_row_real`, `NodeTwoForm.row_outsideLog_weighted`,
`NodeNondegeneracy.normalMatrix_injective`). **There is no surviving `S.B`
form-coefficient site.** `TorusNondegeneracy`, `GlobalTwoForm`,
`GlobalSymplectic`, `NativeNodePrimitive`, `LocalPrimitive`, `GlobalPrimitive`
and `TorusPrimitive` contain no `S.B` at all.

### 1b. The node chart coefficient — PASS, including the sign

#### Lean (`ClusterSkeleton/NodeTwoForm.lean:135-140`)

```lean
def complexForm (x : Vector S I) : Vector S I [⋀^Fin 2]→L[ℂ] ℂ :=
  (∑ i : {i : Fin d // i ∈ I}, (-(S.D i : ℂ) * (rawParameters S I x (Sum.inl i))⁻¹) •
    wedge (du S I i) (dv S I i)) +
  (1 / 2 : ℂ) • ∑ k, ∑ l, (residualMatrix S I hdet hI k l : ℂ) •
    wedge (logParameter S I x k) (logParameter S I x l)
```

```lean
def residualMatrix : … := (rationalInverseMatrix S I hdet hI).transpose *
    outsideBlock S I * rationalInverseMatrix S I hdet hI       -- :130, i.e. Tᵀ K_J T
def outsideBlock : … := S.K.submatrix (·.val) (·.val)          -- :104
theorem row_outsideLog_weighted (x t : Vector S I) (i : {i : Fin d // i ∈ I}) :
    (∑ j : {j : Fin d // j ∉ I}, (S.K i j : ℂ) * outsideLog S I hdet hI x j t) =
      -(S.D i : ℂ) * logParameter S I x (Sum.inl i) t                      -- :256
```

#### Blueprint (`proof-blueprint.tex`, "Weighted form on the actual node charts")

> `Ω = ∑_{i∈I} d_i d log t_i ∧ d log x_i + Ω₀(t,s)`, where `Ω₀` has constant
> coefficients in `d log t_i, d log s_a`. "Indeed the `x_i` row is determined by
> `∑_j K_{ij} d log z_j = -d_i d log t_i`." "On the node `x_i y_i = 1+t_i`,
> `d log t_i ∧ d log x_i = t_i^{-1} dy_i ∧ dx_i`."

#### Judgement

`du S I i` is `dx_i` and `dv S I i` is `dy_i` (`:75-80`: first and second
component of the `i`-th pair). **[elab]**
`rawParameters S I x (Sum.inl i) = (x.1 i).1 * (x.1 i).2 - 1` by `rfl`, i.e.
`q_i = x_i y_i - 1 = t_i`, and `logParameter S I x (Sum.inl i) v =
((x.1 i).2 * (v.1 i).1 + (x.1 i).1 * (v.1 i).2) / ((x.1 i).1*(x.1 i).2 - 1)`, i.e.
`d(x_iy_i)/t_i = dt_i/t_i = d log t_i`. Hence the node term is
`-∑_{i∈I} (d_i/t_i) dx_i ∧ dy_i`. Independently, from the blueprint identity
(re-derived here: `dt = y dx + x dy`, so
`d log t ∧ d log x = ((y dx + x dy)/t) ∧ (dx/x) = (dy ∧ dx)/t`),
`∑_{i∈I} d_i d log t_i ∧ d log x_i = ∑ (d_i/t_i) dy_i ∧ dx_i = -∑ (d_i/t_i) dx_i ∧ dy_i`.
**The two agree, sign included.** The baseline had `+(rawParameters …)⁻¹`; the
flip is forced by `K i j = -(d_i)(B i j)` (`row_outsideLog_weighted`) and is the
weighted form of the blueprint's displayed `x_i` row. At a chart centre
(`x_i = 0`, so `q_i = -1 = t_i`) the block is `+(S.D i : ℂ)`
(`complexForm_boundary`, `:596`), consistent with `-d_i/(-1) = +d_i`. **PASS.**

The identification with `Ω` is not left to inspection: `complexForm_torus`
(`:528`) proves `complexForm S I hdet hI x ![a,b] = matrixValue
(TorusNondegeneracy.complexMatrix S) (originalLog …) (originalLog …)` on the
torus part of the node domain, and `localForm_torus` (`:551`) proves
`evalTwo (localForm S I hdet hI) p a b = P.logarithmicImaginaryValue p a b` for
`p ∈ initialTorus S`. `GlobalTwoForm.localCompatibility` / `omega_eq_localForm`
then make `omega` the common extension. So the global form **is** the blueprint's
`Ω` with the right sign **in every chart**, the off-torus part being the
extension by density that the blueprint itself prescribes ("The local extensions
agree on overlaps by density of the initial torus"). **PASS.**

### 1c. Nondegeneracy, and on what set — PASS

#### Lean

```lean
def weightProjection : Matrix {i // i ∈ I} (IndependentRowBasisIndex S I) ℂ :=
  fun i k => -(S.D i : ℂ) * (rowProjection : …) i k               -- NodeNondegeneracy.lean:82
def normalMatrix : Matrix ({i // i ∈ I} ⊕ IndependentRowBasisIndex S I) … ℂ :=
  Matrix.fromBlocks 0 (weightProjection S I) (-(weightProjection S I).transpose)
    (complexResidual S I hdet hI)                                  -- :96
theorem complementMatrix_kernel (w : Complement S I → ℂ)
    (hw : (complementMatrix S I hdet hI).mulVec w = 0) : w = 0     -- :183
theorem zeroSet_localForm_nondegenerate (p : S.Point)
    (a : … .Tangent p)
    (ha : ∀ b, SmoothManifold.evalTwo (localForm S p.zeroSet hdet p.zeroSet_independent) p a b = 0) :
    a = 0                                                          -- :305
```

```lean
theorem nondegenerate_omega (p : S.Point) :                        -- GlobalSymplectic.lean:15
    (SmoothAtlas.presentation S hdet).manifold.Nondegenerate (GlobalTwoForm.omega S hdet) p
theorem exteriorDerivative_omega (p : S.Point) :                   -- GlobalTwoForm.lean
    … .exteriorDerivative (omega S hdet) p = 0
theorem isSymplecticOn_omega :                                     -- GlobalSymplectic.lean:30
    … .IsSymplecticOn (GlobalTwoForm.omega S hdet) Set.univ
```

#### Blueprint

> "Its skew matrix, in these coordinates, is
> `((0, -D_I, 0), (D_I, A, B₀), (0, -B₀ᵀ, C))`. It is nonsingular, so `C` is
> nonsingular, by eliminating the first two block rows (with the empty-block
> convention when necessary). … Pairing against the `y_i` directions, then the
> `s_a` directions, then the `x_i` directions proves nondegeneracy, using
> `d_i ≠ 0` and nonsingularity of `C`."

#### Judgement

`weightProjection i (Sum.inl i') = if i = i' then -(S.D i : ℂ) else 0` and
`weightProjection i (Sum.inr r) = 0` (`:86`, `:91`), so on
`I ⊕ (I ⊕ R)` `normalMatrix` has block rows `[0 | -D_I, 0]`, `[D_I | A, B₀]`,
`[0 | -B₀ᵀ, C]` — the blueprint matrix **entry for entry**, with `-B₀ᵀ` supplied
by `complexResidual_skew` (`:74`, proved from `Seed.K_skew` through
`complexOutsideBlockᵀ = -complexOutsideBlock`). The elimination of the first two
block rows is `SymmetrizerAlgebra.residualBlock_eq_zero_of_mulVec_eq_zero` with
`δ i = -(S.D i : ℂ)` and `δ i ≠ 0` from `D_pos` — the blueprint's "`d_i ≠ 0`".
The three pairings are `complexForm_boundary_nondegenerate` (`:201`) in exactly
the blueprint's order: the `y_i` directions give `(S.D i : ℂ) * (a.1 i).1 = 0`
hence `(a.1 i).1 = 0`; then the complement directions give
`vecMul (a.2 ·/x.2 ·) complementMatrix = 0`, killed by
`complementMatrix_isUnit`; then the `x_i` directions give `(a.1 i).2 = 0`.
Every division is by a nonzero `d_i`, replacing the baseline's `det B = 1`.

**Nondegeneracy is claimed on the whole space, not just the torus.**
`nondegenerate_omega` quantifies over an arbitrary `p : S.Point` with **no**
`p ∈ initialTorus S` hypothesis; it routes through that point's own zero-set
chart (`zeroSet_chart_mem`, `omega_eq_localForm`). **[elab]** confirmed, together
with `Nondegenerate M eta x = ∀ v, (∀ w, evalTwo eta x v w = 0) → v = 0` by
`rfl`. Closedness (`exteriorDerivative_omega`) is likewise pointwise on all of
`S.Point`, and `isSymplecticOn_omega` is stated on `Set.univ`. **PASS.**

---

## 2. `TorusPrimitive.beta` versus `λ_tor` — PASS

### Lean (`ClusterSkeleton/TorusPrimitive.lean:28-39`)

```lean
def beta : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  covectorForm _ (fun p => ∑ i : Fin d, ∑ j : Fin d,
    ((S.K i j : ℝ) * Real.log ‖p.a i‖) • angleCovector S hdet j p)

/-- There is no factor one half, minus sign, or inverse matrix in beta. -/
theorem evalOne_beta (p : S.Point) (v : … .Tangent p) :
    SmoothManifold.evalOne (beta S hdet) p v =
      ∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * Real.log ‖p.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im
```

with `angleCovector j p v = (coordinateDifferential j p v / p.a j).im`
(`:21`), i.e. `dθ_j = Im(da_j / a_j)`, and

```lean
theorem exteriorDerivative_beta (p : S.Point) (hp : p ∈ initialTorus S) :   -- :285
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (beta S hdet) p =
      GlobalTwoForm.omega S hdet p
```

### Blueprint

> `λ_tor = u^T K dθ`, i.e. `∑_{j,l} K_{jl} u_j dθ_l`, with
> `u_j = log|z_j|`, `θ_j = arg z_j`
> (`eq:acyclic-ltor-split`'s complementary term is `∑_{j,l∉I} K_{jl} u_j dθ_l`).
> "On the initial torus, `Im Ω = ∑_{j,l} K_{jl} du_j ∧ dθ_l`."

### Judgement — index placement, factor, sign

* **Coefficient:** `(S.K i j : ℝ)`, the rational `K = E D̃` cast to `ℝ`, not
  `S.B` and not `S.E`. **[elab]** the definition unfolds by `rfl`.
* **Index placement:** the **first** index of `K` carries `log‖a_i‖ = u_i`, the
  **second** carries `dθ_j`. That is `u^T K dθ` and not `dθ^T K u = -u^T K dθ`.
  The same placement appears in the blueprint's own split
  (`∑_{j,l} K_{jl} u_j dθ_l`) and is what makes §4's contraction come out as
  `K^T u̇ = K^T u + ∂_θ H` rather than its negative.
* **Factor ½:** absent, as in the blueprint (the `½` belongs to `Ω`, which is a
  double sum over an antisymmetric matrix; `λ_tor` is not). The docstring states
  this and is correct.
* **Which of `u`/`θ` carries which index:** `u` the row index, `θ` the column
  index. Unambiguous and matching.
* **`d beta = Im Ω`, and its sign:** `exteriorDerivative_beta` gives
  `d beta = GlobalTwoForm.omega` pointwise on the torus (where `beta` is smooth
  and nothing more is claimed — correct, `beta` has no extension across
  `z_i = 0`), and `GlobalTwoForm.omega_torus` identifies `omega` there with
  `P.logarithmicImaginaryValue = Im Ω`. The sign is `+`. I checked the chain
  that pins it: the germ `logarithmicPrimitive S b` (`:72`) is the affine model
  `∑_{i,j} K_{ij}(log‖b_i‖ + (z_i).re) dθ_j`, and **[elab]**
  `extDeriv (logarithmicPrimitive S b) z = GlobalTwoForm.matrixForm S`
  (`extDeriv_logarithmicPrimitive`, `:137`). Since `matrixForm_real` is
  `∑ K_{ij} du_i ∧ dθ_j`, this *also* fixes the library's exterior-derivative
  normalisation: `d(∑ K_{ij} u_i dθ_j) = ∑ K_{ij} du_i ∧ dθ_j` with no factor
  `2` or `½`. That is the convention used throughout §4.

**PASS.**

---

## 3. `TorusCorrection.H`, summand by summand — PASS; `H_Lean = +H_ref`

### Lean (`ClusterSkeleton/TorusCorrection.lean:68-96`)

```lean
def A (p : S.Point) (j : Fin d) : ℝ := Real.log ‖p.a j‖
def rowLog (p : S.Point) (i : Fin d) : ℝ := ∑ j : Fin d, (S.B i j : ℝ) * A S p j
def angular (δ : ℝ) (p : S.Point) (i : Fin d) : ℝ :=
  PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter p i))

def H (ε κ δ : ℝ) (p : S.Point) : ℝ :=
  ∑ i ∈ S.mutable, (S.D i : ℝ) * (PrimitiveCutoffs.radial ε κ (A S p i) *
    DominanceCutoff.dominance S ε i (A S p) * PrimitiveCutoffs.rho (rowLog S p i) *
      angular S δ p i)
```

### Blueprint (`proof-blueprint.tex`, proof of `thm:acyclic-skeleton`)

> `u_j = log|z_j|`, `θ_j = arg z_j`, `v_i = log|t_i| = c_i(u)`,
> `η_i = arg t_i = c_i(θ)`,
> `χ_i := ∏_{j∈M: B_{ji}≠0} ϑ(u_i − u_j)`,
> `H := ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)`,
> `λ_ac := λ_tor + dH`.
> Cutoffs: `h ≤ 0`, `0 ≤ h' ≤ 1`, `h(u) = u + a (u ≤ −L)`, `h = 0` near
> `[0,∞)`; `ρ ∈ C_c^∞(ℝ,[0,1])`, `ρ = 1` near `0`;
> `supp β ⊂ (π−ε, π+ε)`, `β(η) = η − π` near `π`, `(η−π)β(η) ≥ 0`, `β' ≤ 1`.
> `ϑ` smooth nonincreasing, `= 1` on `(−∞,−1]`, `= 0` on `[0,∞)`.

### Judgement — summand by summand

| blueprint factor | Lean factor | verified identification |
| --- | --- | --- |
| `d_i` | `(S.D i : ℝ)` | **present in every summand**, outside the whole product; **[elab]** the whole `H` unfolds to the displayed weighted formula by `rfl` (`manuscript_formula` is also `rfl`) |
| `h(u_i)` | `PrimitiveCutoffs.radial ε κ (A S p i)` | `radial ε κ A = -radialLength ε κ * transitionPrimitive ((-A-2ε)/radialLength ε κ)` with `radialLength ε κ = 2(κ-2ε)`; the library proves `radial_nonpos` (`h ≤ 0`), `radial_deriv_nonneg`/`radial_deriv_le_one` (`0 ≤ h' ≤ 1`), `radial_eq_zero` for `A ≥ -2ε` (`h = 0` near `[0,∞)`), `radial_tail : radial ε κ A = A + κ` for `A ≤ -radialLength ε κ - 2ε` (`h(u) = u + a` for `u ≤ -L`), `radial_gt : A < radial ε κ A` for `A < 0` (`u - h(u) < 0`). **So `a = κ` and `L = radialLength ε κ + 2ε = 2κ - 2ε`**, and `L > a` holds under `GlobalPrimitive`'s own `2ε + 1 ≤ κ` (then `κ > 2ε`, so `2κ - 2ε > κ`). The argument is `u_i`, not `v_i`. ✓ |
| `χ_i = ∏_{j∈M: B_{ji}≠0} ϑ(u_i − u_j)` | `DominanceCutoff.dominance S ε i (A S p) = ∏_{j ∈ mutableNeighbors S i} chi ε (A i − A j)` with `mutableNeighbors S i = S.mutable.filter (S.B i · ≠ 0)` | `S.B i j ≠ 0 ⟺ S.E j i ≠ 0 ⟺ B_{ji} ≠ 0`: the index set is the blueprint's **exactly** (and symmetric anyway by `E_eq_zero_iff`). The argument is `u_i − u_j`, in the blueprint's order. `chi ε x = smoothTransition((−2x−ε)/ε)` is `1` for `x ≤ −ε`, `0` for `x ≥ −ε/2`, values in `[0,1]`, i.e. `ϑ` with `1` rescaled to `ε`. ✓ |
| `ρ(v_i)` | `PrimitiveCutoffs.rho (rowLog S p i)` | `rowLog S p i = ∑_j (S.B i j : ℝ) u_j = ∑_j E_{ji} u_j = c_i(u) = v_i`. **[elab]** `rowLog S p i = ∑ j, (S.E j i : ℝ) * Real.log ‖p.a j‖` by `rfl`, and `rowLog = PrimitiveLocalization.rowLog` by `rfl`. **`rowLog = +v_i`, no sign flip.** `rho x = smoothTransition (2 − x²)`: values in `[0,1]`, `= 1` for `|x| ≤ 1`, `= 0` for `|x| ≥ 2`, compact support. ✓ |
| `β(η_i)` | `PrimitiveCutoffs.vartheta δ (Complex.arg (−exchangeCharacter p i))` | `exchangeCharacter p i = ∏_j a_j^{E_{ji}} = z^{c_i} = t_i` (**[elab]** `exchangeCharacter_eq_zpow_product`), so `arg(−t_i)` is the principal representative of `η_i − π`; `vartheta δ T = arcsin(sin T) · angularWindow δ T` is supported near `T = 0` (`vartheta_zero_of_radius_le`, `vartheta_support_principal : \|T\| < δ`), equals `T` near `0` (`vartheta_eq_self`), is `2π`-periodic and representative-independent (`vartheta_periodic`, `vartheta_representative_independent`), satisfies `T · vartheta δ T ≥ 0` (`vartheta_local_sign`) and `deriv ≤ 1` (`vartheta_deriv_le_one`). Writing `β(η) := vartheta δ (η − π)` reproduces every blueprint clause, including `supp β ⊂ (π−δ, π+δ)` and `(η−π)β(η) ≥ 0`. **`angle = +(η_i − π)`, no sign flip.** ✓ |

### Definite answer: `H_Lean = +H_ref`

Both inner sign inversions of the accepted baseline are gone. In the baseline
(`docs/skeleton-audit.md` §1.3–1.4) `rowLog = −v_i` and
`arg(−exchangeCharacter) = −(η_i − π)`; `rho` is even and `vartheta δ` is odd, so
the two flips multiplied to `H_Lean = −H_ref`, which the baseline's
`alpha = beta − dH` cancelled a second time. Stage A's column exponents removed
*both* flips (`exchangeCharacter = t_i`, verified above), so

```
H_Lean = ∑_{i∈M} d_i · h(u_i) · χ_i · ρ(v_i) · β(η_i) = H_ref ,   literally.
```

**[elab]** the two parity facts the comparison rests on were machine-checked:
`rho (-x) = rho x` (closed by `simp [PrimitiveCutoffs.rho]`) and
`vartheta δ (-T) = -vartheta δ T` (closed by
`simp [vartheta, angularWindow, Real.sin_neg, Real.cos_neg, Real.arcsin_neg]`).
**PASS.**

> **RISK R5 (stage C, integration).** *Neither parity fact is a statement in the
> Lean library.* `grep` over `ClusterSkeleton/PrimitiveCutoffs.lean` finds no
> `rho_neg`/`rho_even`/`vartheta_neg`/`vartheta_odd`. The entire O1/O2 sign
> decision — and the `D = I` recovery argument of item 7, where `H` really is
> negated — is carried by these two facts on paper only. Both are one-`simp`
> lemmas (Appendix A proves them verbatim). **Minimal fix:** add
> `theorem PrimitiveCutoffs.rho_neg (x : ℝ) : rho (-x) = rho x` and
> `theorem PrimitiveCutoffs.vartheta_neg (δ T : ℝ) : vartheta δ (-T) = -vartheta δ T`
> to `PrimitiveCutoffs.lean` (additive, no statement changed). **Affects stage C:**
> not for correctness of the weighted chain (which never needs them), but
> acceptance check 2 (`D = I` recovery) cannot be *proved* in Lean beyond the
> existential without them.

---

## 4. `alpha := beta + dH`, and the Liouville field derived by hand — PASS

### 4a. The definition

#### Lean (`ClusterSkeleton/TorusPrimitive.lean:53-55`, `TorusCorrection.lean:170`)

```lean
def alpha (H : S.Point → ℝ) : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  beta S hdet + covectorForm _ (differentialCovector _ H)

def alpha (ε κ δ : ℝ) : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  TorusPrimitive.alpha S hdet (H S ε κ δ)
```

#### Blueprint

> `λ_ac := λ_tor + dH`. "Our sign convention is `ι_Z dλ = λ`."

#### Judgement

`+`, matching `λ_ac = λ_tor + dH`, with `beta = λ_tor` (item 2) and
`H_Lean = +H_ref` (item 3). **[elab]** `alpha S hdet H = beta S hdet +
covectorForm _ (differentialCovector _ H)` by `rfl`: the plus sign is
definitional, not a derived simp lemma, so it cannot drift. Therefore
`TorusCorrection.alpha = λ_ac` **on the nose**, and
`exteriorDerivative_alpha : d (alpha) p = GlobalTwoForm.omega S hdet p`
(`TorusCorrection.lean:188`) is `dλ_ac = Im Ω`. **PASS.**

### 4b. The Liouville field, derived from the Lean definitions

Everything below is derived from the Lean definitions quoted above
(`matrixForm_real`, `evalOne_beta`, `H`, `alpha`), **not** from the blueprint;
the blueprint is only the target of comparison.

Fix `p ∈ initialTorus S`. The logarithmic tangent frame is
`radialTangent S hdet p hp i` and `angularTangent S hdet p hp i`
(`TorusLiouvilleDynamics.lean:58-70`), the preimages of `Pi.single i 1` and
`Pi.single i Complex.I` under `TorusNondegeneracy.logarithmicTangentEquiv`;
i.e. `∂_{u_i}` and `∂_{θ_i}`. Write `Z` for the Liouville field
(`TorusLiouvilleDynamics.Z`, the `liouvilleVector` of `TorusCorrection.alpha`),
and `logarithmicComponents p j = dlog a_j (Z) = u̇_j + i θ̇_j`.

**(i) `Im Ω` in the frame.** By `matrixForm_real` together with
`logarithmic_germ`, on the torus
`Im Ω = ∑_{k,l} K_{kl} du_k ∧ dθ_l` with `(α ∧ β)(v,w) = α(v)β(w) − α(w)β(v)`.
Contracting, `ι_Z(du_k ∧ dθ_l) = u̇_k dθ_l − θ̇_l du_k`, so

```
ι_Z Im Ω = ∑_l (∑_k K_{kl} u̇_k) dθ_l − ∑_k (∑_l K_{kl} θ̇_l) du_k .
```

**(ii) `alpha` in the frame.** By `evalOne_beta`,
`beta = ∑_{k,l} K_{kl} u_k dθ_l`; and `dH = ∑_l ∂_{θ_l}H dθ_l + ∑_k ∂_{u_k}H du_k`.
So `alpha = ∑_l [(∑_k K_{kl} u_k) + ∂_{θ_l}H] dθ_l + ∑_k ∂_{u_k}H du_k`.

**(iii) The two contraction equations.** Equating coefficients in
`ι_Z Im Ω = alpha` — concretely, evaluating both sides at `angularTangent_l`
and then at `radialTangent_k` —

```
(A)   ∑_k K_{kl} u̇_k = ∑_k K_{kl} u_k + ∂_{θ_l} H          i.e.  K^T u̇ = K^T u + ∂_θ H
(B)   − ∑_l K_{kl} θ̇_l = ∂_{u_k} H                          i.e.  − K θ̇ = ∂_u H
```

These are, verbatim, the blueprint's
"`K^T u̇ = K^T u + ∂_θ H`, `−K θ̇ = ∂_u H`".

**(iv) `∂_θ H` from the Lean `H`.** In `H = ∑_{i∈M} d_i · radial(u_i) · χ_i(u) ·
ρ(rowLog_i) · vartheta δ(angle_i)` only `angle_i` depends on `θ`, through
`angle_i ≡ η_i − π` with `η_i = c_i(θ) = ∑_l (S.B i l) θ_l = ∑_l E_{li} θ_l`; so
`∂ angle_i/∂θ_l = S.B i l` (the same orientation the library uses in
`logarithmicHamiltonian`, whose angular perturbation is
`+∑_j (S.B i j : ℝ) * (z j).im`). Putting
`a_i := radial(u_i) χ_i ρ(v_i) · vartheta' δ(angle_i) = h(u_i) χ_i ρ(v_i) β'(η_i)`
for `i ∈ M` and `a_j := 0` for `j ∈ F`,

```
∂_{θ_l} H = ∑_{i∈M} d_i a_i (S.B i l) = − ∑_{i∈M} a_i K_{il} = − ∑_k K_{kl} a_k ,
```

using `Seed.K_eq_neg_D_mul_B : S.K i j = -(S.D i) * (S.B i j)`, i.e.
`d_i (S.B i l) = −K_{il}` (`PrimitiveResidual.sum_K_row_real` is its `ℝ`-cast).
This is the same equation as the blueprint's `∂_θ H = K ∑_i a_i e_i`: the
blueprint pairs over the *second* index of `K` via `d_i c_i = K e_i`, the Lean
row `S.B i l` pairs over the first, and the two differ by `K^T = −K`.

**(v) Radial equation.** Substituting (iv) into (A), for every column `l`

```
∑_k K_{kl} u̇_k = ∑_k K_{kl} u_k − ∑_k K_{kl} a_k ,   i.e.   ∑_k K_{kl}(u̇_k − u_k + a_k) = 0 .
```

`det K = ∏ d_i ≠ 0` (`TorusNondegeneracy.complexMatrix_det`,
`isUnit_complexMatrix_det`, from `Seed.det_K_of_unimodular`), so `K^T` is
injective and `u̇ = u − a`:

```
u̇_j = u_j                                              (j ∈ F)
u̇_i = u_i − h(u_i) χ_i ρ(v_i) β'(η_i)                 (i ∈ M)
```

— **`eq:acyclic-flow`, verbatim, sign included, with the weights `d_i`
cancelling**: they enter only through `d_i a_i (S.B i l) = −a_i K_{il}` and are
absorbed by the `K^T` that is then cancelled. With the opposite choice
`alpha = beta − dH` the correction term would come out as `u̇_i = u_i + h(u_i)…`,
and since `h ≤ 0` the blueprint's `u̇_i ≤ u_i − h(u_i) < 0` on `{u_i < 0}`
(`eq:acyclic-radial`) would fail outright. **The sign in the tree is the right
one.**

**(vi) Angular equation.** From (B) and
`∑_l K_{il} x_l = −d_i ∑_l (S.B i l) x_l` (`sum_K_row_real`), with
`c_i(θ̇) = η̇_i`:

```
− ∑_l K_{il} θ̇_l = d_i η̇_i = ∂_{u_i} H   ⟹   η̇_i = (1/d_i) ∂_{u_i} H ,
```

the blueprint's `eq:acyclic-angle-flow` first half, **and the only place a weight
survives**. Applying `c_i` to (v) gives the second half,
`v̇_i = v_i − ∑_{k∈M} B_{ki} a_k` with `B_{ki} = E_{ki} = S.B i k`.

**(vii) At a node.** For `i ∈ I = {j : z_j(q) = 0}` the blueprint's neighbourhood
`W` has `h(u_i) = u_i + a`, `χ_i = ρ(v_i) = β'(η_i) = 1`, so `a_i = u_i + κ`
(Lean's `a` is `κ`, item 3) and `u̇_i = u_i − (u_i + κ) = −κ`, i.e. the
blueprint's `u̇_i = −a`; and `∂_{u_i}H = d_i(η_i − π)` from
`eq:acyclic-H-near` / `RegularCorrection.singularH`, so `η̇_i = η_i − π`,
whence `ṫ_i = t_i Log(−t_i)` and `Z|z_i|² = −2κ|z_i|²`
(`eq:acyclic-divisor-flow`). ✓

### 4c. The shapes stage C must prove

For the stage-C owner, written against the four declarations named in the
mission. `TorusLiouvilleDynamics` is **unchanged from `e62c101`** at `6cdcef7`
(its first error is `omega_real`'s `S.B` coefficient), so these are *targets*,
not current statements.

**`omega_real` (lines 115–130) — `S.B ↦ S.K`, both sums:**

```lean
theorem omega_real (p : S.Point) (hp : p ∈ initialTorus S) (v w : … .Tangent p) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p v w =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) *
        (… .coordinateDifferential i p v / p.a i).re *
        (… .coordinateDifferential j p w / p.a j).im) -
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) *
        (… .coordinateDifferential i p w / p.a i).re *
        (… .coordinateDifferential j p v / p.a j).im)
```

**`radial_matrix_equation` (lines 402–416) — `S.B ↦ S.K` at all three
occurrences, minus sign preserved**; this is (v) before cancelling `K^T`:

```lean
theorem radial_matrix_equation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (j : Fin d) :
    (∑ i : Fin d, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p i).re) =
      (∑ i : Fin d, (S.K i j : ℝ) * TorusCorrection.A S p i) -
      ∑ i ∈ S.mutable, amplitude S ε κ i (TorusCorrection.A S p) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
          (S.K i j : ℝ)
```

No `(S.D i : ℝ)` appears: the weight of the `H` summand is consumed by
`d_i a_i (S.B i j) = -a_i (S.K i j)` (`Seed.K_eq_neg_D_mul_B`). `amplitude`
(`TorusLiouvilleDynamics.lean:62`) stays **unweighted**
(`radial ε κ (a i) * dominance S ε i a * rho (∑ j, (S.B i j : ℝ) * a j)`).

**`mutable_radial_equation` (439–447) and `frozen_radial_equation` (449–453) —
verbatim the baseline statements, no change at all**:

```lean
theorem mutable_radial_equation … (hi : i ∈ S.mutable) :
    (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i -
      PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) *
        DominanceCutoff.dominance S ε i (TorusCorrection.A S p) *
        PrimitiveCutoffs.rho (TorusCorrection.rowLog S p i) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i))

theorem frozen_radial_equation … (hi : i ∉ S.mutable) :
    (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i
```

and likewise `real_logarithmicComponents` and `radialCorrection` are unchanged.
This is `eq:acyclic-flow` / `eq:acyclic-radial`. Three things make the statement
survive the generalization unchanged: the weights cancel (v); `rowLog` is now
`+v_i` so `rho (rowLog …)` is `ρ(v_i)` **literally** rather than through
evenness; and `arg(-exchangeCharacter p i)` is now `+(η_i − π)` so
`deriv (vartheta δ) (…)` is `β'(η_i)` **literally** rather than through
evenness of `vartheta'`. The proof change is `det B = 1` → `IsUnit (det K)`:
use `TorusNondegeneracy.isUnit_complexMatrix_det` with
`Matrix.vecMul_injective_of_isUnit`, **not** a determinant equal to `1`.

**`angular_equation` (132–143) — the minus is new.** Two equivalent weighted
forms; (vi) says which:

```lean
-- K form (matches the `omega_real` coefficient; a MINUS appears)
theorem angular_equation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (∑ j : Fin d, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      -differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i)

-- B form (keeps the baseline LHS; a factor 1/d_i appears, sign unchanged)
    (∑ j : Fin d, (S.B i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      (S.D i : ℝ)⁻¹ * differentialCovector … (TorusCorrection.H S ε κ δ) p
        (radialTangent S hdet p hp i)
```

i.e. `η̇_i = (1/d_i) ∂_{u_i} H` with the blueprint's `+`. The same `±`/`1/d_i`
decision propagates to `angular_equation_logarithmic`,
`angular_equation_partial_deriv` and
`GlobalLiouvilleField.angular_equation_partial_deriv`. This confirms option
**O1** of `docs/weighted-stage-c-map.md` §4 and settles all four of its
"must not assume" items:
(1) `radial_matrix_equation` keeps its baseline minus sign;
(2) `angular_equation` acquires a minus in the `K` form (equivalently `1/d_i` in
the `B` form); (3) `TorusCorrection.angular` and
`(PrimitiveLocalization.nodeLog q i).im` are **not** negated, so
`LocalAngularDynamics.angularRhs`'s zero-stratum branch keeps its sign and gains
`(S.D i : ℝ)`; (4) `η̇_i = +(1/d_i) ∂_{u_i} H`.

Finally the two role-(g) germs:

```lean
theorem differential_H_angular … (j : Fin d) :
    differentialCovector … (TorusCorrection.H S ε κ δ) p (angularTangent S hdet p hp j) =
      ∑ i ∈ S.mutable, (S.D i : ℝ) * amplitude S ε κ i (TorusCorrection.A S p) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
          (S.B i j : ℝ)
    -- equivalently  = -∑ i ∈ S.mutable, amplitude … * deriv … * (S.K i j : ℝ)

theorem differential_H_radial … (j : Fin d) :
    differentialCovector … (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp j) =
      ∑ i ∈ S.mutable, (S.D i : ℝ) * TorusCorrection.angular S δ p i *
        fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S p) (Pi.single j 1)
```

**PASS.**

---

## 5. Node block, `eta`, and the extension across the zero locus — PASS

### 5a. `beta_decomposition` is `eq:acyclic-ltor-split`

#### Lean (`ClusterSkeleton/PrimitiveResidual.lean:17-22, 27-30, 92-99`)

```lean
def tau (i : Fin d) (p : S.Point) : … →L[ℝ] ℝ :=
  ∑ j : Fin d, (S.B i j : ℝ) • TorusPrimitive.angleCovector S hdet j p
def logRow (i : Fin d) (p : S.Point) : ℝ := ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖
def residual (I : Finset (Fin d)) : … .Form 1 :=
  covectorForm _ (fun p => ∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ,
    ((S.K i j : ℝ) * Real.log ‖p.a i‖) • TorusPrimitive.angleCovector S hdet j p)

theorem beta_decomposition (I : Finset (Fin d)) (hI : S.Independent I) :
    TorusPrimitive.beta S hdet = residual S hdet I +
      covectorForm _ (fun p : S.Point => ∑ i ∈ I, (-(S.D i : ℝ)) •
        (Real.log ‖p.a i‖ • tau S hdet i p -
          logRow S i p • TorusPrimitive.angleCovector S hdet i p))
```

#### Blueprint (`eq:acyclic-ltor-split`)

> `λ_tor = ∑_{i∈I} d_i (v_i dθ_i − u_i dη_i) + ∑_{j,l∈(M⊔F)\I} K_{jl} u_j dθ_l`

#### Judgement

`tau i = ∑_j E_{ji} dθ_j = c_i(dθ) = dη_i` (and this is *proved*, not asserted:
`tau_eq_nodeAngle_differential`, `:227`, identifies `tau i p` with
`d(Im Log(1 − x_i y_i))`, and `node_argument`, `:213`, proves
`1 − x_i y_i = −∏_j a_j^{B_{ij}} = −t_i`); `logRow i = v_i`;
`angleCovector i = dθ_i`; `log‖a_i‖ = u_i`. So the `I`-block is
`∑_{i∈I} (−d_i)(u_i dη_i − v_i dθ_i) = ∑_{i∈I} d_i (v_i dθ_i − u_i dη_i)` and
the complementary block is `∑_{i,j∈Iᶜ} K_{ij} u_i dθ_j`. **Term for term the
blueprint's split.** The supporting `split_sum` (`:33`) I re-derived
independently: splitting `∑_{all}` as `∑_{i∈I,all j} + ∑_{i∈Iᶜ,j∈I} +
∑_{i,j∈Iᶜ}`, the middle piece becomes `−∑_{i∈I}(∑_j K_{ij}A_j)T_i` using `K` skew
and `∑_{j∈I}K_{ij}A_j = 0` (independence: `K i j = E i j · D j` and `E i j = 0`
on `I`), which is exactly the Lean bracket. **PASS.**

**The six `⁻¹` sites of `PrimitiveResidual` (lines 138, 165, 192, 195, 197, 238)
are all `(a j)⁻¹` / `(q z j)⁻¹` coordinate inverses in `dlog a_j = da_j / a_j`.**
Verified by `grep -n '⁻¹'`: none is an inverse of `S.B` or of `K`, so neither
role (f) nor role (e) arises in this module and no weight applies. B2's claim
confirmed.

### 5b. `NodePrimitiveCancellation.cancellation` and the sign of `block`

#### Lean (`ClusterSkeleton/NodePrimitiveCancellation.lean:34-36, 130`)

```lean
def lambda (k : ℝ) (p : E) : Covector :=
  -(Complex.imCLM.comp (nodeLogQuotient p • du + (k : ℂ) • dL p))

theorem cancellation (k : ℝ) {p : E} (hp : p ∈ nodeLogDomain) (hu : p.1 ≠ 0) :
    A p • fderiv ℝ T p - S p • dtheta p -
      fderiv ℝ (fun q => (A q + k) * T q) p = lambda k p
```

with `L p = Complex.log (1 − p.1 * p.2)`, `A p = Real.log ‖p.1‖`,
`S p = (L p).re`, `T p = (L p).im`, `dtheta p = Im(p.1⁻¹ du)`; and
`NativeNodePrimitive.nodeMap i q = (q.a i, normalizedPartner q i) = (x_i, y_i)`
with `y_i = z_i'/P_i^-` the reference partner.

#### Blueprint (before `thm:acyclic-skeleton`; `eq:acyclic-H-near`)

> "The node primitive is `v dθ − u dη + d(hρβ)`."
> `λ_ac = ∑_{j,l∉I} K_{jl} u_j dθ_l + dH' + ∑_{i∈I} d_i (v_i dθ_i + (η_i−π) du_i + a dη_i)`,
> using `v_i dθ_i − u_i dη_i + d((u_i+a)(η_i−π)) = v_i dθ_i + (η_i−π) du_i + a dη_i`.
> `H = ∑_{i∈I} d_i (u_i + a)(η_i − π) + H'`.

#### Judgement

On the node, `L = Log(1 − x_i y_i) = Log(−t_i) = v_i + i(η_i − π)` (proved:
`PrimitiveLocalization.neg_character_node` + `rowLog_eq_log_re`, re-exported as
`NativeNodePrimitive.node_real_logRow : NodePrimitiveCancellation.S (nodeMap S i q)
= PrimitiveResidual.logRow S i q`). So `A = u_i`, `S = +v_i`, `T = +(η_i − π)`,
`dT = dη_i`, `dtheta = dθ_i`, and `cancellation` reads

```
u_i dη_i − v_i dθ_i − d((u_i + κ)(η_i − π))  =  lambda κ ,
```

i.e. **`lambda κ` is minus the blueprint's per-node primitive block**
`v_i dθ_i − u_i dη_i + d((u_i + κ)(η_i − π))`. (The baseline had `+`, because its
`T = −(η_i − π)` and `S = −v_i`.) `lambda_zero`
(`lambda κ (0,v) t = (1+κ)(v·t.1).im`, **[elab]**) is the same statement on the
divisor: the blueprint's extension there is
`Im(Log(1−z_iy_i)/z_i · dz_i) + a d arg(1−z_iy_i) → −(1+a) Im(y_i dz_i)`, whose
negative is `+(1+κ) Im(y_i dz_i)`. ✓ consistent.

```lean
def block (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I) : … .Form 1 :=
  covectorForm _ (fun q => ∑ i : I,
    (S.D i.val : ℝ) • lambda S hdet κ ⟨i.val, hI.1 i.property⟩ q)   -- NativeNodePrimitive.lean:75
```

The weight `(S.D i : ℝ)` multiplies the **whole** `lambda`, i.e. the pair
`(v_i dθ_i − u_i dη_i)` *and* `d(affine_i)` together — which is what the
blueprint's `∑_{i∈I} d_i(…)` and `H = ∑_{i∈I} d_i(u_i+a)(η_i−π) + H'` require,
given that `PrimitiveLocalization.affineCorrection` is **unweighted**.
`block_torus` (`:240`) restates it in the torus frame with that factor;
`block_empty` is `0`. **PASS.**

### 5c. `eta = residual − block + regularForm`

#### Lean (`ClusterSkeleton/LocalPrimitive.lean`)

```lean
def eta (ε κ δ : ℝ) (p : S.Point) : … .Form 1 :=
  PrimitiveResidual.residual S hdet p.zeroSet -
    NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent +
    RegularCorrection.regularForm S hdet p.zeroSet ε κ δ
```

```lean
def surviving (I : Finset (Fin d)) : Finset S.Mutable :=                -- RegularCorrection.lean:15
  Finset.univ.filter fun j => (j : Fin d) ∉ I ∧ ∀ i ∈ I, S.B j i = 0
def regularH (I : Finset (Fin d)) (ε κ δ : ℝ) (p : S.Point) : ℝ :=      -- :25
  ∑ j ∈ surviving S I, (S.D j : ℝ) * correction ε κ δ j p
def singularH (I : Finset (Fin d)) (κ : ℝ) (p : S.Point) : ℝ :=         -- :202
  ∑ j ∈ (Finset.univ.filter fun j : S.Mutable => (j : Fin d) ∈ I),
    (S.D j : ℝ) * affineCorrection κ j p
theorem H_split … : TorusCorrection.H S ε κ δ q =
    singularH p.zeroSet κ q + regularH S p.zeroSet ε κ δ q             -- :207
def regularForm (I : Finset (Fin d)) (ε κ δ : ℝ) : … .Form 1 :=
  covectorForm _ (differentialCovector _ (regularH S I ε κ δ))         -- :173
```

#### Judgement — both signs are forced, and the derivation closes

Near `q` with `I = q.zeroSet`, `H_split` is `eq:acyclic-H-near`:
`surviving S I = {j ∈ M \ I : E_{ij} = 0 ∀ i ∈ I}` (**[elab]**
`mem_surviving` restated as `(j : Fin d) ∉ I ∧ ∀ i ∈ I, S.E i j = 0` elaborates,
since `S.B j i = S.E i j`), which is the blueprint's "`H'` is the sum of the
summands of `H` with index `k ∈ M\I` such that `B_{ik} = 0` for all `i ∈ I`";
and `singularH = ∑_{i∈I} d_i (u_i + κ)(η_i − π)` because
`affineCorrection κ i p = (log‖a_i‖ + κ) · (nodeLog p i).im` (**[elab]** by `rfl`)
with `(nodeLog).im = +(η_i − π)`. Therefore, from `alpha = beta + dH`,

```
alpha = residual_I + ∑_{i∈I} d_i (v_i dθ_i − u_i dη_i)        [beta_decomposition]
        + ∑_{i∈I} d_i d((u_i+κ)(η_i−π)) + dH'                 [H_split]
      = residual_I + ∑_{i∈I} d_i [v_i dθ_i − u_i dη_i + d(affine_i)] + d(regularH)
      = residual_I − ∑_{i∈I} d_i (lambda κ)_i + d(regularH)   [5b]
      = residual − block + regularForm .
```

**Both signs flip together with `alpha = beta + dH`, and they did.** This is not
only consistent on paper: `eta_eq_torus` *proves*
`eta S hdet ε κ δ p q = TorusCorrection.alpha S hdet ε κ δ q` for
`q ∈ neighborhood ε κ δ p ∩ initialTorus S`, which is a machine-checked
cross-check of the whole sign triple (`alpha`'s `+dH`, `eta`'s `−block`, and
`eta`'s `+regularForm`): flipping any one of the three alone would break it.
**[elab]** `eta`'s definition unfolds by `rfl`; `eta_eq_torus` has axioms
`[propext, Classical.choice, Quot.sound]` only.

**`eta_zero_partners`** (`residual + regularForm` where all partners vanish) is
also right: `lambda_boundary` gives
`lambda κ i q v = (1+κ)(y_i · da_i(v)).im`, which is `0` when `y_i = 0`, so
`block = 0` there. The blueprint's extension
`Im(Log(1−z_iy_i)/z_i · dz_i) + a d arg(1−z_iy_i)` likewise vanishes at
`y_i = 0`. (The baseline read `residual − regularForm`; the flip is the same
one.) ✓

**Extension across the zero locus.** The blueprint's argument is: the first two
terms of `λ_ac` are smooth on `W`, and the per-node block equals
`Im(Log(1−z_iy_i)/z_i dz_i) + a d arg(1−z_iy_i)`, smooth because
`Log(1−z_iy_i)/z_i` is holomorphic with value `−y_i` on `{z_i = 0}`. In Lean the
corresponding facts are `contDiffAt_residual_inChart` (smooth on
`candidateChartLocus S I`, i.e. including `z_i = 0` for `i ∈ I`),
`NativeNodePrimitive.contDiffAt_block_inChart` (whose `lambda` is built from
`nodeLogQuotient`, the library's `Log(1−uv)/u` with the removable singularity
already handled in `NodeLogExtension`), `RegularCorrection.regularForm_smooth`
(the `H'` part, whose arguments involve only units on `U_I`), and
`LocalPrimitive.locallySmooth_eta` assembling them. The claim that the primitive
extends is therefore made on the same three pieces, in the same order, as the
blueprint. **PASS.**

### 5d. `PrimitiveLocalization.correction` / `affineCorrection` versus the weighted `H`

```lean
def correction (ε κ δ : ℝ) (i : S.Mutable) (p : S.Point) : ℝ :=         -- :32
  radial ε κ (logNorms S p i) * dominance S ε i (logNorms S p) *
    rho (rowLog p i) * vartheta δ (angle p i)
def affineCorrection (κ : ℝ) (i : S.Mutable) (p : S.Point) : ℝ :=       -- :37
  (logNorms S p i + κ) * (nodeLog p i).im
theorem H_eq_sum (ε κ δ : ℝ) (p : S.Point) :                            -- RegularCorrection.lean:191
    TorusCorrection.H S ε κ δ p = ∑ j : S.Mutable, (S.D j : ℝ) * correction ε κ δ j p
```

**Consistent.** Both scalars are **unweighted**, and *every* sum that consumes
them supplies `(S.D j : ℝ)`: `H_eq_sum`, `regularH`, `singularH`,
`LocalPrimitive.singularH_eq_sum`, `differential_H_eq_sum`,
`NativeNodePrimitive.block`. **[elab]** `correction`'s and
`affineCorrection`'s unfoldings hold by `rfl`, and `H_eq_sum` type-checks as
displayed. This is the right division of labour: the blueprint's `d_i` sits
outside the per-index product, and `PrimitiveLocalization`'s `correction_eq_affine`
/ `correction_eventuallyEq` / `correction_mfderiv_eq` are weight-free statements
about one index that stay valid verbatim. The only module-level change in
`PrimitiveLocalization` is a proof fix in `rowLog_eq_log_re`
(`simp only [… Seed.B_apply]`, the stage-A transparency gotcha); **every
statement in that file is byte-identical to `e62c101`**, which is correct, because
`rowLog`'s *meaning* changed (`−v_i → +v_i`) while its text did not — a point the
convention table of item 8 records.

`PrimitiveLocalization.plateaus` is also worth naming as the Lean form of the
blueprint's choice of `W`: it proves `dominance = 1`, `rho (rowLog) = 1`,
`vartheta δ (angle) = angle` and `radial ε κ (logNorms) = logNorms + κ` on
`neighborhood ε κ δ p ∩ initialTorus S`, i.e. the blueprint's
"`ρ(v_i)=1`, `β(η_i)=η_i−π`, `u_i ≤ −L`, `h(u_i)=u_i+a`, `χ_i=1`"; and
`adjacent_dominance_zero` is its "`χ_j = 0` there, because `χ_j` has the factor
`ϑ(u_j − u_i)` and `u_j − u_i ≥ 1`". **PASS.**

---

## 6. `GlobalPrimitive`'s final statement — PASS, with RISK R6

### Lean (`ClusterSkeleton/GlobalPrimitive.lean`, byte-unchanged from `e62c101` except `evalOne_alpha`)

```lean
theorem exists_global_primitive :
    ∃ (ε κ δ : ℝ) (theta : (SmoothAtlas.presentation S hdet).manifold.Form 1),
      0 < ε ∧ 2 * ε + 1 ≤ κ ∧ 0 < δ ∧ δ < Real.pi ∧
      (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta ∧
      (∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p) ∧
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta =
        GlobalTwoForm.omega S hdet ∧
      (∀ p, (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
        ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta) p)
```

plus `exteriorDerivative_alpha` (whole-form equality),
`nondegenerate_exteriorDerivative_alpha`,
`isSymplecticOn_exteriorDerivative_alpha … Set.univ`, `alpha_eq_torus`,
`alpha_eq_eta`, `eq_alpha_of_torus` (uniqueness among smooth extensions by
density).

### Blueprint (`thm:acyclic-skeleton`)

> "There is a Liouville form `λ_ac` of `Im Ω` on `A(B̃)` such that
> `Λ = Skel(Z_{λ_ac}) = ⋃_{I⊂M independent} Λ_I`, …"
> and `target-theorem.tex`, "Formalization target": "Construct the smooth
> presentation, the extended symplectic form, the primitive, and a jointly
> smooth flow defined for every real time."

### Judgement

* **`d alpha = Im Ω`:** present twice — as a whole-form equality
  (`exteriorDerivative_alpha`, proved by density from the torus identity) and
  inside the existential. `GlobalTwoForm.omega` is the weighted `Ω` of item 1,
  so this is `dλ_ac = Im Ω`. ✓
* **Quantifier:** `∀ {d} (S : Seed d) (hdet : S.Unimodular)`, i.e. an arbitrary
  integral `E` with `det E = 1` and an arbitrary positive rational `D` with
  `E D̃` skew — **the PDF's input, with no `d_i = 1`**. **[elab]**
  `#check` on the published commit prints exactly the statement above.
* **Relation to `H`:** the clause
  `∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p` pins
  `theta = beta + dH` on the initial torus, and since the torus is dense
  (`dense_initialTorus`) and `theta` is smooth, `eq_alpha_of_torus` makes
  `theta` **unique**. So the relation to `H` is fully determined by the
  statement, even though it is asserted only on the torus. ✓
* **Parameters:** `ε = 1`, `κ = 3`, `δ = π/2` (`concrete_parameters`), satisfying
  `0 < ε`, `2ε + 1 ≤ κ`, `0 < δ < π`. In blueprint terms `a = κ = 3` and
  `L = 2κ − 2ε = 4`, so `L > a > 0` as required. ✓
* **Clauses weakened or strengthened relative to `e62c101`:** *none.*
  `git diff e62c101 HEAD -- ClusterSkeleton/GlobalPrimitive.lean` is **four
  lines**, all inside `evalOne_alpha` (`S.B → S.K`, `-` → `+`).
  `exists_global_primitive` is byte-identical. Across all eight stage-B2 modules
  the only declaration **added** is `PrimitiveResidual.sum_K_row_real`, and no
  declaration is removed; no hypothesis is added to or removed from any
  statement (the diff consists of coefficient casts `S.B → S.K`, inserted
  `(S.D i : ℝ) *` / `•` factors, three sign flips — `alpha`, `eta`,
  `eta_zero_partners` — and proof-only repairs). Beyond the E/B/K renaming and
  the `d_i` weights there is nothing. ✓

**PASS.**

> **RISK R6 (stage C).** `exists_global_primitive` is existential in `theta`, so
> **nothing about the near-node shape of the primitive can be extracted from
> it**: the node-chart identity `alpha = residual − block + regularForm` lives in
> `GlobalPrimitive.alpha_eq_eta` + `LocalPrimitive.eta` / `eta_zero_partners`,
> which are separate theorems about the *constructed* `GlobalPrimitive.alpha`.
> Nothing in the module says anything about behaviour "at infinity" either — and
> nothing needs to: the blueprint's only global growth input is
> `|u̇_j| ≤ C(1+|u_j|)` with `C = (1+max|β'|)(1+L)`, which is stage C's
> (`PrimitiveCutoffs.radial_linear_growth`, `radial_abs_le` are already in place).
> **Minimal fix:** stage C should consume `GlobalPrimitive.alpha S hdet ε κ hδ`
> together with `alpha_eq_eta` and `eta_zero_partners` — **not**
> `exists_global_primitive` — exactly as B2's handoff advises; alternatively add a
> clause `(∀ p q, q ∈ LocalPrimitive.neighborhood S ε κ δ p → theta q =
> LocalPrimitive.eta S hdet ε κ δ p q)` to the existential. **Affects stage C:**
> yes, as a consumption discipline; it is not a defect in the statement, and the
> acceptance-check-5 reviewer must cite `alpha_eq_eta` alongside
> `exists_global_primitive`.

---

## 7. `D = I` specialization versus the `e62c101` baseline — PASS, definite

Setting: a `SkewSeed d` `S` (fields `B`, `mutable`, `skew : B i j = -B j i`,
`acyclic`), and `S.toSeed` with `E := S.B`, `D := fun _ => 1`. Compare the new
library's `beta`, `H`, `alpha` **at `S.toSeed`** with the baseline library's
`beta`, `H`, `alpha` **at `S`** (`e62c101`), the carriers being identified by
`SkewSeed.pointHomeomorph`, which is the identity on ambient values
(`pointHomeomorph_val = rfl`).

| | baseline at `e62c101` (for `S`) | new at `6cdcef7` (for `S.toSeed`) | relation |
| --- | --- | --- | --- |
| form coefficient | `(S.B i j : ℂ)` | `((S.toSeed).K i j : ℂ) = (S.B i j : ℂ)` (`SkewSeed.toSeed_K`, **[elab]**) | **equal** |
| `beta` | `∑_{i,j} (S.B i j : ℝ) u_i dθ_j` | `∑_{i,j} ((S.toSeed).K i j : ℝ) u_i dθ_j` | **equal** |
| `rowLog` | `∑_j (S.B i j : ℝ) u_j` | `∑_j ((S.toSeed).B i j : ℝ) u_j = ∑_j (S.B j i) u_j = -∑_j (S.B i j) u_j` | **negated** |
| `ρ(rowLog)` | — | — | **equal** (`rho` even) |
| `exchangeCharacter` | `∏_j a_j^{S.B i j}` | `(S.toSeed).positiveMonomial/negativeMonomial = S.negativeMonomial/S.positiveMonomial` (`SkewSeed.toSeed_positiveMonomial`, **[elab]**) `= ∏_j a_j^{-S.B i j}` | **inverted** |
| `angular = vartheta δ (arg(−χ))` | — | `arg(−1/χ_old) = arg(1/(−χ_old)) = −arg(−χ_old)` | **negated** (`vartheta δ` odd) |
| `dominance` | `∏_{j: S.B i j ≠ 0} chi ε (u_i−u_j)` | `∏_{j: (S.toSeed).B i j ≠ 0} …`, same index set (`S.B j i ≠ 0 ⟺ S.B i j ≠ 0`) | **equal** |
| `radial(u_i)` | — | — | **equal** |
| `d_i` | absent | `(S.toSeed).D i = 1` (**[elab]** `rfl`) | **equal** |
| `H` | `H_old` | `-H_old` | **negated** |
| `alpha` | `beta − dH_old` | `beta + d(−H_old) = beta − dH_old` | **equal** |

### Definite answer

**`beta` is equal, `H` is exactly negated, and `alpha` is equal** — not merely
"equal up to an exact form". So acceptance check 2 can claim **more** than the
existential `LiouvilleSkeletonTarget S.toSeed`: the constructed weighted
primitive, specialized at `D = 1, E := B`, is **pointwise the baseline's
primitive** in ambient logarithmic coordinates; hence by uniqueness of the
Liouville vector (`LiouvilleData.field_eq_liouvilleVector`) the Liouville field
is the same vector field, the flow is the same flow, and `trappedSet` — a
*forward*-orbit condition, not invariant under time reversal — is the same set.
The three sign changes compose to the identity on `alpha`: stage A inverted
`exchangeCharacter` and `rowLog`, stage B2 flipped `alpha`'s sign to compensate,
and the two cancel again under `toSeed`. (Note the double role of the parity
facts: they were used in item 3 to show `H_Lean = +H_ref` in the *general*
weighted case, and here to show `H_new = −H_old` in the *specialization*. Both
uses are sound; **R5** is that neither is a Lean statement.)

> **RISK R7 (stage C).** Two residual gaps, both inherited from the stage A
> audit's R1 and now sharpened:
> 1. The equality above is an equality of the **coordinate evaluation formulas**
>    (the right-hand side of `evalOne_alpha`), not a Lean term equality of
>    `Form 1`: the two libraries' atlases differ, because the baseline's node
>    coordinates were `(z_i, z_i'/P_i^+, 1/t_i)` and the new ones are the
>    reference's `(z_i, z_i'/P_i^-, t_i)` (`NativeNodePrimitive.nodeMap`), so
>    `Tangent p` is not literally the same type. The recovery statement must
>    therefore be stated either for `S.toSeed` directly (clauses (a)+(b)+(c) of
>    the stage A audit item 4) or after transporting the smooth structure along
>    `pointHomeomorph`. The item-7 equality is what makes the stronger claim
>    *true*; stating it needs that transport.
> 2. Proving it in Lean needs `rho_neg` and `vartheta_neg` (**R5**).
> **Minimal fix:** state recovery as (a) the instantiation, (b) the torus anchor
> written with the old matrix (immediate from `toSeed_K`), (c) the transported
> objects; and record this item-7 table in the handoff so the stage-C owner does
> not settle for the existential when the pointwise identity is available.

---

## 8. Convention table (old Lean / reference / new Lean), B1 and B2 rows

Old Lean = accepted baseline at `e62c101` (`docs/skeleton-audit.md` §1.2–1.6);
reference = `target-theorem.tex` / `proof-blueprint.tex`; new Lean = `6cdcef7`.
`u_j = log‖z_j‖`, `θ_j = arg z_j`. The stage-A rows are in
`docs/reviews/stage-a-semantic-audit.md` item 7 and are not repeated except where
B1/B2 change their status.

| role | old Lean (`e62c101`) | reference (PDF) | new Lean (`6cdcef7`) | status |
| --- | --- | --- | --- | --- |
| form coefficient (c) | `(S.B i j : ℂ)`, `= K_{ij}` since `B` skew | `Ω = ½ ∑_{j,l} K_{jl} dlog z_j ∧ dlog z_l` | `(S.K i j : ℂ)` in `GlobalTwoForm.matrixForm`, `TorusNondegeneracy.complexMatrix`, `NodeTwoForm.outsideBlock`/`complexOutsideBlock`; `(S.K i j : ℝ)` in `TorusPrimitive.beta`, `PrimitiveResidual.residual` | **done (B1, B2)**; stage-A R2 discharged, no `S.B` form site survives |
| form sign | `= +Im Ω` | `ω\|_T = Im Ω_T` | `= +Im Ω` (`matrixForm_real`, `localForm_torus`) | **PASS (item 1)** |
| form determinant | `det B = 1` | `det K = det E ∏ d_i = ∏ d_i > 0` | `complexMatrix_det hdet : det = ∏ (S.D i : ℂ)`, `isUnit_complexMatrix_det` | **done (B1)**; stage C must use `IsUnit`, **not** `= 1` |
| node coefficient | `+(rawParameters …)⁻¹ • wedge du dv` | `Ω = ∑_{i∈I} d_i dlog t_i ∧ dlog x_i + Ω₀`; `dlog t_i ∧ dlog x_i = t_i^{-1} dy_i ∧ dx_i` | `-(S.D i : ℂ) * (rawParameters S I x (inl i))⁻¹` | **done (B1)**; sign flip is *forced* by `K_{ij} = -d_i B_{ij}` |
| node residual block | `Tᵀ B_J T`, integral | `Ω₀`, constant coefficients | `residualMatrix = Tᵀ K_J T`, **rational**; `T = independentRowInverseMatrix` **unchanged and integral** (role (f) is not weighted) | **done (B1)** |
| node normal form | `[[0,−P,0],[P,A,B₀],[0,−B₀ᵀ,C]]` with `P` the unweighted row projection | `[[0,−D_I,0],[D_I,A,B₀],[0,−B₀ᵀ,C]]` | `normalMatrix = fromBlocks 0 weightProjection (−weightProjectionᵀ) complexResidual`, `weightProjection i (inl i') = -(S.D i) δ_{ii'}` | **done (B1)**, entry for entry |
| nondegeneracy domain | `∀ p : S.Point` | nondegenerate on `A(B̃)` | `GlobalSymplectic.nondegenerate_omega (p : S.Point)`, `isSymplecticOn … Set.univ` | **whole space**, not just the torus |
| `λ_tor` (c) | `beta = ∑_{i,j}(S.B i j) u_i dθ_j` | `λ_tor = u^T K dθ = ∑_{j,l} K_{jl} u_j dθ_l` | `beta = ∑_{i,j}(S.K i j : ℝ) u_i dθ_j`; no `½`, no minus, `u` on the **first** index | **done (B2)** |
| `d beta` | `= Im Ω` on the torus | `dλ_tor = Im Ω` | `exteriorDerivative_beta`: `= GlobalTwoForm.omega p` for `p ∈ initialTorus S` | **done (B2)**, sign `+` |
| `exchangeCharacter` | `1/t_i` | `t_i = P_i^+/P_i^- = z^{c_i}` | `t_i` | **flipped vs baseline**; docstring still says `1/t_i` (**D1**) |
| `rowLog` (d) | `= −v_i` | `v_i = log\|t_i\| = c_i(u) = ∑_j E_{ji} u_j` | `TorusCorrection.rowLog = PrimitiveLocalization.rowLog = PrimitiveResidual.logRow = ∑_j (S.B i j : ℝ) u_j = +v_i` (text unchanged, **meaning flipped**) | **re-derived (B2)**, `+v_i` |
| `angle` (d) | `= −(η_i−π)` | `η_i − π`, `Log(−t_i) = v_i + i(η_i−π)` | `PrimitiveLocalization.angle = arg(−exchangeCharacter) = +(η_i−π)`; `nodeLog = +Log(−t_i)` | **re-derived (B2)**, `+` |
| `tau` (d) | `= −dη_i` | `c_i(dθ) = dη_i` | `PrimitiveResidual.tau = ∑_j (S.B i j : ℝ) • dθ_j = +dη_i` (proved: `tau_eq_nodeAngle_differential`) | **re-derived (B2)**, `+` |
| `H` (g) | `H_Lean = −H_ref`, no `d_i` | `H = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)` | `H = ∑_{i∈S.mutable} (S.D i : ℝ) * (radial · dominance · rho(rowLog) · angular)` | **`H_Lean = +H_ref`** (item 3) |
| `a` and `L` of the cutoffs | `a = κ`, `L = 2κ−2ε` | `L > a > 0`, `h(u)=u+a (u≤−L)` | unchanged (`radial_tail`, `radialLength ε κ = 2(κ−2ε)`); at `ε=1, κ=3`: `a=3 < L=4` | **done** |
| primitive | `alpha = beta − dH_Lean = λ_ac` | `λ_ac = λ_tor + dH` | **`alpha := beta + covectorForm (differentialCovector H)`** | **settled (B2)**, option **O1** |
| per-index scalar | `correction`, unweighted | `h(u_i)χ_iρ(v_i)β(η_i)` | `PrimitiveLocalization.correction`, **unweighted**; every consumer supplies `(S.D j : ℝ)` | **done (B2)** |
| affine germ | `affineCorrection`, unweighted | `(u_i+a)(η_i−π)` | `affineCorrection κ i p = (logNorms + κ)·(nodeLog).im`, **unweighted** | **done (B2)** |
| `H` near a node | `singularH + regularH` | `H = ∑_{i∈I} d_i(u_i+a)(η_i−π) + H'` | `singularH = ∑_{i∈I}(S.D i)·affine_i`, `regularH = ∑_{j∈surviving}(S.D j)·correction_j` | **done (B2)** |
| `H'` index set | `{j ∉ I : S.B j i = 0 ∀ i∈I}` | `{k ∈ M\I : B_{ik} = 0 ∀ i∈I}` | unchanged text, `S.B j i = S.E i j = B_{ij}` | **matching**; note the orientation hidden in the name "row" |
| node primitive block | `lambda κ` = `+`(reference block) | `v dθ − u dη + d(hρβ)` | `lambda κ = −(v_i dθ_i − u_i dη_i + d((u_i+κ)(η_i−π)))`; `block = ∑_{i∈I}(S.D i : ℝ) • lambda_i` | **flipped**, consistently with `alpha` |
| local primitive | `eta = residual + block − regularForm` | `λ_ac` near a node | **`eta = residual − block + regularForm`** | **settled (B2)**; verified by the proved `eta_eq_torus` |
| `eta` on `{y_i = 0}` | `residual − regularForm` | extension vanishes at `y_i = 0` | `eta_zero_partners : residual + regularForm` | **flipped**, consistently |
| radial flow (stage C) | `u̇_i = u_i − h χ ρ β'` with `S.B` | `eq:acyclic-flow` | `mutable_radial_equation` / `frozen_radial_equation` **verbatim unchanged**; `radial_matrix_equation` is `S.B ↦ S.K` at all three sites, minus preserved | **pending (stage C)**, shape fixed in item 4c |
| angular flow (stage C) | `∑_j (S.B i j)(…).im = +∂_{u_i}H` | `η̇_i = (1/d_i) ∂_{u_i} H` | `∑_j (S.K i j)(…).im = −∂_{u_i}H`, equivalently `∑_j (S.B i j)(…).im = (S.D i : ℝ)⁻¹ ∂_{u_i}H` | **pending (stage C)**, sign settled here |
| `∂_θ H`, `∂_u H` (g) | `differential_H_angular/radial`, unweighted | `∂_θ H = K a` | both gain `(S.D i : ℝ)` per summand; the exponent row stays `S.B` | **pending (stage C)** |
| dynamics inverse (e) | `B⁻¹`, `det B = 1` | `θ̇ = −K^{-1}∂_u H`, `c_i(K^{-1}x) = −x_i/d_i` | `K⁻¹` (rational); `SymmetrizerAlgebra.vecMul_E_col_inv_K` | **pending (stage C)** |
| parity of the cutoffs | used implicitly in §1.6 | `ρ` even, `β` odd near `π` | `rho (−x) = rho x`, `vartheta δ (−T) = −vartheta δ T` both **true but unstated** | **R5** |

---

## DEFECT D1 — `exchangeCharacter_eq_zpow_product`'s docstring asserts the opposite of its statement (carried over, still present at `6cdcef7`)

**Declaration.** `ClusterSkeleton.exchangeCharacter_eq_zpow_product`,
`ClusterSkeleton/NodeCoordinates.lean:55-60`.

```lean
/-- The exchange ratio is the Laurent monomial with the actual signed column of
`E`, i.e. the reference's inverse character `1/t_i`. -/
theorem exchangeCharacter_eq_zpow_product (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i) := …
```

**Discrepancy.** The PDF has `t_i = z^{c_i} = ∏_j z_j^{E_{ji}}` with `c_i = E e_i`,
so the statement says `exchangeCharacter p i = t_i` while the docstring says
`1/t_i`. **[elab]** confirmed again on `6cdcef7`. This was reported as **D1** in
the stage A audit (at `de58cd2`) with a documentation-only fix; it is **not fixed**
at `6cdcef7`, and `NodeCoordinates.lean` is a stage-A module that stage B2 was
forbidden to edit, so no stage has yet owned it.

**Why it still matters.** It is now *contradicted by the tree itself*: the new
docstrings on `TorusPrimitive.alpha` ("the Lean character is the reference
character, `exchangeCharacter p i = t_i`"), `TorusCorrection.H` and
`LocalPrimitive.eta` all state the correct relation. A stage-C worker re-deriving
a sign who reads `NodeCoordinates.lean` first will reproduce the baseline's
cancellation and conclude `alpha = beta − dH`, i.e. reverse the Liouville field —
the exact error this review was commissioned to rule out.

**Minimal fix (statement level: none; documentation only).** Replace the
docstring by: "The exchange ratio is the reference character
`t_i = z^{c_i} = ∏_j z_j^{E_{ji}}` with `c_i = E e_i` (the baseline's
`exchangeCharacter` was `1/t_i`; the column convention inverts it, and
`normalizedPartner` is now the reference's `y = z_i'/P_i^-`)." The same stale
word "outgoing" of stage-A **D2** (`Seed.Point.outgoing_ne_zero`,
`CapIndependence.coordinateCap_outgoing_not_interior`) is also still present and
still statement-correct.

**Downstream stage affected.** Stage C, as a reading hazard only; no Lean
statement is wrong. Since stage C owns the Lean tree, it is the natural owner of
both docstring repairs.

---

## Downstream impact summary

* **Nothing in B1 or B2 blocks stage C, and no sign needs re-deciding.**
  `alpha = beta + dH` with `H_Lean = +H_ref` is the blueprint's `λ_ac`; the
  contraction gives `eq:acyclic-flow` and `eq:acyclic-angle-flow` with no extra
  sign; `eta = residual − block + regularForm` is the matching node identity and
  is already machine-checked against `alpha` by `eta_eq_torus`.
* **Stage C (`c208ef62`, running).** Use the four shapes of item 4c; option
  **O1** of `docs/weighted-stage-c-map.md` §4 is confirmed, with the minus in
  `angular_equation` (or `1/d_i` in the `B` form), the baseline minus preserved
  in `radial_matrix_equation`, `mutable_radial_equation` /
  `frozen_radial_equation` **verbatim unchanged**, and `(S.D i : ℝ)` added to
  `differential_H_angular` / `differential_H_radial`. Take the field from
  `GlobalPrimitive.alpha` with `alpha_eq_eta` / `eta_zero_partners`, not from
  `exists_global_primitive` (**R6**). Replace every `det = 1` cancellation by
  `IsUnit (det K)`.
* **Integration (objective planner).** `docs/skeleton-audit.md` can be rewritten
  from item 8's table; the two cheap additive lemmas of **R5** should be landed
  by whoever owns `PrimitiveCutoffs.lean` next, and the recovery theorem of
  **R7** should be stated with the pointwise identity of item 7 rather than only
  existentially. **D1**'s docstring repair belongs to stage C, which owns the
  Lean tree.

---

## Appendix A — elaboration checks

Run at the repository root of this branch with `lake env lean Scratch.lean`
(toolchain `leanprover/lean4:v4.34.1`, pinned Mathlib/FsFltz;
`Scratch.lean` **deleted before committing**). All `example`s below elaborated
with no errors; no Lean file in the tree was modified. Preceded by
`lake build ClusterSkeleton.GlobalPrimitive ClusterSkeleton.RegularCorrection
ClusterSkeleton.GlobalSymplectic ClusterSkeleton.NodeNondegeneracy`
(2914 jobs, success, warnings only).

```lean
import ClusterSkeleton.GlobalPrimitive
import ClusterSkeleton.RegularCorrection
import ClusterSkeleton.NodeNondegeneracy
import ClusterSkeleton.GlobalSymplectic
import ClusterSkeleton.SkewSeed

open ClusterSkeleton FsFltz.Geometry
open scoped Manifold ContDiff BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {d : ℕ}

-- item 2: beta is u^T K dtheta: no 1/2, no minus, first K index on u
example (S : Seed d) (hdet : S.Unimodular) :
    TorusPrimitive.beta S hdet = covectorForm _ (fun p : S.Point =>
      ∑ i : Fin d, ∑ j : Fin d,
        ((S.K i j : ℝ) * Real.log ‖p.a i‖) • TorusPrimitive.angleCovector S hdet j p) := rfl

-- item 4: alpha := beta + d H  (the PLUS is definitional)
example (S : Seed d) (hdet : S.Unimodular) (H : S.Point → ℝ) :
    TorusPrimitive.alpha S hdet H =
      TorusPrimitive.beta S hdet + covectorForm _ (differentialCovector _ H) := rfl

-- item 3: every summand of H carries (S.D i)
example (S : Seed d) (e k del : ℝ) (p : S.Point) :
    TorusCorrection.H S e k del p = ∑ i ∈ S.mutable, (S.D i : ℝ) *
      (PrimitiveCutoffs.radial e k (Real.log ‖p.a i‖) *
       DominanceCutoff.dominance S e i (fun j => Real.log ‖p.a j‖) *
       PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖) *
       PrimitiveCutoffs.vartheta del (Complex.arg (-exchangeCharacter p i))) := rfl

-- the two parity facts the H sign rests on; NEITHER is a library lemma
example (x : ℝ) : PrimitiveCutoffs.rho (-x) = PrimitiveCutoffs.rho x := by
  simp [PrimitiveCutoffs.rho]
example (del T : ℝ) : PrimitiveCutoffs.vartheta del (-T) = -PrimitiveCutoffs.vartheta del T := by
  simp [PrimitiveCutoffs.vartheta, PrimitiveCutoffs.angularWindow, Real.sin_neg,
    Real.cos_neg, Real.arcsin_neg]

-- item 3: rowLog is the integral column exponent row, i.e. c_i(u) = v_i
example (S : Seed d) (p : S.Point) (i : Fin d) :
    TorusCorrection.rowLog S p i = ∑ j : Fin d, (S.E j i : ℝ) * Real.log ‖p.a j‖ := rfl
example (S : Seed d) (p : S.Point) (i : Fin d) :
    TorusCorrection.rowLog S p i = PrimitiveLocalization.rowLog p i := rfl
-- and the exchange character is the reference t_i = z^{c_i}
example (S : Seed d) (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i) :=
  exchangeCharacter_eq_zpow_product p i

-- item 1: the node coefficient is -(d i) / q_i on du ^ dv
example (S : Seed d) (I : Finset (Fin d)) (hdet : S.Unimodular) (hI : S.Independent I)
    (x : IndependentNodeChart.Vector S I) :
    NodeTwoForm.complexForm S I hdet hI x =
      (∑ i : {i : Fin d // i ∈ I},
          (-(S.D i : ℂ) * (IndependentNodeChart.rawParameters S I x (Sum.inl i))⁻¹) •
            NodeTwoForm.wedge (NodeTwoForm.du S I i) (NodeTwoForm.dv S I i)) +
      (1 / 2 : ℂ) • ∑ k, ∑ l, (NodeTwoForm.residualMatrix S I hdet hI k l : ℂ) •
        NodeTwoForm.wedge (NodeTwoForm.logParameter S I x k)
          (NodeTwoForm.logParameter S I x l) := rfl
-- the wedge convention, and logParameter (inl i) = dlog t_i with q_i = x_i y_i - 1
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : E →L[ℂ] ℂ) (v w : E) :
    NodeTwoForm.wedge a b ![v, w] = a v * b w - a w * b v := rfl
example (S : Seed d) (I : Finset (Fin d)) (x : IndependentNodeChart.Vector S I)
    (i : {i : Fin d // i ∈ I}) :
    IndependentNodeChart.rawParameters S I x (Sum.inl i) = (x.1 i).1 * (x.1 i).2 - 1 := rfl
example (S : Seed d) (I : Finset (Fin d)) (x v : IndependentNodeChart.Vector S I)
    (i : {i : Fin d // i ∈ I}) :
    NodeTwoForm.logParameter S I x (Sum.inl i) v =
      ((x.1 i).2 * (v.1 i).1 + (x.1 i).1 * (v.1 i).2) / ((x.1 i).1 * (x.1 i).2 - 1) :=
  NodeTwoForm.logParameter_inl S I x v i

-- item 1: the form coefficient of the global two-form is K
example (S : Seed d) (v : Fin 2 → (Fin d → ℂ)) :
    GlobalTwoForm.matrixForm S v = ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
      (S.K i j : ℂ) * (v 0 i * v 1 j - v 1 i * v 0 j)).im :=
  GlobalTwoForm.matrixForm_apply S v
-- and d beta = that form, so Im Omega is the coefficient-K two-form
example (S : Seed d) (b z : Fin d → ℂ) :
    extDeriv (TorusPrimitive.logarithmicPrimitive S b) z = GlobalTwoForm.matrixForm S :=
  TorusPrimitive.extDeriv_logarithmicPrimitive S b z
example (S : Seed d) (v w : Fin d → ℂ) :
    GlobalTwoForm.matrixForm S ![v, w] =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (v i).re * (w j).im) -
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (w i).re * (v j).im) :=
  TorusPrimitive.matrixForm_real S v w

-- item 1: nondegeneracy is claimed at EVERY point of the space
example (S : Seed d) (hdet : S.Unimodular) :
    ∀ p : S.Point, (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
      (GlobalTwoForm.omega S hdet) p := GlobalSymplectic.nondegenerate_omega S hdet
example {n : ℕ} (M : SmoothManifold n) (eta : M.Form 2) (x : M.Point) :
    M.Nondegenerate eta x = ∀ v : M.Tangent x,
      (∀ w, SmoothManifold.evalTwo eta x v w = 0) → v = 0 := rfl

-- item 5: eta = residual - block + regularForm (both signs definitional)
example (S : Seed d) (hdet : S.Unimodular) (e k del : ℝ) (p : S.Point) :
    LocalPrimitive.eta S hdet e k del p =
      PrimitiveResidual.residual S hdet p.zeroSet -
        NativeNodePrimitive.block S hdet k p.zeroSet p.zeroSet_independent +
        RegularCorrection.regularForm S hdet p.zeroSet e k del := rfl

-- item 5: the unweighted scalar correction, and H as its d-weighted sum
example (e k del : ℝ) (S : Seed d) (i : S.Mutable) (p : S.Point) :
    PrimitiveLocalization.correction e k del i p =
      PrimitiveCutoffs.radial e k (DominanceCutoff.logNorms S p i) *
        DominanceCutoff.dominance S e i (DominanceCutoff.logNorms S p) *
        PrimitiveCutoffs.rho (PrimitiveLocalization.rowLog p i) *
        PrimitiveCutoffs.vartheta del (PrimitiveLocalization.angle p i) := rfl
example (S : Seed d) (e k del : ℝ) (p : S.Point) :
    TorusCorrection.H S e k del p = ∑ j : S.Mutable, (S.D j : ℝ) *
      PrimitiveLocalization.correction e k del j p :=
  RegularCorrection.H_eq_sum e k del p

-- item 5: affineCorrection is UNWEIGHTED, (u_i + k) * Im Log(-t_i)
example (k : ℝ) (S : Seed d) (i : S.Mutable) (p : S.Point) :
    PrimitiveLocalization.affineCorrection k i p =
      (DominanceCutoff.logNorms S p i + k) * (PrimitiveLocalization.nodeLog p i).im := rfl

-- item 5: the node block carries d_i; lambda is the cancellation covector
example (S : Seed d) (hdet : S.Unimodular) (k : ℝ) (I : Finset (Fin d))
    (hI : S.Independent I) (q : S.Point) :
    NativeNodePrimitive.block S hdet k I hI q =
      (covectorForm _ (fun r : S.Point => ∑ i : I,
        (S.D i.val : ℝ) • NativeNodePrimitive.lambda S hdet k ⟨i.val, hI.1 i.property⟩ r)) q := rfl
example (k : ℝ) (p : ℂ × ℂ) (hp : p ∈ nodeLogDomain) (hu : p.1 ≠ 0) :
    NodePrimitiveCancellation.A p • fderiv ℝ NodePrimitiveCancellation.T p -
      NodePrimitiveCancellation.S p • NodePrimitiveCancellation.dtheta p -
      fderiv ℝ (fun q => (NodePrimitiveCancellation.A q + k) * NodePrimitiveCancellation.T q) p
      = NodePrimitiveCancellation.lambda k p :=
  NodePrimitiveCancellation.cancellation k hp hu
-- numeric sign of lambda on the divisor: +(1+k) Im(y dx), i.e. MINUS the reference block
example (k : ℝ) (v : ℂ) (t : ℂ × ℂ) :
    NodePrimitiveCancellation.lambda k (0, v) t = (1 + k) * (v * t.1).im :=
  NodePrimitiveCancellation.lambda_zero k v t

-- item 5: regularH / singularH are the d-weighted eq. acyclic-H-near split
example (S : Seed d) (I : Finset (Fin d)) (e k del : ℝ) (p : S.Point) :
    RegularCorrection.regularH S I e k del p =
      ∑ j ∈ RegularCorrection.surviving S I, (S.D j : ℝ) *
        PrimitiveLocalization.correction e k del j p := rfl
example (S : Seed d) (I : Finset (Fin d)) (k : ℝ) (p : S.Point) :
    RegularCorrection.singularH I k p =
      ∑ j ∈ (Finset.univ.filter fun j : S.Mutable => (j : Fin d) ∈ I),
        (S.D j : ℝ) * PrimitiveLocalization.affineCorrection k j p := rfl
-- surviving = blueprint's { k in M \ I : E_{ik} = 0 for all i in I }
example (S : Seed d) (I : Finset (Fin d)) (j : S.Mutable) :
    j ∈ RegularCorrection.surviving S I ↔
      ((j : Fin d) ∉ I ∧ ∀ i ∈ I, S.E i j = 0) :=
  RegularCorrection.mem_surviving S I j

-- item 7: at D = 1, E := B the weighted form coefficient IS the old integer matrix
example (S : SkewSeed d) (i j : Fin d) : (S.toSeed).K i j = (S.B i j : ℚ) :=
  SkewSeed.toSeed_K S i j
example (S : SkewSeed d) (a : Fin d → ℂ) (i : Fin d) :
    (S.toSeed).positiveMonomial a i = S.negativeMonomial a i :=
  SkewSeed.toSeed_positiveMonomial S a i
example (S : SkewSeed d) (i : Fin d) : (S.toSeed).D i = 1 := rfl

-- item 6: the exact final statements
#check @ClusterSkeleton.GlobalPrimitive.exists_global_primitive
#check @ClusterSkeleton.GlobalPrimitive.exteriorDerivative_alpha
#check @ClusterSkeleton.GlobalPrimitive.alpha_eq_eta
#check @ClusterSkeleton.GlobalPrimitive.alpha_eq_torus

#print axioms ClusterSkeleton.GlobalPrimitive.exists_global_primitive
#print axioms ClusterSkeleton.GlobalPrimitive.exteriorDerivative_alpha
#print axioms ClusterSkeleton.TorusCorrection.H
#print axioms ClusterSkeleton.TorusPrimitive.alpha
#print axioms ClusterSkeleton.LocalPrimitive.eta
#print axioms ClusterSkeleton.LocalPrimitive.eta_eq_torus
#print axioms ClusterSkeleton.PrimitiveResidual.beta_decomposition
#print axioms ClusterSkeleton.NodeTwoForm.complexForm
#print axioms ClusterSkeleton.NodeTwoForm.complexForm_torus
#print axioms ClusterSkeleton.GlobalSymplectic.nondegenerate_omega
#print axioms ClusterSkeleton.NodeNondegeneracy.normalMatrix
```

Every `#print axioms` reported exactly
`[propext, Classical.choice, Quot.sound]`. `#check` printed, in particular:

```
@GlobalPrimitive.exists_global_primitive : ∀ {d : ℕ} (S : Seed d) (hdet : S.Unimodular),
  ∃ ε κ δ theta,
    0 < ε ∧ 2 * ε + 1 ≤ κ ∧ 0 < δ ∧ δ < Real.pi ∧
      (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta ∧
        (∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p) ∧
          (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta =
              GlobalTwoForm.omega S hdet ∧
            ∀ (p : (SmoothAtlas.presentation S hdet).manifold.Point),
              (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
                ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta) p
```
