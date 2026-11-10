# Stage A semantic audit: does the weighted foundation mean the mathematics of `target-theorem.tex`?

Independent **statement** review (not a build check) of stage A of objective
`7d3240fc-f412-49c4-88c8-a9d1a5a1bdaf` revision 2, mission
`cacf0389-5f1b-4b6a-a835-9f8735b8b01b`.

* Reviewed source: commit `de58cd2c5a12942c6571c816d922ffd0bb837ac8` (branch
  `weighted/stage-a`, parent `e62c101`).
* Reference: `docs/tex/target-theorem.tex`, `docs/tex/proof-blueprint.tex`,
  `docs/roadmap.md` (acceptance checks 1–3 and 5), `docs/skeleton-audit.md`
  §1.1–1.9 (which records the accepted `D = I` baseline).
* Review branch: `weighted/stage-a-audit`. The stage A commit is not present in
  this checkout and the remote is not reachable with agent credentials, so the
  base was reproduced per path from
  `GET /api/v3/repositories/5d09d029-.../file?commit_oid=de58cd2c…&path=…`:
  every tracked path whose `blob_oid` differs from `e62c101` was written, plus
  the two new modules. The repository API exposes no tree listing
  (`agent schema --section routes` has only `repository_head` and
  `repository_file`), so "every tracked path" means every path in
  `git ls-files` at `e62c101` plus `ClusterSkeleton/SkewSeed.lean` and
  `ClusterSkeleton/Examples/NonSkew.lean`; a file added by stage A outside that
  list would not appear here. The reproduction is commit `37994c9` and consists
  of exactly 10 modified and 2 new files:
  `ClusterSkeleton.lean`, `CapAngularTangency`, `CapIndependence`, `CapStrata`,
  `Examples/A2`, `GeometryTarget`, `IndependentNodeChart`, `NodeCoordinates`,
  `Seed`, `ZeroSet`, and new `SkewSeed`, `Examples/NonSkew`. `docs/`, the PDFs,
  `lakefile.toml`, `lean-toolchain` are unchanged at `de58cd2`.
* No Lean file is modified or added by this review. The claims marked
  **[elab]** were machine-checked in a scratch file at the repository root with
  `horizon-lean-check --lean Scratch.lean`; the file was deleted before
  committing and its content is listed in Appendix A.

## Verdict summary

| # | Item | Verdict |
| --- | --- | --- |
| 1 | `Seed` fields versus the PDF input | **PASS** (remarks M1, M2) |
| 2 | Exchange equations and the monomial convention | **PASS** (risk R2 on the reused name `S.B`) |
| 3 | Form coefficient and its sign | **PASS** — the Lean form is the PDF's `Im Ω_T`, **not** its negative |
| 4 | `SkewSeed` recovery route | **PASS** on the convention choice, **RISK R1** on the missing recovery statement |
| 5 | `Examples/NonSkew` | **PASS** (risk R4: the acceptance-check-3 consumer line is still absent) |
| 6 | Baseline fidelity | **PASS** — one real statement change (`GeometryTarget`), everything else is `rfl`-level or a module-graph improvement; **DEFECT D1**, **DEFECT D2** (both documentation) |
| 7 | Weighted convention table | **delivered** below; it carries two mandatory stage-B actions (**RISK R3**) |

Findings, with the downstream stage each affects:

| id | kind | declaration | stage |
| --- | --- | --- | --- |
| D1 | DEFECT (docstring contradicts the statement) | `ClusterSkeleton.exchangeCharacter_eq_zpow_product` | B1, B2, C |
| D2 | DEFECT (name/docstring orientation) | `ClusterSkeleton.Seed.Point.outgoing_ne_zero` | none (readability) |
| R1 | RISK (obligation not yet stated) | `SkewSeed.pointHomeomorph` consumers | C |
| R2 | RISK (silently wrong if reused in the form role) | `Seed.B` / `Seed.Bexp` | B1 |
| R3 | RISK (undetectable by the torus anchor) | `TorusCorrection.H`, `TorusPrimitive.alpha` | B1, B2, C |
| R4 | RISK (acceptance scope) | `FirstGeometricTarget` consumers | C |

No DEFECT requires a change to a stage A **statement**. The two DEFECTs are
docstrings in convention-critical files, i.e. exactly the places where stage B
is instructed to re-derive signs; D1 asserts the opposite of what the
accompanying statement says and is therefore reported as a defect, not a nit.

---

## 1. `Seed` fields versus the PDF input — PASS

### Lean (`ClusterSkeleton/Seed.lean:31-43`)

```lean
structure Seed (d : ℕ) where
  E : Matrix (Fin d) (Fin d) ℤ
  mutable : Finset (Fin d)
  D : Fin d → ℚ
  D_pos : ∀ i, 0 < D i
  skewSymmetrizable : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < E i j)
```

```lean
def Unimodular : Prop := S.E.det = 1                                    -- Seed.lean:53
def K : Matrix (Fin d) (Fin d) ℚ := fun i j => (S.E i j : ℚ) * S.D j    -- Seed.lean:69
def Independent (I : Finset (Fin d)) : Prop :=
  I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.E i j = 0                         -- Seed.lean:250
```

### PDF (`target-theorem.tex`, §1)

> `E ∈ GL_n(Z)`, `D̃ = diag(d_1,…,d_n)`, `d_j ∈ Q_{>0}`, `K = E D̃`, `K^T = -K`.
> Thus `E_{ij} d_j = -E_{ji} d_i`, rather than `E_{ij} = -E_{ji}`.
> Require the mutable block `B = E_{M,M}` to be acyclic: the arrows `i → j`
> with `B_{ij} > 0` have no directed cycle. No acyclicity is required on the
> full set of indices.
> Call `I ⊆ M` independent if `E_{ij} = 0` for all `i,j ∈ I`.

### Judgement

* **`K = E D̃`, not `D̃ E`.** `K i j = E i j * D j` is right multiplication by
  the diagonal (column scaling), i.e. `(E D̃)_{ij} = E_{ij} d_j`. `D̃ E` would
  give `d_i E_{ij}`. The field `skewSymmetrizable` is the PDF sentence
  `E_{ij} d_j = -(E_{ji} d_i)` verbatim. **[elab]** `S.K i j = (S.E i j : ℚ) * S.D j`
  holds by `rfl`. Cross-check against the blueprint, which uses `K` in three
  places with a fixed index order and all three agree with this definition:
  `∑_j K_{ij} dlog z_j = -d_i dlog t_i` needs `K_{ij} = -E_{ji}d_i`;
  `∑_j K_{ji} u_j = d_i ∑_j E_{ji} u_j = d_i v_i` needs `K_{ji} = E_{ji} d_i`;
  `K_{ii'} = d_{i'} B_{ii'}` needs `K_{ii'} = E_{ii'} d_{i'}`. PASS.
* **`Unimodular := E.det = 1` versus `det = ±1` / `IsUnit`.** The PDF states
  `E ∈ GL_n(Z)` and then *derives* equality with `1`: "In fact `det E = 1`: a
  nonsingular real skew-symmetric matrix has positive determinant, so
  `det E = det K / det D̃ > 0`, while unimodularity gives `det E = ±1`."
  So `E.det = 1` is **not** a strengthening of the PDF input: given the `Seed`
  fields, `IsUnit S.E.det` and `S.E.det = 1` are equivalent (if `det E = -1`
  then `K = E D̃` is a nonsingular rational skew-symmetric matrix of negative
  determinant, impossible). Nothing in the baseline *needs* `= 1` rather than
  `IsUnit`: every consumer immediately rewrites to a unit —
  `NodeCoordinates.independent_rows_inverse_pairing` line 99
  (`have hunit : IsUnit S.B.det := by rw [S.B_det hdet]; exact isUnit_one`),
  `TorusNondegeneracy.complexMatrix_det`, `AllStrataGrowth:117`,
  `LocalAngularDynamics:226`, `TorusLiouvilleDynamics:424,739`,
  `NodeNondegeneracy:114` — all of which would also work from `IsUnit`.
  Reported, not changed. **Remark M1:** stage A records no declaration carrying
  the PDF's derivation, so a check-5 reviewer must take the implication
  `IsUnit S.E.det → S.Unimodular` on the PDF's authority. The cheap fix is a
  docstring citation on `Seed.Unimodular`; the full Lean statement
  `S.Unimodular ↔ IsUnit S.E.det` needs skew-symmetric determinant positivity
  (Pfaffian), which is not currently worth its cost and is not required by any
  acceptance check.
  **Remark M2:** for odd `d`, `Seed d` plus `Unimodular` is contradictory
  (`det K = det E * ∏ D ≠ 0` while an odd skew matrix has determinant `0`), so
  the weighted target is vacuous in odd ambient dimension. This is equally true
  of the PDF input and is not a defect.
* **`acyclic`.** The field relation is `0 < E i j` on the subtype
  `{i // i ∈ mutable}`, i.e. exactly the PDF's arrow set `i → j` with
  `B_{ij} > 0` restricted to `M` (the PDF's `B = E_{M,M}` here is the *untransposed*
  restriction of `E`, as the blueprint's maximal-path proof uses). Equivalence
  with "no directed cycle" is proved generally:
  `Seed.wellFounded_iff_no_directed_cycle : WellFounded r ↔ ∀ i, ¬ Relation.TransGen r i i`
  for `[Finite α]` (`Seed.lean:262`), and the orientation is irrelevant on the
  finite mutable type by `Seed.acyclic_exponent : WellFounded (fun i j : S.Mutable => 0 < S.B i j)`
  (`Seed.lean:279`, proved via `Relation.transGen_swap`). Both orientations are
  therefore equivalent to the PDF hypothesis. PASS.
* **`Independent`.** `I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.E i j = 0` is the PDF
  condition including `i = j` (automatic from `E_diag_zero`). **[elab]** the
  unfolding holds by `rfl`. PASS.
* **Sign facts replacing `Seed.skew`.** `E_diag_zero`, `E_pos_iff_neg`,
  `E_eq_zero_iff` are exactly the blueprint's sentence "Positivity of the `d_i`
  implies `E_{ii} = 0` and `E_{ij} = 0 ⟺ E_{ji} = 0`, with opposite signs when
  nonzero. These are the sign properties used in the zero-set proof." PASS.
* `Seed` itself does not demand invertibility of `E`; `Unimodular` is a separate
  hypothesis quantified in `FirstGeometricTarget`. The quantifier structure
  therefore matches the PDF ("The unimodular completion is part of the input"),
  and intermediate lemmas proved without it are strictly stronger. PASS.

## 2. Exchange equations — PASS

### Lean (`Seed.lean:180-219`)

```lean
def positiveMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ := ∏ j, a j ^ (S.E j i).toNat
def negativeMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ := ∏ j, a j ^ (-S.E j i).toNat

abbrev Point :=
  {x : (Fin d → ℂ) × (S.Mutable → ℂ) //
    (∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
    (∀ f, f ∉ S.mutable → x.1 f ≠ 0)}

theorem exchange (i : S.Mutable) :
    p.a i * p.b i = S.positiveMonomial p.a i + S.negativeMonomial p.a i := p.2.1 i
theorem frozen_ne_zero (f : Fin d) (hf : f ∉ S.mutable) : p.a f ≠ 0 := p.2.2 f hf
```

### PDF (`target-theorem.tex`, §1)

> Use *column* exchange exponents throughout:
> `P_i^±(z) = ∏_{j=1}^n z_j^{[±E_{ji}]_+}`.
> `X_E = {(z,z') ∈ C^n × C^M : z_i z_i' = P_i^+(z) + P_i^-(z) (i ∈ M), z_f ≠ 0 (f ∈ F)}`.
> Here `[a]_+ = max(a,0)`. … Frozen coordinates remain variable elements of `C^*`;
> no principal-coefficient assumption is made.

### Judgement

`(S.E j i).toNat = [E_{ji}]_+` and `(-S.E j i).toNat = [-E_{ji}]_+`, so
`positiveMonomial = P_i^+` and `negativeMonomial = P_i^-` **literally**, with the
roadmap's "Use column exponents `E_ji` in the exchange equations". The ambient
space `(Fin d → ℂ) × (S.Mutable → ℂ)` is `C^n × C^M`; the mutable equation has
`P_i^+` on the same side and in the same order as the PDF; the frozen condition
is nonvanishing of a free variable, with no value fixed and no principal
coefficients. `Point` is a subtype, so the topology is the inherited one
(the PDF: "Give `X_E` the induced topology"). **PASS.**

**There is no remaining monomial interchange.** The internal row-convention
abbreviation is `Seed.Bexp := S.Eᵀ`, `Seed.B := S.Bexp`, and
`Seed.B_apply : S.B i j = S.E j i := rfl` (`Seed.lean:64`) — **[elab]** verified
by `rfl`, as are `positiveMonomial a i = ∏ j, a j ^ (S.B i j).toNat` and
`negativeMonomial a i = ∏ j, a j ^ (-S.B i j).toNat`
(`positiveMonomial_eq_prod_B`, `negativeMonomial_eq_prod_B`). Because the two
matrices are *definitionally* related, the exchange space is the
column-convention space on the nose and the roadmap's alternative obligation
("If preserving an internal row convention, prove the exact convention
equivalence, including the exchange space and form sign") is discharged by
definitional equality for the exchange space. The form-sign half of that
sentence is **not** discharged by `rfl` and is the subject of item 3 and risk R2.

> **RISK R2 (stage B1).** `S.B` keeps its old name but now denotes `Eᵀ`, i.e.
> the *transpose* of the baseline's matrix; at `D = 1` it is `-K`. In the
> exponent, adjacency and integer-lattice roles (groups (a), (b), (f) of the
> stage A assignment) `S.B` is correct and is what makes the old proofs
> transport. In the **form-coefficient** role (group (c)) `S.B` is now the
> negative of the right matrix. The sites still holding `S.B` in the form role
> at `de58cd2` are `GlobalTwoForm.matrixForm` (`:232`),
> `TorusPrimitive.beta` (`:29`), `TorusNondegeneracy.complexMatrix`,
> `NodeTwoForm.matrixValue`, `PrimitiveResidual.*`. Each must become `S.K`.
> This risk is mostly *self-detecting*: `NodeTwoForm.localForm_torus`
> (`:484-498`) closes with `rfl` against
> `SmoothPresentation.logarithmicImaginaryValue`, which stage A already moved to
> `(S.K i j : ℂ)`, and `TorusPrimitive.exteriorDerivative_alpha` ties `beta` to
> `matrixForm`; so a stage-B commit that leaves `S.B` in these places cannot
> compile. It is listed because it is the one place where "mechanical renaming"
> and "sign flip" coincide.

## 3. Form coefficient — PASS; the Lean form is the PDF form, not its negative

### Lean (`GeometryTarget.lean:79-86`)

```lean
def logarithmicImaginaryValue {S : Seed d} (P : SmoothPresentation S)
    (p : S.Point) (v w : P.manifold.Tangent p) : ℝ :=
  ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
    (S.K i j : ℂ) *
      ((P.coordinateDifferential i p v / p.a i) *
        (P.coordinateDifferential j p w / p.a j) -
       (P.coordinateDifferential i p w / p.a i) *
        (P.coordinateDifferential j p v / p.a j))).im
```

### PDF / blueprint

> `Ω_T = ½ ∑_{j,l} K_{jl} dlog z_j ∧ dlog z_l`  (`target-theorem.tex` §1;
> identically in `proof-blueprint.tex`, "On the initial torus put
> `Ω = ½ ∑_{j,l} K_{jl} d log z_j ∧ d log z_l`").
> Target theorem, item 2: `ω = dλ` is nondegenerate and `ω|_T = im Ω_T`.
> `∑_j K_{ij} dlog z_j = -d_i dlog t_i`;
> `Ω = ∑_{i∈I} d_i dlog t_i ∧ dlog x_i + Ω_0(t,s)`.

### Judgement — definite answer

With the convention `(α ∧ β)(v,w) = α(v)β(w) - α(w)β(v)` the Lean expression is
term-for-term `Im(½ ∑_{i,j} K_{ij} dlog a_i ∧ dlog a_j)`: the factor `½` is
present as in the PDF, the first index of `K` sits on the first tangent slot
exactly as the PDF's first `dlog` factor does, the cast is of the **rational**
`K = E·D̃` (not of `E`), and the real value is the imaginary part, matching
`ω|_T = im Ω_T`. **This is the PDF form with the same sign, no transpose and no
extra factor.** Three independent consistency checks:

1. Using `K^T = -K`, `½∑_{j,l}K_{jl}(ζ_j(v)ζ_l(w) - ζ_j(w)ζ_l(v)) = ∑_{j,l}K_{jl}ζ_j(v)ζ_l(w)`,
   so taking imaginary parts gives `Im Ω = ∑_{j,l} K_{jl} du_j ∧ dθ_l`, which is
   the blueprint's own torus formula ("On the initial torus,
   `Im Ω = ∑_{j,l} K_{jl} du_j ∧ dθ_l`"). A negated coefficient would
   contradict that line.
2. The node block: `∑_j K_{ij} dlog z_j = -d_i dlog t_i` with `K_{ij} = E_{ij}d_j`
   and `dlog t_i = ∑_j E_{ji} dlog z_j` holds precisely for `K i j = E i j * D j`,
   and yields the blueprint's `Ω = ∑_{i∈I} d_i dlog t_i ∧ dlog x_i + Ω_0`.
3. `ι_Z Im Ω = λ_tor + dH` with `λ_tor = u^T K dθ` reproduces the blueprint's
   `K^T u̇ = K^T u + ∂_θ H`, `-K θ̇ = ∂_u H` only with this index placement.

**Stage B1's `GlobalTwoForm.matrixForm` with coefficient `(S.K i j : ℂ)` is the
PDF form, not its negative.** Its shape is already pinned:

```lean
theorem matrixForm_apply (v : Fin 2 → (Fin d → ℂ)) :
    matrixForm S v = ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
      (S.B i j : ℂ) * (v 0 i * v 1 j - v 1 i * v 0 j)).im      -- GlobalTwoForm.lean:237
```

i.e. the same `(first index, first slot)` placement as
`logarithmicImaginaryValue`; substituting `S.K` for `S.B` therefore gives
`Im Ω_T` with the PDF's sign, and the Liouville field direction, the forward
orbit set and the skeleton `Skel(Φ)` are the PDF's. Keeping `S.B` there would
give `-Im Ω_T` at `D = 1` (since `S.B = Eᵀ = -K`) and reverse the flow; see R2.
**PASS.**

## 4. Recovery route — PASS on the convention choice; RISK R1 on the statement

### Lean (`SkewSeed.lean`)

```lean
structure SkewSeed (d : ℕ) where
  B : Matrix (Fin d) (Fin d) ℤ
  mutable : Finset (Fin d)
  skew : ∀ i j, B i j = -B j i
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < B i j)

def positiveMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ := ∏ j, a j ^ (S.B i j).toNat
def negativeMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ := ∏ j, a j ^ (-S.B i j).toNat

def toSeed : Seed d where
  E := S.B
  mutable := S.mutable
  D := fun _ => 1
  …

@[simp] theorem toSeed_K (i j : Fin d) : (S.toSeed).K i j = (S.B i j : ℚ)
theorem toSeed_positiveMonomial (a) (i) : (S.toSeed).positiveMonomial a i = S.negativeMonomial a i
theorem toSeed_monomial_sum (a) (i) :
    (S.toSeed).positiveMonomial a i + (S.toSeed).negativeMonomial a i =
      S.positiveMonomial a i + S.negativeMonomial a i
theorem carrier_set_eq : {x | old predicate} = {x | new predicate}
def pointHomeomorph : S.Point ≃ₜ (S.toSeed).Point
@[simp] theorem pointHomeomorph_val (p : S.Point) : (pointHomeomorph S p).val = p.val := rfl
```

### PDF / roadmap

> `target-theorem.tex`: "The old code uses row exchange exponents. For `D̃ = I`,
> row and column conventions only interchange the two monomials. … The
> implementation must use the column convention above, or prove an explicit
> transpose/convention equivalence preserving the exchange space, the sign of
> the form, and the same-flow skeleton identity."
> `roadmap.md`, acceptance check 2: "A proved recovery of the old `D = I`
> theorem, preserving the actual geometry and convention/sign matching."

### Judgement — definite answer on the convention choice

The choice `E := B` (rather than `E := Bᵀ`) is **correct and is the only one of
the two that recovers the old theorem**, for the reason given in the module
docstring and confirmed here:

* `toSeed_K : (S.toSeed).K i j = (S.B i j : ℚ)` — the weighted form coefficient
  of the image seed is *literally* the old integer matrix. Since the baseline's
  `logarithmicImaginaryValue` used `(S.B i j : ℂ)` and `docs/skeleton-audit.md`
  §1.5 certifies that this was the reference's `Im Ω` "with the same sign, no
  transpose and no extra factor", the weighted form at `D = 1, E := B` is
  pointwise the old form. No sign flip, hence no time reversal; and
  `trappedSet` (a *forward*-orbit condition) is not invariant under time
  reversal, so the alternative `E := Bᵀ` (giving `K = -B`) would have destroyed
  exactly the clause that acceptance check 2 is about. **PASS.**
* The price — the two monomials swap — costs nothing, because the exchange
  equation uses only their sum (`toSeed_monomial_sum`), so the carriers are the
  same subset of the ambient space (`carrier_set_eq`) and the canonical identity
  map is a homeomorphism with `pointHomeomorph_val = rfl`. Every predicate of
  the target that is phrased in ambient coordinates — `initialTorus`
  (`{p | ∀ j, p.a j ≠ 0}`), `coordinateCap`, `lambdaStratum`, and relative
  compactness of forward orbits — therefore transports verbatim, and
  `toSeed_independent_iff`/`toSeed_unimodular_iff` are `Iff.rfl`. **PASS.**

### The exact recovery theorem stage C must prove

Nothing in stage A yet *states* a recovery theorem, and the trivial
instantiation is not enough on its own: `LiouvilleSkeletonTarget S.toSeed` is a
statement about the type `(S.toSeed).Point`, whose defining predicate carries the
*swapped* monomials; a reviewer is entitled to ask for the old carrier. The
minimal adequate package is:

```lean
-- (a) the instantiation (one line, from the weighted theorem)
theorem SkewSeed.liouvilleSkeletonTarget {d : ℕ} (S : SkewSeed d)
    (hdet : S.Unimodular) : LiouvilleSkeletonTarget S.toSeed :=
  FullSkeleton.liouvilleSkeletonTarget S.toSeed (S.toSeed_unimodular_iff.mpr hdet)

-- (b) convention/sign matching: the torus anchor written with the OLD matrix
theorem SkewSeed.torus_anchor_old_matrix {d : ℕ} (S : SkewSeed d)
    (P : SmoothPresentation S.toSeed) (p : (S.toSeed).Point) (v w : _) :
    P.logarithmicImaginaryValue p v w =
      ((1 / 2 : ℂ) * ∑ i, ∑ j, (S.B i j : ℂ) *
        ((P.coordinateDifferential i p v / p.a i) * (P.coordinateDifferential j p w / p.a j) -
         (P.coordinateDifferential i p w / p.a i) * (P.coordinateDifferential j p v / p.a j))).im
-- immediate from toSeed_K; this is the clause that certifies "no sign flip"

-- (c) the objects of the old statement, transported along pointHomeomorph
--     (each is `rfl`-cheap because pointHomeomorph_val is rfl)
theorem SkewSeed.image_initialTorus :
    pointHomeomorph S '' {p : S.Point | ∀ j, p.a j ≠ 0} = initialTorus S.toSeed
theorem SkewSeed.image_coordinateCap :
    pointHomeomorph S '' {p : S.Point | (∀ f, f ∉ S.mutable → ‖p.a f‖ = 1) ∧
        ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧ ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0}
      = coordinateCap S.toSeed
theorem SkewSeed.image_lambdaStratum (I : Finset (Fin d)) :
    pointHomeomorph S '' {p : S.Point | (∀ i : S.Mutable, (i : Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧
        (∀ j, j ∉ I → ‖p.a j‖ = 1)} = lambdaStratum S.toSeed I
theorem SkewSeed.trappedSet_conj (Φ : Flow ℝ (S.toSeed).Point) :
    trappedSet (Φ.conj (pointHomeomorph S)) = pointHomeomorph S ⁻¹' trappedSet Φ
```

so that the old skeleton identity `Skel = C_B = ⋃_I Λ_I` on the old carrier is
the image of (a) under `pointHomeomorph`. Objects that must transport: the
initial torus, the coordinate cap, every stratum `Λ_I`, the forward orbits and
hence the trapped set, the smooth presentation (transport of a charted/manifold
structure along a homeomorphism), the primitive and the two-form (through (b)),
and the vector field/flow (conjugation). The independence index set needs no
transport (`toSeed_independent_iff` is `Iff.rfl`).

> **RISK R1 (stage C).** Two residual gaps, neither fatal, both worth stating in
> the handoff so stage C does not aim at the wrong statement:
>
> 1. **Term identity of the flow is not available, and is not needed.** The old
>    library's constructed objects are *not* the stage-B/C objects at `D = 1`:
>    the atlas differs (the baseline's node coordinates were
>    `(z_i, z_i'/P_i^+, 1/t_i)`, the reciprocal node; stage A's are the
>    reference's `(z_i, z_i'/P_i^-, t_i)` — see item 6 and the table), and
>    `TorusCorrection.H` changes value because its arguments `rowLog` and
>    `arg(-exchangeCharacter)` both flip sign (item 7). So "the same flow"
>    cannot be a Lean `rfl`. What *is* true, and is the right thing to claim:
>    both constructions produce the same `λ_tor = u^T K dθ` (at `D=1`,
>    `K = B_old`), and once stage B restores `α = β + dH` (R3) the Lean function
>    `α` is pointwise the baseline's `α` (because `H_new = -H_old` pointwise, by
>    `rho` even and `vartheta` odd — the two sign flips cancel a second time), so
>    the Liouville field is the same vector field by uniqueness
>    (`LiouvilleData.field_eq_liouvilleVector`) and the flow is the same flow.
>    Recovery should nevertheless be stated at the level of the **existential**
>    target (`LiouvilleSkeletonTarget`), which is what the PDF quantifies
>    (`∀(n,E,D̃,M) ∃(smooth structure, λ, Z, Φ)`), rather than as an equality of
>    constructed terms. Only the skeleton *set* and the torus-anchored form are
>    pinned by the statement; that is exactly what acceptance check 2 asks for.
> 2. `pointHomeomorph` is a homeomorphism, not yet a diffeomorphism. Clause (c)
>    above transports the topological content; transporting a *smooth* structure
>    requires pushing `SmoothPresentation` along it (routine, since the chart
>    source data is the ambient coordinate inclusion and `pointHomeomorph_val`
>    is `rfl`), or stating recovery directly for `S.toSeed` as in (a)+(b)+(c).
>    State which, and do not leave the old smooth structure implicitly claimed.

## 5. `Examples/NonSkew` — PASS

### Lean (`ClusterSkeleton/Examples/NonSkew.lean`)

```lean
def nonSkewMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, -1, 0;
    -2, 0, 0, -1;
     1, 0, 0, 0;
     0, 1, 0, 0]
def nonSkewWeights : Fin 4 → ℚ := ![1, 2, 1, 2]
def nonSkewMutable : Finset (Fin 4) := {0, 1}
def nonSkewSeed : Seed 4 where E := nonSkewMatrix; mutable := nonSkewMutable; D := nonSkewWeights; …

theorem nonSkewSeed_unimodular : nonSkewSeed.Unimodular
theorem nonSkewSeed_not_skew : ¬ ∀ i j, nonSkewSeed.E i j = -nonSkewSeed.E j i
theorem nonSkewSeed_entries : nonSkewSeed.E 0 1 = 1 ∧ nonSkewSeed.E 1 0 = -2
theorem nonSkewSeed_weights_ne : nonSkewSeed.D 0 ≠ nonSkewSeed.D 1
theorem nonSkewSeed_K_transpose : nonSkewSeed.Kᵀ = -nonSkewSeed.K
theorem nonSkewSeed_det_K : nonSkewSeed.K.det = 4
```

### PDF (`target-theorem.tex`, §4) and roadmap check 3

> `E = ((0,1,-1,0),(-2,0,0,-1),(1,0,0,0),(0,1,0,0))`, `D̃ = diag(1,2,1,2)`,
> `M = {1,2}`. Here `det E = 1`, `E D̃` is skew-symmetric, and the mutable quiver
> is acyclic, but `E_{12} = 1 ≠ 2 = -E_{21}`.

### Judgement

* **Row-by-row identity.** `!![0,1,-1,0; -2,0,0,-1; 1,0,0,0; 0,1,0,0]` is the
  PDF matrix row by row. **[elab]** `#eval` over `List.finRange 4` printed
  `[[0, 1, -1, 0], [-2, 0, 0, -1], [1, 0, 0, 0], [0, 1, 0, 0]]`, the weights
  `[1, 2, 1, 2]`, and `nonSkewMutable = {0,1}` (`decide` = `true`; membership
  vector `[true, true, false, false]`), i.e. `M = {1,2}` one-based.
* **All five facts are PROVED theorems, not definitions**, and all four
  structure fields of `nonSkewSeed` are discharged by `fin_cases`/`norm_num`
  (positivity, skew-symmetrizability, acyclicity) rather than assumed.
  **[elab]** `#print axioms` on `nonSkewSeed_unimodular` and
  `nonSkewSeed_not_skew` reports only `propext, Classical.choice, Quot.sound`.
* **[elab]** independent numeric confirmation: `det E = 1`;
  `K = [[0,2,-1,0],[-2,0,0,-2],[1,0,0,0],[0,2,0,0]]`, which is visibly skew;
  `det K = 4 = 1 · (1·2·1·2)`, consistent with `det_K`; the mutable block of `E`
  is `[[0,1],[-2,0]]`, a single arrow `0 → 1`, hence acyclic.
* `nonSkewSeed_not_skew` is the PDF's "but `E_{12} = 1 ≠ 2 = -E_{21}`", with the
  witness recorded separately in `nonSkewSeed_entries`.
* **Is this the `Seed` instance the final theorem will be applied to?** Yes.
  `FirstGeometricTarget : ∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S`,
  and **[elab]** `fun h => h 4 Examples.nonSkewSeed Examples.nonSkewSeed_unimodular`
  elaborates at type `FirstGeometricTarget → LiouvilleSkeletonTarget Examples.nonSkewSeed`.
  The same check passes for `a2Seed` (the restated `D = 1` example).
  **PASS.**

> **RISK R4 (stage C).** Roadmap check 3 asks for "a **consumer** instantiating
> the final theorem" on this input. Stage A delivers the seed plus the
> hypothesis facts, which is all that is possible before the theorem exists; the
> remaining obligation is literally the line
> `theorem nonSkewSeed_target : LiouvilleSkeletonTarget nonSkewSeed := FullSkeleton.liouvilleSkeletonTarget _ nonSkewSeed_unimodular`
> (verified above to typecheck modulo the hypothesis), and it must be added at
> stage C. Related scope note for check 5: `LiouvilleSkeletonTarget` contains
> only density, the presentation/`LiouvilleData` witnesses, the torus anchor and
> `trappedSet = coordinateCap`. The PDF's theorem also asserts
> `C_E = ⋃_I Λ_I`, compactness of each `Λ_I`, and the node-chart shape
> `N^I × (C^*)^{n-2|I|}` with `2|I| ≤ n`. In the library these are the separate
> `coordinateCap_eq_iUnion_lambdaStratum`, `isCompact_lambdaStratum`
> (`CapStrata.lean:85`), `IndependentNodeChart.homeomorph` and
> `IndependentNodeChart.complementRank_eq_sub_two_mul_card` /
> `two_mul_card_le` (`IndependentNodeSmooth.lean:251,264`), all unchanged and
> still proved at `de58cd2`. This split is inherited from the accepted baseline
> and is not a stage A regression, but the final consumer and the check-5 review
> must cite all of them, not `FirstGeometricTarget` alone.

## 6. Baseline fidelity — PASS

The complete diff `e62c101..de58cd2` touches 12 files. Beyond the mechanical
`E`/`B`/`K` renaming, these are *all* the statement-shape changes:

| # | Declaration | Change | Forced by the weighted target? |
| --- | --- | --- | --- |
| 1 | `Seed` | fields `B, mutable, skew, acyclic` → `E, mutable, D, D_pos, skewSymmetrizable, acyclic` | forced (item 1) |
| 2 | `Seed.Unimodular` | `S.B.det = 1` → `S.E.det = 1` | forced; **no change in strength**: `S.B = S.Eᵀ`, and `Seed.B_det` re-proves `S.B.det = 1` from it, so every old consumer gets its old hypothesis back |
| 3 | `Seed.positiveMonomial` / `negativeMonomial` | row exponents `[±B_{ij}]_+` → column exponents `[±E_{ji}]_+` | forced (PDF: "The implementation must use the column convention"). Net effect: the carrier changed *meaning* from "the reference variety of `B` with the monomials interchanged" (audit §1.2) to "the reference variety of `E`, literally". For skew `E` the two carriers are the same **set** (`SkewSeed.carrier_set_eq`), as the PDF says they must be |
| 4 | `Seed.Independent` | `S.B i j = 0` → `S.E i j = 0` for all `i,j ∈ I` | equivalent (same equation set, reindexed); `Independent.exponent_eq_zero` supplies the exponent orientation. Neither weakening nor strengthening |
| 5 | `ZeroSet.matrix_eq_zero_of_coordinates_zero` | conclusion `S.B i j = 0` → `S.E i j = 0` | equivalent: the statement is universally quantified in `i, j`, and `S.E i j = 0 ↔ S.E j i = 0` (`E_eq_zero_iff`). Not a weakening |
| 6 | `ZeroSet.outgoing_ne_zero`, `CapIndependence.coordinateCap_outgoing_not_interior` | statement text unchanged (`0 < S.B i j`), **meaning** changed to `0 < S.E j i`; induction switched from `S.acyclic.induction` to `S.acyclic_exponent.induction` | forced, and now *closer* to the blueprint: the hypothesis reads "`j` occurs in `P_i^+`", which is exactly the blueprint's `B_{j_{r-1}i} > 0 ⇒ P_i^+(p) = 0` step. See **DEFECT D2** for the stale word "outgoing" |
| 7 | `NodeCoordinates.exchangeCharacter_eq_zpow_product`, `IndependentNodeChart.row_product_eq_outside`, `recovered_ratio` | `∏ j, a j ^ S.B i j` → `∏ j, a j ^ S.E j i` | **`rfl`-level**: the two expressions are definitionally equal (`B_apply`). Cosmetic. But the *mathematical content* of `exchangeCharacter` changed with item 3 of this table: see **DEFECT D1** |
| 8 | `CapIndependence.norm_eq_one_of_not_strict` | new; `CapAngularTangency.norm_eq_one_of_not_strict` retained as a one-line alias with the identical statement; `CapStrata` drops `import CapAngularTangency` | not forced, but a genuine **improvement** and no statement change: the stratified cap identity no longer depends on the flow modules of stages B/C. Not a weakening |
| 9 | `GeometryTarget.SmoothPresentation.logarithmicImaginaryValue` | coefficient `(S.B i j : ℂ)` → `(S.K i j : ℂ)` | forced; **the only real statement change in a target-level definition** (item 3). Correct, and it is what pins the form sign for stage B |
| 10 | `Examples.a2Seed` | restated as a weighted seed with `D = 1`, plus `a2Seed_D_eq_one`, `a2Seed_K_eq` | forced; `a2Seed_unimodular`, `a2_not_both_zero` unchanged |
| 11 | new `SkewSeed`, `Examples/NonSkew`, two imports in `ClusterSkeleton.lean` | additions only | required by acceptance checks 2 and 3 |

Explicitly **unchanged in shape and in meaning** (checked against the PDF):

* `Seed.Point.exchange`, `frozen_ne_zero`, `zeroSet`, `zeroSet_independent`.
* `CapSet.coordinateCap = {p | (∀ f ∉ mutable, ‖p.a f‖ = 1) ∧ ∀ i : Mutable, ‖p.a i‖ ≤ 1 ∧ ((1 - ‖p.a i‖^2 : ℝ) : ℂ) * p.b i = 0}`
  — literally the PDF's `C_E = {|z_f| = 1 (f∈F), |z_i| ≤ 1, (1-|z_i|²)z_i' = 0 (i∈M)}`.
  Purely ambient, so convention-free.
* `CapStrata.lambdaStratum S I = {p | (∀ i : Mutable, i ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧ (∀ j ∉ I, ‖p.a j‖ = 1)}`
  — the PDF's `Λ_I = {z_i' = 0, |z_i| ≤ 1 (i∈I), |z_j| = 1 (j∉I)}`; and
  `coordinateCap_eq_iUnion_lambdaStratum`, `isCompact_lambdaStratum` unchanged.
* `CoordinateLoci.initialTorus S = {p | ∀ j, p.a j ≠ 0}` — the PDF's
  `T = {z_1⋯z_n ≠ 0}`; `TrappedSet.trappedSet flow = {x | IsCompact (closure (flow.forwardOrbit x))}`
  — the PDF's `Skel(Φ)`, with the closure in the subtype topology ("The closure
  is taken in the actual exchange space").
* **Chart dimension `n - 2|I|`:** `IndependentNodeSmooth.lean:264`
  `complementRank (independentRowRightInverse S I) = d - 2 * I.card` and
  `:251 two_mul_card_le : 2 * I.card ≤ d`, untouched and still proved. Their
  input `independent_rows_inverse_pairing` is now the blueprint statement
  *exactly*: the rows of `S.B = Eᵀ` indexed by `I` are the reference columns
  `c_i = E e_i`, and `S.B⁻¹ = (E⁻¹)ᵀ` is the blueprint's "the integer inverse of
  `E` restricts to a retraction". The baseline reached the same statement only
  because `B` was skew.
* `SmoothAtlas.presentation`, `dense_initialTorus`, `LiouvilleSkeletonTarget`,
  `FirstGeometricTarget` — unchanged apart from now quantifying over the
  weighted seed.

No silent weakening or strengthening of a hypothesis was found: no declaration
in the diff gained or lost a hypothesis, and the two statements whose conclusion
was re-oriented (#5, #7) are interderivable with their baseline forms.

### DEFECT D1 — `exchangeCharacter_eq_zpow_product` docstring asserts the opposite of its statement

**Declaration.** `ClusterSkeleton.exchangeCharacter_eq_zpow_product`,
`ClusterSkeleton/NodeCoordinates.lean:55-60`.

```lean
/-- The exchange ratio is the Laurent monomial with the actual signed column of
`E`, i.e. the reference's inverse character `1/t_i`. -/
theorem exchangeCharacter_eq_zpow_product (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i) := …
```

**Discrepancy.** The PDF defines `c_i = E e_i` and
`t_i = z^{c_i} = P_i^+/P_i^-`, i.e. `t_i = ∏_j z_j^{E_{ji}}`. With the stage A
column monomials, `exchangeCharacter p i = positiveMonomial/negativeMonomial`
is therefore **`t_i`, not `1/t_i`**. **[elab]** confirmed:
`exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i)` and
`∏ j, p.a j ^ ((S.E.mulVec e_i) j) = ∏ j, p.a j ^ (S.E j i)` both elaborate, so
the Lean character is literally `z^{c_i}`. The docstring reproduces the
*baseline's* relation (`docs/skeleton-audit.md` §1.3: "`exchangeCharacter p i =
(t_i)⁻¹`"), which stage A's own convention change inverted. The same inversion
makes `normalizedPartner p i = p.b i / negativeMonomial p.a i` equal to the
reference's `y = z_i'/P_i^-` (baseline: `y/t_i`), so
`normalized_node_equation : p.a i * normalizedPartner p i = 1 + exchangeCharacter p i`
is now the reference node `x y = 1 + t` on the nose rather than in reciprocal
coordinates.

**Why it matters (not a nit).** This docstring is the single sentence a stage B
worker will read when re-deriving the `H` and `α` signs that the stage A handoff
explicitly defers ("the sign bookkeeping of `H` and `alpha = beta - dH` in §1.6
must be re-derived in stage B"). Taken at face value it reproduces the
baseline's cancellation (`rho` even, `vartheta` odd) and yields
`α = λ_tor - dH_ref`, i.e. the wrong primitive — see R3.

**Minimal proposed fix (statement level: none; documentation only).** Replace
the docstring by: "The exchange ratio is the reference character
`t_i = z^{c_i} = ∏_j z_j^{E_{ji}}` with `c_i = E e_i` (the baseline's
`exchangeCharacter` was `1/t_i`; the column convention inverts it, and
`normalizedPartner` is now the reference's `y = z_i'/P_i^-`)." Optionally add
the pinning lemma
`theorem exchangeCharacter_eq_character (p : S.Point) (i : Fin d) : exchangeCharacter p i = ∏ j, p.a j ^ ((S.E.mulVec (fun k => if k = i then 1 else 0)) j)`
so the identification with `z^{c_i}` is machine-checked rather than read.

**Downstream stage affected.** B1 and B2 (`TorusCorrection.H`, `TorusPrimitive.alpha`,
`PrimitiveLocalization.angle`, `TorusLiouvilleDynamics.angular_equation`), and
through them stage C (the skeleton inclusions).

### DEFECT D2 — `outgoing_ne_zero` is now about incoming arrows

**Declaration.** `ClusterSkeleton.Seed.Point.outgoing_ne_zero`,
`ClusterSkeleton/ZeroSet.lean:18-22`.

```lean
/-- A zero mutable coordinate has no zero outgoing mutable neighbor. Here
`0 < S.B i j` is the column exponent condition `0 < S.E j i`, i.e. the
coordinate `j` occurs in the positive exchange monomial of `i`. -/
theorem outgoing_ne_zero :
    ∀ i : S.Mutable, p.a i = 0 → ∀ j : S.Mutable, 0 < S.B i j → p.a j ≠ 0
```

**Discrepancy.** `Seed`'s own docstring fixes the arrow convention as "`E i j > 0`
for an arrow from `i` to `j`". The hypothesis `0 < S.B i j` is `0 < S.E j i`,
i.e. an arrow **`j → i`**: `j` is a predecessor of `i`, not an outgoing
neighbour. The statement is correct and matches the blueprint (`B_{j_{r-1}i}>0`
forces `P_i^+(p)=0`); only the name and the first clause of the docstring are
stale. The second sentence of the docstring already says the right thing, so the
file is self-contradictory.

**Minimal proposed fix.** Statement unchanged. Either rename to
`incoming_ne_zero` (a rename ripples into `ZeroSet`/`CapIndependence` proofs, so
it is stage B's call) or drop the word "outgoing" from the docstring: "A zero
mutable coordinate has no zero mutable predecessor". The analogous
`CapIndependence.coordinateCap_outgoing_not_interior` carries the same stale
word.

**Downstream stage affected.** None mathematically; it is a readability defect
in the two modules whose orientation is hardest to re-check.

## 7. The weighted convention table

Old Lean = accepted baseline at `e62c101` (as certified in
`docs/skeleton-audit.md` §1.2–1.6); reference = `target-theorem.tex` /
`proof-blueprint.tex`; new Lean = `de58cd2`. `u_j = log‖z_j‖`, `θ_j = arg z_j`.

| role | old Lean (`e62c101`) | reference (PDF) | new Lean (`de58cd2`) | status |
| --- | --- | --- | --- | --- |
| exchange matrix | `S.B`, skew (`S.skew`) | `E ∈ GL_n(Z)`, not skew; `K = E D̃` skew | `S.E` (not skew), `S.D`, `S.K i j = E i j * D j` | done |
| exponent matrix | rows `S.B i j` | columns `[±E_{ji}]_+` | `S.B i j := S.E j i` (`S.B = S.Eᵀ`, `B_apply` by `rfl`) | done |
| `P_i^+` | `∏ j, a j ^ (B i j).toNat` = reference `P_i^-` (interchanged) | `∏_j z_j^{[E_{ji}]_+}` | `∏ j, a j ^ (E j i).toNat` = reference `P_i^+` | done, literal |
| carrier | reference variety of `B`, monomials swapped | `X_E` | `X_E` literally | done |
| `t_i` | `exchangeCharacter p i = 1/t_i` | `t_i = P_i^+/P_i^- = z^{c_i}`, `c_i = E e_i` | `exchangeCharacter p i = t_i` | **sign flipped vs baseline**; docstring still says `1/t_i` (**D1**) |
| node partner `y` | `normalizedPartner = y/t_i` | `y = z_i'/P_i^-` | `normalizedPartner = y` | done, literal |
| node equation | `x·(y t) = 1 + 1/t` (reciprocal node) | `x y = 1 + t` | `p.a i * normalizedPartner = 1 + exchangeCharacter` | done, literal |
| `v_i` | `rowLog p i = ∑_j B_{ij} u_j = -v_i` | `v_i = log|t_i| = c_i(u) = ∑_j E_{ji} u_j` | `rowLog p i = ∑_j S.B i j * u_j = +v_i` (unchanged text, flipped meaning) | **flipped**; stage B must re-derive |
| `η_i - π` | `arg(-exchangeCharacter) = -(η_i-π)` | `η_i = arg t_i = c_i(θ)`, `Log(-t_i) = v_i + i(η_i-π)` | `arg(-exchangeCharacter) = +(η_i-π)`; `nodeLog = +Log(-t_i)` | **flipped**; stage B must re-derive |
| form coefficient | `(S.B i j : ℂ)`, `= K_{ij}` since `B` skew | `Ω_T = ½ ∑_{j,l} K_{jl} dlog z_j ∧ dlog z_l` | `(S.K i j : ℂ)` in `logarithmicImaginaryValue` | done; **`S.B` here is now `S.B i j = E_{ji} = -K_{ij}/d_i`, i.e. `-K` at `D = I`** (**R2**) |
| form sign | `= +Im Ω` (audit §1.5) | `ω|_T = im Ω_T` | `= +Im Ω` | **PASS (item 3)**: PDF form, not its negative |
| `λ_tor` | `beta = ∑_{i,j} (B i j) u_i dθ_j = u^T K dθ` | `λ_tor = u^T K dθ` | must become `∑_{i,j} (K i j) u_i dθ_j` (still `S.B` at `de58cd2`) | **stage B1 action** (R2) |
| `H` | `H_Lean = -H_ref` (no `d_i`, correct at `D=I`) | `H = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)` | with the flipped `rowLog`/`angular`, `H_Lean = +H_ref` **except that the weights `d_i` are still missing** | **stage B action** (R3) |
| primitive | `alpha = beta - dH_Lean = λ_ac` | `λ_ac = λ_tor + dH` | **expected: `alpha = beta + dH`** (both sign flips of the baseline are gone; equivalently negate `H`) | **stage B action** (R3) |
| form determinant | `det B = 1` | `det K = det E ∏ d_i > 0` | `det_K`, `det_K_of_unimodular : K.det = ∏ i, D i`, `det_K_ne_zero`, `isUnit_det_K` | done |
| integer inverse | `S.B⁻¹`, `det B = 1` | `E^{-1}` restricts to a retraction; `c_i` extend to a basis of `Z^{(M⊔F)\I}` | `S.B⁻¹ = (E⁻¹)ᵀ`, `S.B_det hdet : S.B.det = 1` | done, now literal |
| dynamics inverse | `B⁻¹` | `θ̇ = -K^{-1} ∂_u H`, `c_i(K^{-1}x) = -x_i/d_i` | stage C: `K⁻¹` (rational) | pending (stage C) |
| acyclicity | `WellFounded (0 < S.B i j)` | arrows `B_{ij} > 0` on `M` acyclic | field on `0 < S.E i j`; `acyclic_exponent` bridges to `0 < S.B i j` | done |
| `Unimodular` | `S.B.det = 1` | `E ∈ GL_n(Z)`, hence `det E = 1` | `S.E.det = 1` (+ `B_det`) | done (M1) |

Two mandatory stage-B actions follow from the table:

> **RISK R3 (stages B1, B2, C).** `TorusCorrection.H` must gain the factor `d_i`
> per summand (the reference's `H = ∑_{i∈M} d_i h(u_i)χ_iρ(v_i)β(η_i)`; the
> weights cancel only in the *radial* equation, cf. `target-theorem.tex` §4 and
> `roadmap.md`), and `TorusPrimitive.alpha` must become `beta + dH` (or `H` must
> be negated) because stage A removed both sign inversions that made
> `alpha = beta - dH` correct in the baseline. **This error is invisible to the
> target's torus anchor**: `alpha = beta ± dH` differ by an exact form, so
> `d alpha` — and hence the clause
> `evalTwo (exteriorDerivative L.primitive) = logarithmicImaginaryValue` of
> `LiouvilleSkeletonTarget` — cannot detect it. The only statement that detects
> it is `trappedSet = coordinateCap` itself, i.e. stage C's skeleton inclusions
> (where the radial estimate `u̇_i ≤ u_i - h(u_i) < 0` fails outright for the
> wrong sign). It must therefore be settled by derivation in stage B, not left
> to be discovered by a failing build.

## Downstream impact summary

* **Stage B1 (weighted form and primitive).** D1 (the `t_i` docstring), R2 (the
  five remaining `S.B` form-coefficient sites), R3 (`H` weights and the `α` sign).
  Nothing in stage A's *statements* obstructs B1; the form sign it must implement
  is fixed and is the PDF's (item 3).
* **Stage B2 (field, bounds, complete flow).** R3 propagates: the field is the
  Liouville field of `α`, and the radial/angular equations of
  `proof-blueprint.tex` eq. (acyclic-flow)/(acyclic-angle-flow) must be
  re-derived in the new sign convention (`rowLog = +v`, `arg(-t) = +(η-π)`), not
  copied from `docs/skeleton-audit.md` §1.7.
* **Stage C (skeleton assembly and recovery).** R1 (state the recovery theorem
  as (a)+(b)+(c) of item 4 and decide the smooth-structure transport), R4 (add
  the `nonSkewSeed` consumer line; cite the stratified union, `Λ_I`
  compactness and the chart rank alongside `FirstGeometricTarget`).
* **No stage is blocked by a stage A statement defect.** The foundation says
  what the PDF says for items 1–3 and 5, and the recovery route of item 4 is the
  correct one of the two available choices.

## Appendix A — elaboration checks

Run at the repository root of this branch with
`horizon-lean-check --lean Scratch.lean` (toolchain `leanprover/lean4:v4.34.1`,
pinned Mathlib/FsFltz; `Scratch.lean` deleted before committing). All
`example`s below elaborated with no errors; no Lean file in the tree was
modified.

```lean
-- item 1
example (S : Seed d) (i j : Fin d) : S.K i j = (S.E i j : ℚ) * S.D j := rfl
example (S : Seed d) : S.Unimodular = (S.E.det = 1) := rfl
example (S : Seed d) (I : Finset (Fin d)) :
    S.Independent I = (I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.E i j = 0) := rfl
-- item 2
example (S : Seed d) (a) (i) : S.positiveMonomial a i = ∏ j, a j ^ (S.E j i).toNat := rfl
example (S : Seed d) (a) (i) : S.negativeMonomial a i = ∏ j, a j ^ (-S.E j i).toNat := rfl
example (S : Seed d) (i j : Fin d) : S.B i j = S.E j i := rfl
-- item 6 / D1: the exchange character is the reference t_i = z^{c_i}, c_i = E e_i
example (S : Seed d) (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = S.positiveMonomial p.a i / S.negativeMonomial p.a i := rfl
example (S : Seed d) (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i) := exchangeCharacter_eq_zpow_product p i
example (S : Seed d) (p : S.Point) (i : Fin d) :
    (∏ j, p.a j ^ ((S.E.mulVec (fun k => if k = i then (1:ℤ) else 0)) j)) =
      ∏ j, p.a j ^ (S.E j i) := by …
-- item 4
example (S : SkewSeed d) (i j : Fin d) : (S.toSeed).K i j = (S.B i j : ℚ) := S.toSeed_K i j
example (S : SkewSeed d) (a) (i) :
    (S.toSeed).positiveMonomial a i = S.negativeMonomial a i := S.toSeed_positiveMonomial a i
-- item 5
example (h : FirstGeometricTarget) : LiouvilleSkeletonTarget Examples.nonSkewSeed :=
  h 4 Examples.nonSkewSeed Examples.nonSkewSeed_unimodular
example (h : FirstGeometricTarget) : LiouvilleSkeletonTarget Examples.a2Seed :=
  h 2 Examples.a2Seed Examples.a2Seed_unimodular
```

Numeric output (`#eval`):

```
nonSkewMatrix      [[0, 1, -1, 0], [-2, 0, 0, -1], [1, 0, 0, 0], [0, 1, 0, 0]]
nonSkewWeights     [1, 2, 1, 2]
nonSkewSeed.K      [[0, 2, -1, 0], [-2, 0, 0, -2], [1, 0, 0, 0], [0, 2, 0, 0]]
nonSkewMatrix.det  1
nonSkewSeed.K.det  4
nonSkewMutable     = {0, 1}  (decide = true; membership [true, true, false, false])
mutable block of E [[0, 1], [-2, 0]]
```

`#print axioms` on `Examples.nonSkewSeed_unimodular`,
`Examples.nonSkewSeed_not_skew`, `SkewSeed.carrier_set_eq`,
`SkewSeed.pointHomeomorph`, `Seed.acyclic_exponent`, `Seed.det_K`:
`[propext, Classical.choice, Quot.sound]` in every case.
