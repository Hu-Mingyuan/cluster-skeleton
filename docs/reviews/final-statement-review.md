# Final statement review — the generalized theorem at stage C versus the PDFs

Acceptance check 5 of objective `7d3240fc-f412-49c4-88c8-a9d1a5a1bdaf` revision 2
(`docs/roadmap.md` @ `e62c101`), with checks 1 and 4 at statement level.

* **Reviewed tree:** stage-C commit `114d63939d72cfb5c81d6bd22dd0811e053805a3`
  (branch `weighted/stage-c`). That commit is not reachable in this checkout, so
  every path was fetched through the repository file API and committed first; the
  `git hash-object` of each written file reproduces the remote `blob_oid` exactly,
  and every remaining path of `e62c101` was confirmed byte-identical at `114d639`
  by `blob_oid` comparison. The reproduced tree is complete: the import closure of
  `ClusterSkeleton.lean` is 62 modules + the root and references no absent module.
* **Reference:** `docs/tex/target-theorem.tex` (Theorem `thm:target`) and
  `docs/tex/proof-blueprint.tex` (Theorem `thm:acyclic-skeleton` and the acyclic
  flow equations), both byte-identical at `114d639` to `e62c101`.
* **Method:** statement reading, not a build check. Where a reading could be
  wrong, it was turned into a Lean `rfl`/`example` and elaborated (Appendix A).
  The full library was built once (`horizon-lean-check ClusterSkeleton`:
  `passed`, 3750 jobs, Lean 4.34.1 / Lake 5.0.0) only so that `lake env lean`
  could elaborate the scratch checks. No Lean or `verification/` file was
  modified; the scratch file was deleted before committing.
* **Earlier reviews cited, not redone:** `docs/reviews/stage-a-semantic-audit.md`
  @ `4fe163223e348afdd4e0214970c451b797bb06c8` (items 1–3, 5, 6 and risks
  R1–R4). The stage-B semantic audit could **not** be cited: the newest verified
  publication of assignment `60e8be8f-62b6-4d17-adb7-be01d0426f47` at the time of
  reading is `71f783b3d006195debb38929eeb44b9b35a0408a`
  (created 2026-11-10T00:32:32Z), and
  `GET .../file?commit_oid=71f783b3…&path=docs/reviews/stage-b-semantic-audit.md`
  returns 404, as does the same path on the previous verified commit
  `eb356ed8007761260aac736191971beebb250991`. The B-level facts this report needs
  (the primitive, `H`, the O1 sign) were therefore re-derived from scratch in
  item 5 rather than cited.
* The stage-C handoff (obligation `ba2f64dc`, assignment `c208ef62`) was read and
  then verified independently. Every claim of it that this report checked is
  correct; one of its lists is reported as incomplete in item 7 (`GeometryTarget.lean`
  is *not* byte-identical to `e62c101` — it was changed in stage A, as the stage-A
  audit records; the handoff only claimed stage-C modules were unchanged).

## Verdict summary

| # | Item | Verdict |
| --- | --- | --- |
| 1 | Exact theorem type, fully unfolded | **PASS** |
| 2 | Input: `Seed` fields, `Unimodular`, no hidden skewness / `D = 1` / equal weights | **PASS** |
| 3 | Space: PDF variety, column exponents, constructed smooth structure | **PASS** |
| 4 | Logarithmic form: `K = E·D`, factor `1/2`, sign, imaginary part symplectic on all of `X_E` | **PASS** |
| 5 | Flow: `λ_ac = λ_tor + dH`, Liouville field, complete and constructed; blueprint equations | **PASS** |
| 6 | Conclusions: every PDF clause mapped | **RISK R4** — three PDF clauses are proved but live *outside* `LiouvilleSkeletonTarget` |
| 7 | Diff against the baseline and the `D = 1` specialization | **PASS** |
| 8 | Audit inventory and axioms | **PASS** on the axioms; **DEFECT A1** — `verification/AxiomAudit.lean` no longer covers four modules |
| 9 | Replacement `statement-review.md` | **delivered** (Appendix B) |

Findings:

| id | kind | declaration / file | final assembly (`3e612104`) affected? |
| --- | --- | --- | --- |
| R4 | RISK (acceptance scope, carried from stage A) | `ClusterSkeleton.FirstGeometricTarget` consumers | no statement change needed; see item 6 for the citation list |
| A1 | DEFECT (verification coverage) | `verification/AxiomAudit.lean` module list | **no** — `verification/` belongs to the receipts mission |
| D1 | DEFECT (docstring contradicts its statement; carried from stage A, unfixed at `114d639`) | `ClusterSkeleton.exchangeCharacter_eq_zpow_product` | **yes, bookkeeping only** — the fix already exists on `weighted/recovery-scaffold` @ `e7a6d96`; final assembly must not lose it in the merge |
| D2 | DEFECT (stale name/docstring orientation; carried from stage A, unfixed at `114d639`) | `ClusterSkeleton.Seed.Point.outgoing_ne_zero` | same as D1 |

**No hidden hypothesis, no assumed flow, no assumed skeleton equality and no
wrong field direction was found.** The URGENT-DEFECT rule of the mission did not
fire. Items 2, 5 and 6 have definite negative answers to all three questions;
the evidence is in the corresponding sections.

---

## 1. Exact theorem type — PASS

### The three declarations, as printed at `114d639`

```lean
theorem ClusterSkeleton.FullSkeleton.firstGeometricTarget : FirstGeometricTarget :=
fun d S hdet => FullSkeleton.liouvilleSkeletonTarget S hdet

def ClusterSkeleton.FirstGeometricTarget : Prop :=
∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S

def ClusterSkeleton.LiouvilleSkeletonTarget : {d : ℕ} → Seed d → Prop :=
fun {d} S =>
  Dense (initialTorus S) ∧
    ∃ P L,
      (∀ p ∈ initialTorus S,
          ∀ (v w : P.manifold.Tangent p),
            FsFltz.Geometry.SmoothManifold.evalTwo
                (P.manifold.exteriorDerivative L.primitive) p v w =
              P.logarithmicImaginaryValue p v w) ∧
        trappedSet L.completeFlow.flow = coordinateCap S
```

`#check @ClusterSkeleton.FullSkeleton.firstGeometricTarget` prints
`FullSkeleton.firstGeometricTarget : FirstGeometricTarget` — **no binder of any
kind, in particular no instance argument**.

### Fully unfolded statement

Every `ClusterSkeleton` and `FsFltz` definition occurring in the type was inlined
by hand and the result was checked against the real target by the kernel:

```lean
example : FirstGeometricTarget = UnfoldedTarget := rfl   -- elaborates, Appendix A
```

with (`cdiff P j p` is literally the body of
`SmoothPresentation.coordinateDifferential`, i.e.
`mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*d))) 𝓘(ℝ, ℂ) (fun q : S.Point => q.val.1 j) p`):

```lean
def UnfoldedTarget : Prop :=
  ∀ (d : ℕ) (S : Seed d),
    S.E.det = 1 →                                                   -- Seed.Unimodular
    Dense {p : {x : (Fin d → ℂ) × ({i : Fin d // i ∈ S.mutable} → ℂ) //   -- Seed.Point
          (∀ i : {i : Fin d // i ∈ S.mutable},
              x.1 i.val * x.2 i
                = (∏ j, x.1 j ^ (S.E j i.val).toNat)                -- Seed.positiveMonomial
                + (∏ j, x.1 j ^ (-S.E j i.val).toNat)) ∧            -- Seed.negativeMonomial
            (∀ f, f ∉ S.mutable → x.1 f ≠ 0)} |
        ∀ j : Fin d, p.val.1 j ≠ 0} ∧                               -- initialTorus
    ∃ (P : SmoothPresentation S),
      letI : ChartedSpace (EuclideanSpace ℝ (Fin (2 * d))) S.Point := P.charts
      ∃ (L : LiouvilleData P),
      (∀ p : S.Point, (∀ j : Fin d, p.val.1 j ≠ 0) →
        ∀ v w : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d)))) p,
          ((extDeriv                                                -- SmoothManifold.exteriorDerivative
              (fun y => (L.primitive ((chartAt (EuclideanSpace ℝ (Fin (2*d))) p).symm y)
                          ).compContinuousLinearMap                 -- SmoothManifold.formInChart
                (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*d))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*d)))
                  (chartAt (EuclideanSpace ℝ (Fin (2*d))) p).symm y))
              (chartAt (EuclideanSpace ℝ (Fin (2*d))) p p)).compContinuousLinearMap
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*d))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*d)))
              (chartAt (EuclideanSpace ℝ (Fin (2*d))) p) p)) ![v, w]   -- evalTwo
            = ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,              -- logarithmicImaginaryValue
                (((S.E i j : ℚ) * S.D j : ℚ) : ℂ) *                 -- Seed.K i j
                  ((cdiff P i p v / p.val.1 i) * (cdiff P j p w / p.val.1 j)
                    - (cdiff P i p w / p.val.1 i) * (cdiff P j p v / p.val.1 j))).im) ∧
      {x : S.Point |                                                -- trappedSet
          IsCompact (closure (Set.range fun t : ↥(AddSubmonoid.nonneg ℝ) =>
            L.completeFlow.flow.toFun t.val x))}                     -- Flow.forwardOrbit
        = {p : S.Point |                                            -- coordinateCap
            (∀ f, f ∉ S.mutable → ‖p.val.1 f‖ = 1) ∧
              ∀ i : {i : Fin d // i ∈ S.mutable},
                ‖p.val.1 i.val‖ ≤ 1 ∧ ((1 - ‖p.val.1 i.val‖ ^ 2 : ℝ) : ℂ) * p.val.2 i = 0}
```

The two remaining binders are structures, not definitions; their complete field
lists (also from `#print`) are:

```lean
structure ClusterSkeleton.SmoothPresentation {d : ℕ} (S : Seed d) : Type
  charts              : ChartedSpace (EuclideanSpace ℝ (Fin (2 * d))) S.Point
  smooth              : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*d)))) ∞ S.Point
  inclusion_smooth    : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*d)))
                          𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ)) ∞ (fun p => ↑p)
  inclusion_immersion : ∀ (p : S.Point), Function.Injective ⇑(mfderiv … (fun q => ↑q) p)

structure ClusterSkeleton.LiouvilleData {d : ℕ} {S : Seed d} (P : SmoothPresentation S) : Type
  primitive        : P.manifold.Form 1
  smooth_primitive : P.manifold.IsSmoothForm primitive
  symplectic       : P.manifold.IsSymplecticOn (P.manifold.exteriorDerivative primitive) Set.univ
  field            : (p : S.Point) → P.manifold.Tangent p
  smooth_field     : P.manifold.IsSmoothVectorField field
  contraction      : ∀ p v, evalTwo (P.manifold.exteriorDerivative primitive) p (field p) v
                              = evalOne primitive p v
  completeFlow     : FsFltz.Geometry.CompleteLiouvilleFlow P.manifold field

structure FsFltz.Geometry.CompleteLiouvilleFlow {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) : Type
  flow          : Flow ℝ M.Point          -- toFun, cont', map_add', map_zero'
  smooth_action : ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
                    (fun p : ℝ × M.Point => flow.toFun p.1 p.2)
  solves        : ∀ x t a, flow.toFun t x ∈ (chartAt (Model d) a).source →
                    HasDerivAt (fun s => chartAt (Model d) a (flow.toFun s x))
                      (M.chartTangentMap a (flow.toFun t x) (Z (flow.toFun t x))) t
```

and the FsFltz notions used above are
`IsSymplecticOn M eta s = M.IsSmoothForm eta ∧ (∀ x ∈ s, M.exteriorDerivative eta x = 0) ∧ ∀ x ∈ s, M.Nondegenerate eta x`,
`Nondegenerate M eta x = ∀ v, (∀ w, evalTwo eta x v w = 0) → v = 0`,
`evalOne α x v = α x (fun _ => v)`, `evalTwo eta x v w = eta x ![v, w]`,
`Model d = EuclideanSpace ℝ (Fin d)`.

**Verdict PASS.** The unfolded type contains exactly the PDF's data (`2n`-dimensional
smooth structure, smooth immersive coordinate inclusion, dense torus, smooth
one-form, smooth field, jointly smooth all-real-time flow with the chart ODE,
`ι_Z dλ = λ`, nondegeneracy of `dλ` on `Set.univ`, the torus value `Im Ω_T`, and
`Skel(Φ) = C_E`) and nothing else.

---

## 2. Input — PASS

### Lean (`ClusterSkeleton/Seed.lean:31-43`, `:53`, `:69`, `:199-220`, `:267`)

```lean
structure Seed (d : ℕ) where
  E : Matrix (Fin d) (Fin d) ℤ
  mutable : Finset (Fin d)
  D : Fin d → ℚ
  D_pos : ∀ i, 0 < D i
  skewSymmetrizable : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < E i j)

def Unimodular : Prop := S.E.det = 1
def K : Matrix (Fin d) (Fin d) ℚ := fun i j => (S.E i j : ℚ) * S.D j
abbrev B : Matrix (Fin d) (Fin d) ℤ := S.Bexp            -- `S.Bexp = S.Eᵀ`, so `S.B i j = S.E j i`
def Independent (I : Finset (Fin d)) : Prop :=
  I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.E i j = 0
```

### PDF (`target-theorem.tex`, §1)

```
 E∈GL_n(Z),  D̃=diag(d_1,…,d_n), d_j∈Q_{>0},  K=E D̃,  K^T=-K.
 Thus E_ij d_j = -E_ji d_i, rather than E_ij = -E_ji.
 Require the mutable block B=E_{M,M} to be acyclic: the arrows i→j with
 B_ij>0 have no directed cycle.
 … In fact det E=1 …
```
and `blueprint`: *"A subset I⊂M is independent if B_ij=0 for all i,j∈I."*

### Judgement

* `E` integral, unrestricted: field `E : Matrix … ℤ` with **no** skewness field.
  The structure's only matrix hypothesis is `skewSymmetrizable`, which is
  literally the PDF's `E_ij d_j = -E_ji d_i`, i.e. `Kᵀ = -K` (`Seed.K_transpose`).
* `D` arbitrary positive rational: `D : Fin d → ℚ` + `D_pos`. No field, instance
  or default forces `D i = 1` or `D i = D j`.
* Mutable set: a free `Finset (Fin d)`; no principal-coefficient or frozen-value
  restriction.
* Acyclicity: `WellFounded (0 < E i j)` on the mutable subtype, which
  `Seed.wellFounded_iff_no_directed_cycle` shows is exactly "no directed cycle",
  on the mutable block only, in the PDF's arrow orientation.
* **`Unimodular` is the PDF hypothesis, not a strengthening.** The PDF assumes
  `E∈GL_n(Z)` (`det E = ±1`) and then *derives* `det E = 1` from
  `det K = det E · ∏ d_i > 0`; Lean's `det E = 1` is therefore equivalent to the
  PDF's hypothesis under the other fields. (`Seed.det_K`, `Seed.det_K_of_unimodular`
  are the same computation.) For odd `d` no `Seed` satisfies `Unimodular` at all —
  a skew `K` of odd size is singular — so the Lean statement is vacuously true
  there and is in no way weaker.
* Quantification: `FirstGeometricTarget = ∀ (d : ℕ) (S : Seed d), S.Unimodular → …`.
  `S.Unimodular` is the **only** hypothesis, and the fully unfolded type of item 1
  exhibits it as the sole non-structural premise.

### No hidden skewness / `D = 1` / equal weights — definite answer

* `grep -rn "skew" ClusterSkeleton*.lean`: outside `ClusterSkeleton/SkewSeed.lean`
  and `ClusterSkeleton/Examples/A2.lean` every hit is either a comment or a fact
  about **`K`** (`Seed.K_skew`, `Seed.K_transpose`, `SeedAlgebra.K_transpose_real`,
  `NodeTwoForm.matrixValue_skew`, `NodeNondegeneracy.complexResidual_skew`,
  `normalMatrix_skew`). `S.skewSymmetrizable` is the structure field. There is no
  hypothesis `E i j = -E j i` anywhere in the target's dependency closure.
* The import closure of `ClusterSkeleton.FullSkeleton` is 58 modules and contains
  **neither `ClusterSkeleton.SkewSeed` nor `ClusterSkeleton.Examples.*`**, so the
  old skew structure cannot reach the final theorem even indirectly.
* `grep` for `D = 1`, `D i = 1`, `fun _ => 1`: the only hits in
  `ClusterSkeleton/**` outside `SkewSeed.lean`/`Examples/` are docstrings
  ("With `D = 1` it degenerates to …") and `Seed.unitPoint` (`a = 1`), which is a
  *point*, not a weight.
* `grep` for `det = 1`: the only uses are `Seed.Unimodular` itself,
  `Seed.B_det` (`det Eᵀ = det E = 1`, integral matrix) and
  `SeedAlgebra.det_Breal/det_Bcomplex` (same statement over `ℝ`/`ℂ`). The
  dynamics no longer uses `det B = 1` as a cancellation: the baseline
  `full_matrix_inverse_bound` calc block is replaced by
  `SeedAlgebra.exists_inverse_bound_Kreal`, and `LocalAngularDynamics.nu` and
  `AllStrataGrowth.full_matrix_nu_equation` use only
  `SeedAlgebra.isUnit_det_Kreal` (`det K = ∏ d_i ≠ 0`). Verified by reading
  `TorusLiouvilleDynamics.lean:771`, `LocalAngularDynamics.lean:110-116`,
  `AllStrataGrowth.lean:114-126`.
* `Examples/NonSkew.lean` constructs exactly the PDF §4 input
  (`E = !![0,1,-1,0; -2,0,0,-1; 1,0,0,0; 0,1,0,0]`, `D = ![1,2,1,2]`,
  `M = {0,1}`) with `nonSkewSeed_unimodular`, `nonSkewSeed_not_skew`
  (`E 0 1 = 1 ≠ -2 = -(E 1 0)`) and `nonSkewSeed_weights_ne`, and the final
  theorem applies to it on one line (Appendix A):
  `FullSkeleton.firstGeometricTarget 4 Examples.nonSkewSeed Examples.nonSkewSeed_unimodular
   : LiouvilleSkeletonTarget Examples.nonSkewSeed`. (That consumer line is not
  *in* the tree at `114d639` — see item 6 / R4 — but it elaborates.)

**Verdict PASS.** No instance argument, no auxiliary structure field and no
definition body in the target's closure smuggles in `E` skew, `D = 1` or equal
weights.

---

## 3. Space — PASS

### Lean (`Seed.lean:199-220`)

```lean
def positiveMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ := ∏ j, a j ^ (S.E j i).toNat
def negativeMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ := ∏ j, a j ^ (-S.E j i).toNat

abbrev Point :=
  {x : (Fin d → ℂ) × (S.Mutable → ℂ) //
    (∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
    (∀ f, f ∉ S.mutable → x.1 f ≠ 0)}
```

### PDF (`target-theorem.tex`, §1)

```
 P_i^±(z)=∏_{j=1}^n z_j^{[±E_{ji}]_+}.
 X_E = { (z,z')∈C^n×C^M :  z_i z_i' = P_i^+(z)+P_i^-(z)  (i∈M),
                            z_f ≠ 0                       (f∈F) }.
 Give X_E the induced topology. … The initial torus is T={z_1⋯z_n≠0}⊂X_E.
```

### Judgement

* **Column exponents, literally.** `(S.E j i).toNat = [E_{ji}]_+` and
  `(-S.E j i).toNat = [-E_{ji}]_+`; the Lean index order is `E j i`, the PDF's
  `E_{ji}`. `S.B i j = S.E j i` is only a name (`Seed.B_apply : S.B i j = S.E j i`
  is `rfl`) and carries no skewness. The integer exponents come from `E`, never
  from the rational `K`, in agreement with the PDF's explicit warning.
* **Ambient space and topology.** The carrier is the subtype of
  `(Fin d → ℂ) × (S.Mutable → ℂ)` with the inherited subtype topology; nothing is
  transported to another point type. `SmoothPresentation.inclusion_smooth` /
  `inclusion_immersion` are stated for `fun p : S.Point => p.val` into that very
  ambient space.
* **Frozen coordinates** are free nonzero variables (`∀ f ∉ S.mutable, x.1 f ≠ 0`),
  never fixed to 1; the cap condition `‖p.a f‖ = 1` is a *conclusion*, not a
  hypothesis.
* **Not a dummy carrier.** `Seed.unitPoint` (`a ≡ 1`, `b ≡ 2`) is a point of every
  seed variety, and `initialTorus_nonempty`, `coordinateCap_nonempty` witness both
  distinguished sets. `initialTorus S = {p | ∀ j, p.a j ≠ 0}`
  (`CoordinateLoci.lean:56`) is the PDF's `T`.
* **The smooth structure is constructed, not assumed.**
  `SmoothAtlas.presentation S hdet : SmoothPresentation S` (`SmoothAtlas.lean:222`)
  is built from `SmoothAtlas.chart`, which is built from
  `IndependentNodeChart.homeomorph` (`IndependentNodeChart.lean:315`) together with
  `IndependentNodeSmooth`'s `contDiffOn_transition`, `inclusion_smooth`,
  `inclusion_immersion`. The presentation is an existential *witness* in the
  target, never a hypothesis.
* **Chart rank.** `IndependentNodeChart.vector_finrank_real : Module.finrank ℝ (Vector S I) = 2*d`
  gives the PDF's dimension `2n`; the model type of the manifold is
  `Model (2*d) = EuclideanSpace ℝ (Fin (2*d))`.

**Verdict PASS.** (Stage A reached the same conclusion for items 1–2 of its own
numbering; nothing changed in `Seed.lean` between stage A and `114d639` beyond
what stage A reviewed.)

---

## 4. Logarithmic form — PASS

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

### PDF (`target-theorem.tex`, §1 and `thm:target`(2))

```
 Ω_T = ½ Σ_{j,l} K_{jl} dlog z_j ∧ dlog z_l ,     K = E D̃
 (2) ω = dλ is nondegenerate and ω|_T = Im Ω_T .
```

### Judgement

* **Coefficient.** `S.K i j = (S.E i j : ℚ) * S.D j` is `K_{ij} = E_{ij} d_j`, i.e.
  `K = E D̃` with the PDF's index order. Not `E`, not `B = Eᵀ`, not `-K`.
* **Factor and antisymmetrization.** `(1/2) * Σ_{i,j} K_{ij} (L_i(v)L_j(w) − L_i(w)L_j(v))`
  with `L_j = dlog z_j`; `dlog z_i ∧ dlog z_j` evaluated on `(v,w)` is exactly
  `L_i(v)L_j(w) − L_i(w)L_j(v)`. So the Lean value is `Im Ω_T(v,w)` on the nose —
  the PDF's form, **not** its negative, confirming the stage-A finding (item 3 of
  `docs/reviews/stage-a-semantic-audit.md`, which is about this same definition
  with `S.B` replaced by `S.K`).
* **Real logarithmic shape.** Because `Kᵀ = -K`, this equals the blueprint's
  `Im Ω = Σ_{j,l} K_{jl} du_j ∧ dθ_l`. This is not asserted here, it is *proved*
  in the tree and re-checked by elaboration (Appendix A, check A.5):
  ```
  logarithmicImaginaryValue p v w
    = (Σ_i Σ_j K_ij · Re(L_i v) · Im(L_j w)) − (Σ_i Σ_j K_ij · Re(L_i w) · Im(L_j v))
  ```
  (`GlobalTwoForm.omega_torus` composed with `TorusLiouvilleDynamics.omega_real`).
  Hand check: `Im(½ Σ K_ij (v_i w_j − w_i v_j)) = Σ K_ij (Re v_i Im w_j + Im v_i Re w_j)`
  by skewness of the real matrix `K`, and the second summand equals
  `−Σ K_ij Re w_i Im v_j` after swapping indices and using `K_ji = −K_ij`.
* **It is the imaginary part that is claimed symplectic, on the whole space.**
  The field `LiouvilleData.symplectic : IsSymplecticOn (exteriorDerivative primitive) Set.univ`
  asks for smoothness, closedness and **nondegeneracy at every point of `S.Point`**,
  not only on the torus. The torus clause of the target then pins that global
  2-form to `Im Ω_T` on `T`, which is dense (`dense_initialTorus`); this is exactly
  the PDF's "`ω = dλ` nondegenerate and `ω|_T = Im Ω_T`" and the blueprint's
  statement that the extension/nondegeneracy of `Ω` are *construction obligations*.
  Discharged by `GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha`
  (`GlobalPrimitive.lean:143`), via `GlobalSymplectic.isSymplecticOn_omega`.

**Verdict PASS.**

---

## 5. Flow — PASS

### The primitive

`TorusPrimitive.beta` (`TorusPrimitive.lean:29`):
```lean
def beta : … .Form 1 :=
  covectorForm _ (fun p => ∑ i : Fin d, ∑ j : Fin d,
    ((S.K i j : ℝ) * Real.log ‖p.a i‖) • angleCovector S hdet j p)
```
i.e. `β = Σ_{i,j} K_{ij} u_i dθ_j = uᵀ K dθ = λ_tor`. **No `1/2`, no minus, no
inverse** (`evalOne_beta`, and the module's own docstring says so).

`TorusPrimitive.alpha H = beta + d H` (`TorusPrimitive.lean:53`, option **O1**),
`TorusCorrection.alpha = TorusPrimitive.alpha (TorusCorrection.H)`
(`TorusCorrection.lean:171`), and

`TorusCorrection.H` (`TorusCorrection.lean:83`):
```lean
def H (ε κ δ : ℝ) (p : S.Point) : ℝ :=
  ∑ i ∈ S.mutable, (S.D i : ℝ) * (PrimitiveCutoffs.radial ε κ (A S p i) *
    DominanceCutoff.dominance S ε i (A S p) * PrimitiveCutoffs.rho (rowLog S p i) *
      angular S δ p i)
```

PDF (`target-theorem.tex` §4, `proof-blueprint.tex` proof of `thm:acyclic-skeleton`):
```
 λ_tor = uᵀ K dθ ,   H = Σ_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i) ,   λ_ac = λ_tor + dH .
```
Dictionary, each half checked: `A S p i = log‖z_i‖ = u_i`;
`PrimitiveCutoffs.radial = h`; `DominanceCutoff.dominance = χ_i`;
`rowLog S p i = Σ_j B_{ij} u_j = Σ_j E_{ji} u_j = c_i(u) = v_i`
(elaboration check A.8, `rfl`); `angular S δ p i = ϑ_δ(arg(−t_i)) = β(η_i)`
because `arg(−t_i) = η_i − π` and `ϑ_δ` is supported near `0` with `ϑ_δ(s)=s`
near `0`, i.e. `β(η) = ϑ_δ(η−π)`; `exchangeCharacter p i = ∏_j z_j^{E_{ji}} = z^{c_i} = t_i`
(`exchangeCharacter_eq_zpow_product`). So **every summand carries the weight `d_i`
exactly as in the PDF**, and the exponent row inside `ρ` stays integral.

### The vector field and the flow

`GlobalLiouvilleField.Z S hdet ε κ hδ p = (…).manifold.liouvilleVector (GlobalPrimitive.alpha …) p`
(`GlobalLiouvilleField.lean:18`); `contraction_exteriorDerivative`
(`:31`) proves `evalTwo (d α) p (Z p) v = evalOne α p v`, i.e. `ι_Z dλ_ac = λ_ac`,
the blueprint's stated convention. Completeness:
`NativeCompleteFlow.exists_completeLiouvilleFlow` (`NativeCompleteFlow.lean:104`)
is a **theorem**, proved from `FiniteTimeConfinement`; `completeFlow` (`:129`) is
`Classical.choice` of it. So the flow is constructed and the only reason
`Classical.choice` appears in the axiom list is this choice of a witness for a
proved existential — not an opaque constant, not an axiom, not a hypothesis.

### Hand derivation versus the blueprint

Write `L_j = dlog z_j (Z)`, so `Re L_j = u̇_j`, `Im L_j = θ̇_j`. With
`Im Ω = Σ_{j,l} K_{jl} du_j ∧ dθ_l` (item 4) and
`λ_ac(∂_{u_i}) = ∂_{u_i}H`, `λ_ac(∂_{θ_l}) = Σ_i K_{il} u_i + ∂_{θ_l}H`:

* **Radial tangent.** `Im Ω(Z, ∂_{u_i}) = −Σ_l K_{il} θ̇_l`, hence
  `Σ_l K_{il} θ̇_l = −∂_{u_i}H`. Lean, verbatim:
  ```lean
  theorem TorusLiouvilleDynamics.angular_equation … (i : Fin d) :
      ∑ j, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im =
        -differentialCovector … (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i)
  ```
  The **minus is correct and is forced by O1**; it is not a free choice.
* **Where `d_i` enters.** `K_{ij} = −d_i B_{ij}` (`Seed.K_eq_neg_D_mul_B`,
  `Seed.lean:158`; `SeedAlgebra.sum_K_row`), and `Σ_j B_{ij} θ̇_j = Σ_j E_{ji} θ̇_j = c_i(θ̇) = η̇_i`.
  Substituting:
  ```lean
  theorem TorusLiouvilleDynamics.angular_equation_row … :
      (S.D i : ℝ) * ∑ j, (S.B i j : ℝ) * (logarithmicComponents … p j).im =
        differentialCovector … (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i)
  ```
  i.e. `d_i η̇_i = ∂_{u_i}H`, which is **blueprint eq. `acyclic-angle-flow`**
  `η̇_i = (1/d_i) ∂_{u_i} H`. Equivalently `c_i(K^{-1}x) = −x_i/d_i`
  (`SeedAlgebra.c_inv_K`), the PDF's displayed identity.
* **Angular tangent.** `Im Ω(Z, ∂_{θ_j}) = Σ_i K_{ij} u̇_i`, and
  `∂_θ H = K Σ_i h χ ρ β' e_i` (blueprint), i.e.
  `∂_{θ_j}H = Σ_i K_{ij} r_i` with `r_i = h(u_i)χ_iρ(v_i)β'(η_i)`. Lean proves
  exactly this with the sign the O1 convention produces:
  ```lean
  theorem TorusLiouvilleDynamics.differential_H_angular_K … (j : Fin d) :
      differentialCovector … (TorusCorrection.H S ε κ δ) p (angularTangent S hdet p hp j) =
        -∑ i ∈ S.mutable, amplitude S ε κ i (A S p) *
          deriv (PrimitiveCutoffs.vartheta δ) ((-exchangeCharacter p i).arg) * (S.K i j : ℝ)
  ```
  **Here the `d_i` of each `H` summand cancels**: `differential_H_angular`
  carries `(S.D i : ℝ) * (… * (S.B i j : ℝ))`, and `d_i B_{ij} = −K_{ij}` turns it
  into `−K_{ij}`, which is why the next statement keeps the baseline shape:
  ```lean
  theorem TorusLiouvilleDynamics.radial_matrix_equation … (j : Fin d) :
      ∑ i, (S.K i j : ℝ) * (logarithmicComponents … p i).re =
        (∑ i, (S.K i j : ℝ) * TorusCorrection.A S p i) -
        ∑ i ∈ S.mutable, amplitude S ε κ i (A S p) *
          deriv (PrimitiveCutoffs.vartheta δ) ((-exchangeCharacter p i).arg) * (S.K i j : ℝ)
  ```
  This is `Kᵀ u̇ = Kᵀ u − Kᵀ r`, and injectivity of `K` over `ℝ`
  (`SeedAlgebra.Kreal_vecMul_injective`, from `isUnit_det_Kreal`, i.e.
  `det K = ∏ d_i ≠ 0` — **not** `det = 1`) gives `u̇ = u − r`:
  ```lean
  theorem TorusLiouvilleDynamics.mutable_radial_equation … (i ∈ S.mutable) :
      (logarithmicComponents … p i).re = TorusCorrection.A S p i -
        PrimitiveCutoffs.radial ε κ (A S p i) * DominanceCutoff.dominance S ε i (A S p) *
          PrimitiveCutoffs.rho (TorusCorrection.rowLog S p i) *
          deriv (PrimitiveCutoffs.vartheta δ) ((-exchangeCharacter p i).arg)

  theorem TorusLiouvilleDynamics.frozen_radial_equation … (i ∉ S.mutable) :
      (logarithmicComponents … p i).re = TorusCorrection.A S p i
  ```
  i.e. `u̇_i = u_i − h(u_i)χ_iρ(v_i)β'(η_i)` for `i∈M` and `u̇_j = u_j` for `j∈F`:
  **blueprint eq. `acyclic-flow` verbatim, weight-free**, because the `d_i`
  cancelled against `K_{ij} = −d_i B_{ij}`, not because `d_i = 1`. The globalized
  copies are `GlobalLiouvilleField.mutable_radial_equation` (`:108`) and
  `frozen_radial_equation_torus` (`:120`), both with the same shape.
* **Near a node.** Blueprint eq. `acyclic-H-near` gives `∂_{u_i}H = d_i(η_i−π)`;
  Lean:
  ```lean
  theorem BoundaryTangency.local_H_radial … :
      differentialCovector … (TorusCorrection.H S ε κ δ) q (radialTangent S hdet q ht i) =
        (S.D (i : Fin d) : ℝ) * (PrimitiveLocalization.nodeLog q i).im
  ```
  with `nodeLog q i = Log(−t_i) = v_i + i(η_i−π)`, so the right side is
  `d_i(η_i−π)`. **Exact match, with the weight explicit.**
* **The second cancellation.** The consumer keeps the baseline shape:
  ```lean
  theorem BoundaryTangency.nodeLog_drift_torus … :
      drift S hdet ε κ hδ (fun r => PrimitiveLocalization.nodeLog r i) q =
        PrimitiveLocalization.nodeLog q i
  ```
  i.e. `d/dτ Log(−t_i) = Log(−t_i)`, equivalently `v̇_i = v_i` and `η̇_i = η_i − π`
  — blueprint eq. `acyclic-divisor-flow` `ṫ_i = t_i Log(−t_i)`. The imaginary half
  is `d_i η̇_i = ∂_{u_i}H = d_i(η_i−π)`, i.e. `angular_equation_row` divided by
  `local_H_radial`: **the `d_i` of the angular equation cancels the `d_i` of
  `∂_{u_i}H`**, which is exactly why the divisor rate `−2a` and the partner rate
  `2(1+a)` (`eq:acyclic-partner-flow`) stay weight-free and their modules
  (`ZeroStratumInvariance`, `NormalizedPartnerNormDrift`,
  `ZeroStratumPartnerDynamics`, `ZeroStratumEscape`) are byte-identical to
  `e62c101` (item 7).
* **The `K`-route off the torus.** Blueprint: `θ̇ = −K^{-1} ∂_u H`. Lean:
  ```lean
  def LocalAngularDynamics.nu (ε κ δ : ℝ) (p q : S.Point) : Fin d → ℝ :=
    Matrix.mulVec (SeedAlgebra.Kreal S)⁻¹ (fun i => -angularRhs S ε κ δ p q i)
  ```
  with `angularRhs … j = Σ_{i∈M} d_i · (masked ∂_{u_j} of the i-th summand)`, i.e.
  the masked `∂_{u_j}H` **with the weights in it** — the same object as
  `differential_H_radial`, which also carries `(S.D i : ℝ)`. The minus is the one
  of `angular_equation`. `nu_eq_torus` proves `nu = Im L` on the torus, and
  `AllStrataGrowth.full_matrix_nu_equation` / `row_nu_equation`
  ```lean
  (∑ k, (S.K j k : ℝ) * nu … k) = -angularRhs … j
  (S.D j : ℝ) * (∑ k, (S.B j k : ℝ) * nu … k) = angularRhs … j
  ```
  reproduce the two forms off the torus, so `InteriorPartnerPropagation`'s and
  `CapAngularTangency`'s consumer statements keep their baseline shapes — again by
  cancellation of `d_j`, not by assuming it is `1`. The matrix inversion uses only
  `SeedAlgebra.isUnit_det_Kreal`/`Kreal_mul_inv`/`Kreal_inv_mul`, and the growth
  bound uses `SeedAlgebra.exists_inverse_bound_Kreal`, which replaces the
  baseline's `det B = 1` one-norm block (`TorusLiouvilleDynamics.lean:771`).

**Verdict PASS.** The primitive is the PDF's `λ_ac = λ_tor + dH` with the weighted
`H`; the field is the Liouville field of that primitive in the blueprint's own
sign convention `ι_Z dλ = λ`; the flow is complete, jointly smooth, two-sided and
**constructed** (existence proved, then chosen); and every radial/angular equation
of stage C agrees with `eq:acyclic-flow`, `eq:acyclic-angle-flow`,
`eq:acyclic-H-near` and `eq:acyclic-divisor-flow`, with the three cancellation
points identified above.

---

## 6. Conclusions — RISK R4

PDF `thm:target` clause by clause.

| PDF clause | Lean declaration | inside `LiouvilleSkeletonTarget`? |
| --- | --- | --- |
| smooth real manifold structure of dimension `2n` | `SmoothPresentation.charts`/`.smooth`, model `Model (2*d)`; witness `SmoothAtlas.presentation`; `IndependentNodeChart.vector_finrank_real` | **inside** (`∃ P`) |
| (1) coordinate inclusion into `C^n×C^M` is a smooth immersion | `SmoothPresentation.inclusion_smooth`, `.inclusion_immersion`; witnesses `SmoothAtlas.inclusion_smooth`, `SmoothAtlas.inclusion_immersion` | **inside** |
| (1) `T` is dense | first conjunct `Dense (initialTorus S)`; witness `ClusterSkeleton.dense_initialTorus` | **inside** |
| smooth real one-form `λ` | `LiouvilleData.primitive`, `.smooth_primitive`; witness `GlobalPrimitive.alpha`, `isSmoothForm_alpha` | **inside** |
| (2) `ω = dλ` nondegenerate (everywhere) | `LiouvilleData.symplectic : IsSymplecticOn (exteriorDerivative primitive) Set.univ`; witness `GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha` | **inside** |
| (2) `ω|_T = Im Ω_T` | the torus clause of the target; witness `FullSkeleton.torus_anchor` | **inside** |
| smooth vector field `Z` | `LiouvilleData.field`, `.smooth_field`; witness `GlobalLiouvilleField.Z`, `isSmoothVectorField_Z` | **inside** |
| (3) `ι_Z ω = λ` | `LiouvilleData.contraction`; witness `GlobalLiouvilleField.contraction_exteriorDerivative` | **inside** |
| (3) `Φ_0(p)=p`, `Φ_{t+s}=Φ_t∘Φ_s`, jointly smooth, all real times | `CompleteLiouvilleFlow.flow : Flow ℝ S.Point` (`map_zero'`, `map_add'`, `cont'`) + `.smooth_action`; witness `NativeCompleteFlow.completeFlow` | **inside** |
| (3) `d/dt Φ_t(p) = Z(Φ_t(p))`, both directions | `CompleteLiouvilleFlow.solves` (chart form, `HasDerivAt`, all `t∈ℝ`) | **inside** |
| (4) `Skel(Φ) = C_E` | `trappedSet L.completeFlow.flow = coordinateCap S`; witness `FullSkeleton.trappedSet_eq_coordinateCap` | **inside** |
| (4) `C_E = ⋃_{I independent} Λ_I` | `ClusterSkeleton.coordinateCap_eq_iUnion_lambdaStratum` (`CapStrata.lean:55`), and for the flow `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` (`FullSkeleton.lean:36`) | **OUTSIDE — R4** |
| (4) each `Λ_I` is compact | `ClusterSkeleton.isCompact_lambdaStratum S I (hI : I ⊆ S.mutable)` (`CapStrata.lean:85`); also `isCompact_coordinateCap` | **OUTSIDE — R4** |
| `U_I ≅ N^I × (C*)^{n−2|I|}` | `IndependentNodeChart.homeomorph S I hdet hI : Locus S I ≃ₜ Model S I` with `Model = ({i // i∈I} → Node) × NonzeroTorus (Complement S I)`, `Node = {uv : ℂ×ℂ // uv.1*uv.2 ≠ 1}`, and `IndependentNodeChart.complementRank_eq_sub_two_mul_card : complementRank … = d − 2*I.card` | **OUTSIDE — R4** |
| `in particular 2|I| ≤ n` | `IndependentNodeChart.two_mul_card_le S I hdet hI : 2 * I.card ≤ d` | **OUTSIDE — R4** |
| `Skel(Φ)` defined by relative compactness of the forward orbit, closure in `X_E` | `trappedSet flow = {x | IsCompact (closure (flow.forwardOrbit x))}` (`TrappedSet.lean:20`), closure in the subtype topology of `S.Point` | definition, matches |
| `C_E`, `Λ_I`, independence defined without reference to any flow | `coordinateCap` (`CapSet.lean:25`), `lambdaStratum` (`CapStrata.lean:27`), `Seed.Independent` (`Seed.lean:267`) — all flow-free | matches |

**PDF clauses with no Lean counterpart: none.**

**Lean clauses weaker than the PDF:**

1. *(R4, scope only.)* The boxed identity of the PDF is a three-way equality
   `Skel(Φ) = C_E = ⋃_I Λ_I`; `LiouvilleSkeletonTarget` contains only the first
   equality. The remaining two statements are proved, for every weighted seed, in
   `CapStrata.lean` and `CapIndependence.lean`, but a reader of
   `FirstGeometricTarget` alone does not get them. This is the risk R4 recorded in
   `docs/reviews/stage-a-semantic-audit.md`; it is **unchanged, not worsened**, by
   stage C.
2. The node-chart clause is delivered as a **homeomorphism** (`≃ₜ`), not as an
   isomorphism of complex-analytic/algebraic varieties. The PDF's `N` is
   `{(x,y,t) : xy = 1+t, t≠0}`, Lean's `Node` is its image `{(x,y) : xy ≠ 1}`
   under `t = xy − 1` (a bijection), so the sets agree; the smooth structure is
   carried by `IndependentNodeSmooth`/`SmoothAtlas`, which is what the target uses.
   The PDF's own statement of this clause is set-theoretic/structural, so this is a
   presentational, not a mathematical, gap. Recorded as part of R4, not as a defect.

### What a consumer must cite to obtain the full PDF theorem

Elaborated in Appendix A (A.3, A.4):

```lean
-- clause 4 for the *same* flow produced by the target's existential:
obtain ⟨hdense, P, L, hanchor, hskel⟩ := FullSkeleton.firstGeometricTarget d S hdet
-- hskel                                     : trappedSet L.completeFlow.flow = coordinateCap S
-- hskel ▸ coordinateCap_eq_iUnion_lambdaStratum S
--                                           : trappedSet L.completeFlow.flow = ⋃ I, lambdaStratum S I
-- isCompact_lambdaStratum S I.val I.property.1       : IsCompact (lambdaStratum S I)
-- IndependentNodeChart.homeomorph S I hdet hI        : Locus S I ≃ₜ Model S I
-- IndependentNodeChart.complementRank_eq_sub_two_mul_card S I hdet hI
-- IndependentNodeChart.two_mul_card_le S I hdet hI   : 2 * I.card ≤ d
```

Note that `coordinateCap_eq_iUnion_lambdaStratum` is **flow-free**, so the
stratified form follows for *any* witness `L` the existential produces; the
consumer never has to reach inside the target to recover
`NativeCompleteFlow.completeFlow`. (`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`
is the convenient packaged form for the canonical witness, with
`FullSkeleton.liouvilleData_flow : (liouvilleData …).completeFlow.flow = (completeFlow …).flow`
being `rfl`.)

**Definite answers to the three hidden-premise questions**

* *Hidden hypothesis?* **No.** Item 2; the fully unfolded type of item 1 has
  `S.E.det = 1` as its only premise.
* *Assumed flow?* **No.** `LiouvilleData.completeFlow` is a field of an
  **existentially quantified** structure and is instantiated by
  `NativeCompleteFlow.completeFlow = Classical.choice (exists_completeLiouvilleFlow …)`,
  where `exists_completeLiouvilleFlow` is a theorem proved from
  `FiniteTimeConfinement.…` and the native uniqueness/smooth-dependence results.
* *Assumed skeleton equality?* **No.**
  `FullSkeleton.trappedSet_eq_coordinateCap` is
  `Set.Subset.antisymm (ConstructedFlowReverseInclusion.trappedSet_subset_coordinateCap …)
   (ConstructedFlowCapInclusion.subset_trappedSet …)`; both inclusions are theorems
  about the same constructed flow, and neither module is a hypothesis of anything
  upstream. `trappedSet` and `coordinateCap` are defined independently
  (`TrappedSet.lean` imports only Mathlib; `CapSet.lean` imports only `Seed`).
* *Wrong field direction?* **No.** See the hand derivation in item 5; the O1 minus
  sign in `angular_equation` is exactly what `ι_Z Im Ω = λ_tor + dH` forces, and
  the downstream forward-orbit statements (`nodeLog_drift_torus`,
  `eq:acyclic-partner-flow` rates, cap forward invariance) come out with the
  blueprint's signs.

---

## 7. Diff against the baseline — PASS

All comparisons by `git rev-parse <commit>:<path>` on the reproduced tree.

### Byte-identical to `e62c101` (blob OID shown)

| file | blob |
| --- | --- |
| `ClusterSkeleton/FullSkeleton.lean` | `80fac71b9933da192a03fca84f12b3610b3653a6` |
| `ClusterSkeleton/ConstructedFlowCapInclusion.lean` | `3dfb51d0510f377329b3196ccb24ed2824a17f1f` |
| `ClusterSkeleton/ConstructedFlowReverseInclusion.lean` | `828da3cca9d232682696dba160f7084d48c1bb81` |
| `ClusterSkeleton/NativeCompleteFlow.lean` | `69bd5d3fbf75d968468a1bb8acdea2ba87a4777b` |
| `ClusterSkeleton/CapForwardInvariance.lean` | `0873d1a53984b6194e3635d33ad43c02451990ea` |
| `ClusterSkeleton/FiniteTimeConfinement.lean` | `35592602d59fdf7c25d80edb5a7eba165e413487` |
| `ClusterSkeleton/ZeroStratumInvariance.lean` | `f7b452f8c849e49194cbca0c268ef27a952b3c0b` |
| `ClusterSkeleton/ZeroStratumPartnerDynamics.lean` | `7e6bb517685386497c84477392f3f18f3370a4a1` |
| `ClusterSkeleton/ZeroStratumEscape.lean` | `2de9fa8c2072cc5fa36ce3066f6d30e31d8178cd` |
| `ClusterSkeleton/NormalizedPartnerNormDrift.lean` | `999e2bcf4f0796cf99bd20d22546193bdf55bc28` |
| `ClusterSkeleton/ScalarOrbitDynamics.lean` | `192430d95e0aeda9ec13ce983691cf120ed78c42` |
| `ClusterSkeleton/CapSet.lean` | `588a1e3ae3b674c1ba2569f4a78b4046881eb6a4` |
| `ClusterSkeleton/CoordinateLoci.lean` | `5cf1c3a30f4f62119a03b648176f79e252dc92e9` |
| `ClusterSkeleton/TrappedSet.lean` | `cae9dd164f26260c0c4a9160e2aa53e5e0c812a5` |
| `ClusterSkeleton/SmoothAtlas.lean` | `8fc6bd0eddbde3b7422aa5dfa9f2d17818d5ea8b` |
| `ClusterSkeleton/IndependentNodeSmooth.lean` | `23ce0f8efbbb0cb1a4a5a771141571cb3b5a5962` |
| `ClusterSkeleton/GlobalSymplectic.lean` | `f03548de6ec89c9aeca115801d0b025e7df5427d` |
| `ClusterSkeleton/PrimitiveCutoffs.lean`, `LocalFormGluing.lean`, `NodeLogExtension.lean`, `NodePrimitiveCancellation.lean`, `LaurentCoordinates.lean`, `IndependentLaurentCoordinates.lean`, `IntegralBasisCompletion.lean`, `InitialTorusDensity.lean`, `FormExtensionUniqueness.lean`, `GeometryNativeBridge.lean`, `TorusChart.lean` | unchanged |
| `verification/AxiomAudit.lean`, `verification/FullSkeletonConsumer.lean`, `verification/accepted-library.json`, all other `verification/*`, `docs/tex/*`, `docs/roadmap.md`, `docs/skeleton-audit.md`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, both PDFs | unchanged |

This confirms the stage-C handoff's byte-identity list exactly, and in particular
that the **final theorem file itself was never edited** by stages A, B1, B2 or C.

### `GeometryTarget.lean` is NOT byte-identical

`e5bad190ebf34f0b49de1bb14ca8cf2da0756a03` → `25954770177d487a7c3960bbdf815fb3c3097ce7`.
The change is from **stage A** (de58cd2), not stage C, and is the single
target-level statement change in the whole generalization:

```diff
-/-- Evaluation of Im(1/2 Σ Bᵢⱼ dlog(aᵢ) ∧ dlog(aⱼ)).
+/-- Evaluation of `Im(1/2 Σ_{i,j} K_ij dlog(a_i) ∧ dlog(a_j))`, the imaginary part
+of the reference's weighted logarithmic form
+`Ω_T = ½ Σ_{j,l} K_jl dlog z_j ∧ dlog z_l`, whose coefficient is the skew
+rational matrix `K = E * D`, not the integral exchange matrix `E`.
 Only its restriction to `initialTorus` is used in the target. -/
 def logarithmicImaginaryValue {S : Seed d} (P : SmoothPresentation S)
     (p : S.Point) (v w : P.manifold.Tangent p) : ℝ :=
   ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
-    (S.B i j : ℂ) *
+    (S.K i j : ℂ) *
```

`SmoothPresentation`, `LiouvilleData`, `LiouvilleSkeletonTarget` and
`FirstGeometricTarget` are otherwise unchanged text.

### Other target-level definitions

`coordinateCap` (`CapSet.lean`), `initialTorus` (`CoordinateLoci.lean`),
`trappedSet` (`TrappedSet.lean`) are in byte-identical files. `lambdaStratum` is
in a changed file (`CapStrata.lean`), but the change is only the removal of the
`import ClusterSkeleton.CapAngularTangency` and the relocation of
`norm_eq_one_of_not_strict` into `CapIndependence.lean`; the `def lambdaStratum`
text is untouched (and `rfl`-checked in Appendix A, A.7). `CapIndependence.lean`
changed only in proofs (`S.skew` → `Seed.E_pos_of_neg`/`E_eq_zero_iff`,
`S.acyclic` → `S.acyclic_exponent`), plus the moved lemma.

### Does the weighted statement specialize at `D = 1` to the accepted baseline?

**Yes.** Baseline `Seed` at `e62c101` is
`⟨B : Matrix … ℤ, mutable, skew : B i j = -B j i, acyclic⟩` with
`Unimodular : B.det = 1`, `positiveMonomial = ∏_j a_j^{[B_{ij}]_+}` (**row**
exponents) and `Independent I ↔ ∀ i,j∈I, B i j = 0`.
`ClusterSkeleton/SkewSeed.lean` (new, stage A) reproduces that structure verbatim
as `SkewSeed` and maps it by `toSeed := ⟨E := B, D := 1, …⟩`. Under this
documented convention (`E := B`, not `E := Bᵀ`):

| baseline object | weighted object at `D = 1`, `E := B` | status |
| --- | --- | --- |
| `Unimodular : B.det = 1` | `Unimodular : E.det = 1` | `Iff.rfl` (`SkewSeed.toSeed_unimodular_iff`) |
| `Independent I` | `Independent I` | `Iff.rfl` (`SkewSeed.toSeed_independent_iff`) |
| form coefficient `B i j` | `K i j = E i j · 1 = B i j` | `SkewSeed.toSeed_K`, **no sign change** |
| `P_i^+`, `P_i^-` | interchanged (`toSeed_positiveMonomial`, `toSeed_negativeMonomial`) | sum unchanged, `toSeed_monomial_sum` |
| carrier `SkewSeed.Point` | `(toSeed).Point` | the **same subset** of the same ambient space, `SkewSeed.carrier_set_eq`; identity map is `SkewSeed.pointHomeomorph` |
| `coordinateCap`, `lambdaStratum`, `initialTorus`, `trappedSet` | identical definitions (matrix-free, only `p.a`, `p.b`, `S.mutable`) | unchanged |
| `LiouvilleSkeletonTarget`, `FirstGeometricTarget` | unchanged text except the coefficient | unchanged |

So the weighted target at `D = 1` is the accepted baseline target, with the
carrier identified by the proved homeomorphism and the symplectic form literally
equal (not negated) — which is why the forward-orbit skeleton identity transports
without a time reversal. `SkewSeed.lean`'s module docstring states and justifies
exactly this, including why the alternative `E := Bᵀ` would have been wrong.
The recovery **theorem** itself (`SkewSeed.skeleton_recovery`) is out of scope
here and is reviewed on the final-assembly commit.

**Verdict PASS.**

---

## 8. Audit inventory — PASS on axioms, DEFECT A1 on coverage

### Module inventory at `114d639`

`ClusterSkeleton/**/*.lean`: **62** files (plus the root `ClusterSkeleton.lean`,
63 in total). The import closure of the root is all 63, so the full-library build
is the full-library check. Baseline `e62c101` had 58; the **four new modules** are

```
ClusterSkeleton/SkewSeed.lean            (stage A)
ClusterSkeleton/SymmetrizerAlgebra.lean  (stage A/B1)
ClusterSkeleton/SeedAlgebra.lean         (stage C prerequisite, from ee47a57)
ClusterSkeleton/Examples/NonSkew.lean    (stage A)
```

plus the new non-Lean file `docs/weighted-stage-c-map.md`. The import closure of
`ClusterSkeleton.FullSkeleton` is 58 modules and excludes `SkewSeed`,
`Examples.A2`, `Examples.NonSkew` and `GeometryNativeBridge`.

### `#print axioms` — every proposed root

Run with `lake env lean` on the built tree at `114d639`. **All 56 report exactly
`[propext, Classical.choice, Quot.sound]`; zero non-conforming entries.**

Final theorem and target-level:
`FullSkeleton.firstGeometricTarget`, `.liouvilleSkeletonTarget`,
`.liouvilleSkeletonTarget_of_parameters`, `.trappedSet_eq_coordinateCap`,
`.trappedSet_eq_iUnion_lambdaStratum`, `.liouvilleData`, `.liouvilleData_flow`,
`.liouvilleData_trappedSet`, `.torus_anchor`.

Separate clauses of item 6:
`coordinateCap_eq_iUnion_lambdaStratum`, `isCompact_coordinateCap`,
`isCompact_lambdaStratum`, `isClosed_lambdaStratum`,
`lambdaStratum_subset_coordinateCap`, `dense_initialTorus`,
`initialTorus_nonempty`, `iUnion_independent_candidateChartLocus`,
`Seed.Point.exists_independent_nonvanishing_locus`,
`IndependentNodeChart.homeomorph`,
`IndependentNodeChart.complementRank_eq_sub_two_mul_card`,
`IndependentNodeChart.two_mul_card_le`,
`IndependentNodeChart.vector_finrank_real`.

Constructed witnesses and dynamics:
`NativeCompleteFlow.completeFlow`, `NativeCompleteFlow.exists_completeLiouvilleFlow`,
`SmoothAtlas.presentation`, `GlobalPrimitive.alpha`,
`GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha`,
`GlobalLiouvilleField.Z`, `GlobalLiouvilleField.contraction_exteriorDerivative`,
`GlobalLiouvilleField.mutable_radial_equation`,
`TorusLiouvilleDynamics.angular_equation`, `.angular_equation_row`,
`.radial_matrix_equation`, `.mutable_radial_equation`, `.frozen_radial_equation`,
`.omega_real`, `.full_matrix_inverse_bound`,
`BoundaryTangency.local_H_radial`, `BoundaryTangency.nodeLog_drift_torus`,
`LocalAngularDynamics.nu`, `AllStrataGrowth.row_nu_equation`.

`Seed` / `SeedAlgebra` / `SymmetrizerAlgebra` roots:
`Seed.K_eq_neg_D_mul_B`, `Seed.sum_K_row_eq`, `Seed.K_transpose`,
`Seed.det_K_of_unimodular`, `Seed.acyclic_exponent`,
`SeedAlgebra.Kreal`, `SeedAlgebra.K_eq_neg_D_mul_B`, `SeedAlgebra.sum_K_row`,
`SeedAlgebra.c_inv_K`, `SeedAlgebra.isUnit_det_Kreal`,
`SeedAlgebra.det_Kreal_of_unimodular`, `SeedAlgebra.exists_inverse_bound_Kreal`,
`SeedAlgebra.Kreal_vecMul_injective`,
`SymmetrizerAlgebra.K_transpose`, `SymmetrizerAlgebra.isUnit_det_K`.

### `sorry` / `axiom` / `opaque` / `native_decide` / `unsafe`

`grep -rn "sorry\|admit\b\|axiom \|opaque\|native_decide\|unsafe"` over
`ClusterSkeleton.lean`, `ClusterSkeleton/**`, `verification/**`:
**no hits in any Lean source of the library.** The only matches anywhere are
inside `verification/AxiomAudit.lean`'s own error messages
(`throwError "Forbidden axiom …"`) and in `verification/README.md` prose. The
full build produced no `declaration uses 'sorry'` warning.

### DEFECT A1 — the existing audit no longer covers four modules

* **Declaration / file:** the `modules` array of the `run_cmd` loop in
  `verification/AxiomAudit.lean` (byte-identical to `e62c101`).
* **Discrepancy:** it lists 58 module names, i.e. the `e62c101` inventory. The four
  modules new at `114d639` — `ClusterSkeleton.SkewSeed`,
  `ClusterSkeleton.SymmetrizerAlgebra`, `ClusterSkeleton.SeedAlgebra`,
  `ClusterSkeleton.Examples.NonSkew` — are therefore **not** audited. The loop only
  errors on a listed module with zero declarations, so the audit would still
  *pass* while silently under-covering 4 of 62 modules. Separately, the
  `#print axioms` block names
  `ClusterSkeleton.IndependentNodeChart.complementRank_eq_sub_two_mul_card`, which
  still resolves (the declaration moved file but kept its namespace), so that line
  is fine.
* **Minimal statement-level fix:** add the four module names to the `modules`
  array, and add the following `#print axioms` roots for the generalized theorem
  and the separate clauses of item 6:
  ```lean
  #print axioms ClusterSkeleton.isCompact_coordinateCap
  #print axioms ClusterSkeleton.isCompact_lambdaStratum
  #print axioms ClusterSkeleton.dense_initialTorus
  #print axioms ClusterSkeleton.IndependentNodeChart.homeomorph
  #print axioms ClusterSkeleton.IndependentNodeChart.two_mul_card_le
  #print axioms ClusterSkeleton.IndependentNodeChart.vector_finrank_real
  #print axioms ClusterSkeleton.Seed.K_transpose
  #print axioms ClusterSkeleton.Seed.det_K_of_unimodular
  #print axioms ClusterSkeleton.Seed.acyclic_exponent
  #print axioms ClusterSkeleton.SeedAlgebra.isUnit_det_Kreal
  #print axioms ClusterSkeleton.SeedAlgebra.exists_inverse_bound_Kreal
  #print axioms ClusterSkeleton.SeedAlgebra.c_inv_K
  #print axioms ClusterSkeleton.SymmetrizerAlgebra.K_transpose
  #print axioms ClusterSkeleton.SymmetrizerAlgebra.isUnit_det_K
  ```
  plus, once the recovery theorem and the non-skew consumer land,
  `SkewSeed.skeleton_recovery` and the `Examples.nonSkewSeed` consumer.
* **Final assembly affected?** **No.** `verification/` is explicitly out of final
  assembly's scope and belongs to the verification/receipts mission; this report
  does not modify it.

**Verdict for item 8: PASS on the axiom result, DEFECT A1 on coverage.**

### Carried-over documentation defects D1, D2

Both were reported by the stage-A semantic audit and both are **still present at
`114d639`** (they were fixed on `weighted/recovery-scaffold` @ `e7a6d96`, a branch
stage C did not build on):

* **D1** — `ClusterSkeleton.exchangeCharacter_eq_zpow_product`
  (`NodeCoordinates.lean:55-57`). The statement is
  `exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i)`, i.e. `z^{c_i} = t_i`, but the
  docstring says *"the reference's inverse character `1/t_i`"* — the opposite.
  *Minimal fix:* replace the docstring (text already written at `e7a6d96`).
  *Final assembly affected:* yes, bookkeeping only — the merge must keep
  `e7a6d96`'s version of `NodeCoordinates.lean`'s docstrings.
* **D2** — `ClusterSkeleton.Seed.Point.outgoing_ne_zero` (`ZeroSet.lean:22-25`).
  With column exponents, `0 < S.B i j` is an arrow `j → i`, so the name and the
  docstring's "outgoing" are stale. *Minimal fix:* the `e7a6d96` docstring. Same
  assembly note.

---

## 9. Replacement text for the weighted `statement-review.md`

See **Appendix B**. Note the path: at `e62c101` and at `114d639` the baseline
statement review lives at **`verification/statement-review.md`** (there is no
`docs/statement-review.md`); `docs/skeleton-audit.md` is the separate
skeleton audit. The replacement text below is written for
`verification/statement-review.md` and must be installed by the
verification/receipts mission, which owns `verification/`. This review does not
touch it.

---

## Appendix A — elaboration checks

Run at the repository root of this branch after
`horizon-lean-check ClusterSkeleton` (status `passed`, 3750 jobs, Lean 4.34.1 /
Lake 5.0.0), with `lake env lean Scratch.lean`; `Scratch.lean` was deleted before
committing and no tracked Lean file was modified. Every check below elaborated
with no errors.

```lean
-- A.1  the fully unfolded target of item 1 is the real target (kernel-checked)
example : FirstGeometricTarget = UnfoldedTarget := rfl

-- A.2  the final theorem has no binder at all
#check @ClusterSkeleton.FullSkeleton.firstGeometricTarget
--  FullSkeleton.firstGeometricTarget : FirstGeometricTarget

-- A.3  the PDF's non-skew §4 input is accepted, in one line
example : LiouvilleSkeletonTarget Examples.nonSkewSeed :=
  FullSkeleton.firstGeometricTarget 4 Examples.nonSkewSeed Examples.nonSkewSeed_unimodular

-- A.4  the full PDF clause 4 for the very flow the target produces
example {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    ∃ (P : SmoothPresentation S) (L : LiouvilleData P),
      trappedSet L.completeFlow.flow = coordinateCap S ∧
      trappedSet L.completeFlow.flow =
        ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val ∧ True := by
  obtain ⟨-, P, L, -, hskel⟩ := FullSkeleton.firstGeometricTarget d S hdet
  exact ⟨P, L, hskel, by rw [hskel, coordinateCap_eq_iUnion_lambdaStratum S], trivial⟩

example {d : ℕ} (S : Seed d) (I : {I : Finset (Fin d) // S.Independent I}) :
    IsCompact (lambdaStratum S I.val) := isCompact_lambdaStratum S I.val I.property.1

example {d : ℕ} (S : Seed d) (hdet : S.Unimodular) (I : Finset (Fin d)) (hI : S.Independent I) :
    Nonempty (IndependentNodeChart.Locus S I ≃ₜ IndependentNodeChart.Model S I) ∧
      SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card ∧
      2 * I.card ≤ d :=
  ⟨⟨IndependentNodeChart.homeomorph S I hdet hI⟩,
   IndependentNodeChart.complementRank_eq_sub_two_mul_card S I hdet hI,
   IndependentNodeChart.two_mul_card_le S I hdet hI⟩

-- A.5  the target's Im Ω_T clause is the blueprint's Σ K_jl du_j ∧ dθ_l
example {d : ℕ} (S : Seed d) (hdet : S.Unimodular) (p : S.Point) (hp : p ∈ initialTorus S)
    (v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p v w =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential i p v / p.a i).re *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p w / p.a j).im) -
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential i p w / p.a i).re *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im) :=
  (GlobalTwoForm.omega_torus S hdet p hp v w).symm.trans
    (TorusLiouvilleDynamics.omega_real S hdet p hp v w)

-- A.6  λ_ac = uᵀ K dθ + dH, no 1/2, no minus, no inverse
example … : evalOne (TorusCorrection.alpha S hdet ε κ δ) p v =
      (∑ i, ∑ j, (S.K i j : ℝ) * Real.log ‖p.a i‖ * (… p v / p.a j).im) +
      differentialCovector … (TorusCorrection.H S ε κ δ) p v :=
  TorusCorrection.evalOne_alpha S hdet ε κ δ p v

-- H = Σ_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)
example … : TorusCorrection.H S ε κ δ p = ∑ i ∈ S.mutable, (S.D i : ℝ) *
      (PrimitiveCutoffs.radial ε κ (Real.log ‖p.a i‖) *
       DominanceCutoff.dominance S ε i (fun j => Real.log ‖p.a j‖) *
       PrimitiveCutoffs.rho (∑ j, (S.B i j : ℝ) * Real.log ‖p.a j‖) *
       PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter p i))) :=
  TorusCorrection.manuscript_formula S ε κ δ p hp

-- A.7  the matrix-free target-level sets
example {d : ℕ} (S : Seed d) : coordinateCap S =
    {p : S.Point | (∀ f, f ∉ S.mutable → ‖p.a f‖ = 1) ∧
      ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧ ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0} := rfl
example {d : ℕ} (S : Seed d) (I : Finset (Fin d)) : lambdaStratum S I =
    {p : S.Point | (∀ i : S.Mutable, (i : Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧
      (∀ j : Fin d, j ∉ I → ‖p.a j‖ = 1)} := rfl

-- A.8  rowLog is the PDF's v_i = c_i(u) with c_i = E e_i
example {d : ℕ} (S : Seed d) (p : S.Point) (i : Fin d) :
    TorusCorrection.rowLog S p i = ∑ j : Fin d, (S.E j i : ℝ) * Real.log ‖p.a j‖ := rfl

-- A.9  D = 1 specialization data (item 7)
example {d : ℕ} (S : SkewSeed d) (i j : Fin d) : (S.toSeed).K i j = (S.B i j : ℚ) := by simp
example {d : ℕ} (S : SkewSeed d) : (S.toSeed).Unimodular ↔ S.Unimodular := Iff.rfl
example {d : ℕ} (S : SkewSeed d) (I : Finset (Fin d)) :
    (S.toSeed).Independent I ↔ S.Independent I := Iff.rfl

-- A.10  D1: the statement says t_i, the docstring says 1/t_i
example {d : ℕ} (S : Seed d) (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = ∏ j, p.a j ^ (S.E j i) := exchangeCharacter_eq_zpow_product p i
```

---

## Appendix B — replacement text for `verification/statement-review.md`

> Install verbatim (replacing the whole file) once the weighted library is
> integrated; the leading blockquote of the `D = I` version must go.

```markdown
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
- The `D = I` specialization returns the accepted baseline: `SkewSeed.toSeed`
  uses `E := B`, so `K = B` with no sign change, the two exchange monomials are
  interchanged with unchanged sum, and the carriers coincide
  (`SkewSeed.carrier_set_eq`, `SkewSeed.pointHomeomorph`).

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

The global flow is chosen after proving existence. It is not advertised as an
executable numerical flow algorithm.

The PDFs are mathematical expositions, not machine-checked documents. The
kernel-checked statements are the Lean declarations whose exact source and
dependency hashes are recorded by the verifier.
```
