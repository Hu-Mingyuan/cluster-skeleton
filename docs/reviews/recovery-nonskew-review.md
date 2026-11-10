# Recovery and non-skew statement review (acceptance checks 2 and 3, audit roots)

Independent **statement** review, not a build check, of what final assembly adds
on top of the reviewed stage-C tree. Objective
`7d3240fc-f412-49c4-88c8-a9d1a5a1bdaf` rev 2, roadmap source
`e62c10176919227d13a901b383cd2c2ef13e72f7` (`docs/roadmap.md`).
Mission `e755eaea-8fad-4a1d-aeee-56891825a70f` rev 1, assignment
`fa9c4c1e-2e9f-4e15-8698-0c0904a0f0b1`.

A Lean build checks elaboration, not meaning. Everything below was re-derived
from the sources at the reviewed commit; the handoff was used only to locate the
commit and was then verified independently.

## Reviewed commit and gate

* **Reviewed final-assembly commit F = `a575aa236b485672f0606bba6ebc80571671f8a9`**
  ("Add the delivered stage-B semantic audit"), tip of branch
  `weighted/final-assembly`, present in this checkout
  (`git cat-file -t` → `commit`).
* Final assembly's deliverable obligation `8df1e544-686a-45c4-87a2-50c9b41434ba`
  (assignment `3e612104-f8bd-418c-9647-1f22e0fd7415`) is `done` and its
  `resolution.note` begins `FINAL ASSEMBLY DELIVERED` — **not** `BLOCKED:` — and
  names F. F contains `ClusterSkeleton/SkewSeedSkeleton.lean`
  (`git ls-tree -r F`), so the gate is cleared and the review proceeds.
* Publication cross-check: F is verified-published as
  `refs/heads/horizon/recovery/c6b6325b-fc95-4900-824e-c079a22bba7e/a575aa236b485672f0606bba6ebc80571671f8a9`
  (publication `5577df58-5a2b-4b46-bb3d-3e7040947a36`, verified,
  2026-11-10T01:08:14Z). *Note:* the newest verified publication by timestamp
  (`43e6e111-…`, 2026-11-10T01:10:44Z) names `07132a64…`, which `git log`
  confirms is the **parent** of F, so no commit newer than F exists on the
  branch; F is the superset and is the commit reviewed here.
* Stage-C base **`114d63939d72cfb5c81d6bd22dd0811e053805a3`** and baseline
  **`e62c10176919227d13a901b383cd2c2ef13e72f7`** are both objects in this
  checkout, so no tree reproduction was required and no file was fetched through
  the repository API except the one noted below.
* The final statement review of the universal theorem **was available** and is
  used as an input: `docs/reviews/final-statement-review.md` at commit
  **`24b7bef8aaea7fd098e8ccd10474502d5a7320fa`** (publication
  `1040be6e-…`, verified 2026-11-10T01:09:40Z; blob
  `ec7f7b83bbd3944306d4d81524399060e5ef5967`, 1106 lines). That commit is not an
  object in this checkout, so the file was read through
  `GET /api/v3/repositories/5d09d029-…/file?commit_oid=24b7bef8…`. It is **not**
  reproduced here (it is not in this mission's output scope); its item 6
  (PDF-clause map) and item 8 (proposed root list) are quoted where used. The
  universal theorem itself is **not** re-reviewed here.

## Verdict summary

| # | Item | Verdict |
| --- | --- | --- |
| 1 | Exact recovery statements, fully unfolded | **PASS** |
| 2 | Is this the old `D = I` theorem? (acceptance check 2) | **PASS**, with the carried risk **R-N1** recorded below |
| 3 | Non-skew instance (acceptance check 3) | **PASS** |
| 4 | Consumers | **PASS** |
| 5 | Axiom audit | **PASS** on module coverage and axiom results; **RISK R-N2** on the `#print axioms` root list |
| 6 | Additivity versus the reviewed tree `114d639` | **PASS** — strictly additive |
| 7 | Replacement paragraphs for `verification/statement-review.md` | delivered (Appendix) |

**No URGENT-DEFECT.** There is no hidden hypothesis in the recovery theorem; the
non-skew instance does come from the universal theorem; every literal matches
the roadmap entry for entry; no axiom beyond `propext, Classical.choice,
Quot.sound` appears anywhere; and no statement, name or proof token changed
relative to `114d639`.

Two open items for the maintainer, neither blocking acceptance of checks 2 and 3:

* **R-N1** (item 2) — the smooth presentation and the Liouville datum, hence the
  primitive, the two-form, its nondegeneracy, the field and the complete flow,
  are asserted for `S.toSeed.Point`, not for the baseline subtype `S.Point`.
  This is the route that the stage-A audit item 4 (R1(2)) and the stage-B audit
  item 7 (R7) both prescribed, and `docs/weighted-recovery-plan.md` §2 records
  the decision and its reason. Closing statements and honest sizes: §2.6.
* **R-N2** (item 5) — the `#print axioms` root list does not yet contain the
  separate PDF clauses that the final statement review's DEFECT A1 proposes
  (`isCompact_lambdaStratum`, `isCompact_coordinateCap`,
  `IndependentNodeChart.homeomorph`, `two_mul_card_le`, `vector_finrank_real`,
  the `Seed`/`SeedAlgebra`/`SymmetrizerAlgebra` roots), nor the old-carrier
  compactness roots `SkewSeed.isCompact_coordinateCap` /
  `SkewSeed.isCompact_lambdaStratum`. Axiom *coverage* is unaffected (all 1811
  declarations of all 65 modules are audited); only the receipt's
  `audited_final_declarations` list is short. `verification/` belongs to the
  verification/receipts mission.

---

## 1. Exact recovery statements — PASS

All types below are as elaborated by `#check`/`#print` with `lake env lean` on F
(scratch file at the repo root, deleted before committing).

### 1.1 Clause (a) and the packaged theorem, as elaborated

```
@SkewSeed.liouvilleSkeletonTarget : ∀ {d : ℕ} (S : SkewSeed d),
  S.Unimodular → LiouvilleSkeletonTarget S.toSeed

@SkewSeed.skeleton_recovery : ∀ {d : ℕ} (S : SkewSeed d),
  S.Unimodular →
    Dense S.initialTorus ∧
      ∃ P L,
        (∀ p ∈ initialTorus S.toSeed,
            ∀ (v w : P.manifold.Tangent p),
              evalTwo (P.manifold.exteriorDerivative L.primitive) p v w =
                (1 / 2 *
                    ∑ i,
                      ∑ j,
                        ↑(S.B i j) *
                          ((P.coordinateDifferential i p) v / p.a i * ((P.coordinateDifferential j p) w / p.a j) -
                            (P.coordinateDifferential i p) w / p.a i *
                              ((P.coordinateDifferential j p) v / p.a j))).im) ∧
          trappedSet (S.conjFlow L.completeFlow.flow) = S.coordinateCap ∧
            trappedSet (S.conjFlow L.completeFlow.flow) = ⋃ I, S.lambdaStratum ↑I

@SkewSeed.skeleton_recovery_of_parameters : ∀ {d : ℕ} {ε κ δ : ℝ} (S : SkewSeed d),
  S.Unimodular → 0 < ε → 2 * ε + 1 ≤ κ → 0 < δ → (… the same conjunction …)
```

The binders of the existential are, from the source
(`ClusterSkeleton/SkewSeedSkeleton.lean:137`, `:170`):
`P : SmoothPresentation S.toSeed` and `L : LiouvilleData P`. The witnesses are
`SmoothAtlas.presentation S.toSeed (S.toSeed_unimodular hdet)` and
`FullSkeleton.liouvilleData S.toSeed (S.toSeed_unimodular hdet) hε hκ hδ`
(`:149-152`), with `skeleton_recovery` instantiating
`(ε := 1) (κ := 3) (δ := 1)` by `norm_num` (`:182-184`) — the baseline's own
cutoff triple.

The remaining declarations of the recovery — the first four in
`SkewSeedSkeleton.lean` (which has exactly seven declarations, matching the
audit's `AUDITED ClusterSkeleton.SkewSeedSkeleton: 7`), the last in
`SkewSeedRecovery.lean`:

```
@SkewSeed.dense_initialTorus : ∀ {d : ℕ} (S : SkewSeed d), S.Unimodular → Dense S.initialTorus

@SkewSeed.liouvilleData_torus_anchor_old_matrix : ∀ {d : ℕ} {ε κ δ : ℝ} (S : SkewSeed d)
  (hdet : S.Unimodular) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ),
  ∀ p ∈ initialTorus S.toSeed,
    ∀ (v w : (SmoothAtlas.presentation S.toSeed ⋯).manifold.Tangent p),
      evalTwo
          ((SmoothAtlas.presentation S.toSeed ⋯).manifold.exteriorDerivative
            (FullSkeleton.liouvilleData S.toSeed ⋯ hε hκ hδ).primitive) p v w =
        (1 / 2 * ∑ i, ∑ j, ↑(S.B i j) * (…)).im

@SkewSeed.liouvilleData_trappedSet_conjFlow : ∀ {d : ℕ} {ε κ δ : ℝ} (S : SkewSeed d)
  (hdet : S.Unimodular) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ),
  trappedSet (S.conjFlow (FullSkeleton.liouvilleData S.toSeed ⋯ hε hκ hδ).completeFlow.flow)
    = S.coordinateCap

@SkewSeed.liouvilleData_trappedSet_conjFlow_iUnion : (same hypotheses)
  trappedSet (S.conjFlow (FullSkeleton.liouvilleData S.toSeed ⋯ hε hκ hδ).completeFlow.flow)
    = ⋃ I, S.lambdaStratum ↑I

@SkewSeed.torus_anchor_old_matrix : ∀ {d : ℕ} (S : SkewSeed d) (P : SmoothPresentation S.toSeed)
  (p : S.toSeed.Point) (v w : P.manifold.Tangent p),
  P.logarithmicImaginaryValue p v w =
    (1 / 2 * ∑ i, ∑ j, ↑(S.B i j) * (…)).im
```

### 1.2 Every definition unfolded down to the weighted target and Mathlib

`ClusterSkeleton/SkewSeed.lean:44-48` — the old input structure, with no extra
field and no instance argument:

```lean
structure SkewSeed (d : ℕ) where
  B : Matrix (Fin d) (Fin d) ℤ
  mutable : Finset (Fin d)
  skew : ∀ i j, B i j = -B j i
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < B i j)
```

As printed: `def ClusterSkeleton.SkewSeed.Unimodular : {d : ℕ} → SkewSeed d → Prop := fun {d} S => S.B.det = 1`,
and the `example`s below all elaborate at F:

```lean
example (S : SkewSeed d) : S.Unimodular = (S.B.det = 1) := rfl
example (S : SkewSeed d) : (S.toSeed).Unimodular = (S.B.det = 1) := rfl
```

so the hypothesis is `det B = 1` on the nose, the baseline's
`Seed.Unimodular` (`e62c101:Seed.lean:35`).

```
def ClusterSkeleton.SkewSeed.toSeed : {d : ℕ} → SkewSeed d → Seed d :=
fun {d} S => { E := S.B, mutable := S.mutable, D := fun x => 1, D_pos := ⋯,
               skewSymmetrizable := ⋯, acyclic := ⋯ }
```

verified pointwise: `(S.toSeed).E = S.B := rfl`, `(S.toSeed).D i = 1 := rfl`,
`(S.toSeed).K i j = (S.B i j : ℚ)` (`toSeed_K`, `simp [Seed.K]`), hence
`(((S.toSeed).K i j : ℚ) : ℂ) = (S.B i j : ℂ)` (`toSeed_K_complex`).

`SkewSeed.Point` (`SkewSeed.lean:69-74`) is the baseline subtype verbatim, with
the baseline **row** exponents. The following `rfl` elaborates at F:

```lean
example (S : SkewSeed d) :
    S.Point =
      {x : (Fin d → ℂ) × (S.Mutable → ℂ) //
        (∀ i : S.Mutable,
          x.1 i * x.2 i = (∏ j, x.1 j ^ (S.B i j).toNat) + (∏ j, x.1 j ^ (-S.B i j).toNat)) ∧
        (∀ f, f ∉ S.mutable → x.1 f ≠ 0)} := rfl
```

`pointHomeomorph : S.Point ≃ₜ (S.toSeed).Point` (`SkewSeed.lean:166-180`) is the
identity on ambient coordinates — `toFun p := ⟨p.val, …⟩`, `invFun p := ⟨p.val, …⟩`,
both `left_inv`/`right_inv` `rfl`, continuity on both sides
`continuous_subtype_val.subtype_mk`. Confirmed:

```lean
example (S : SkewSeed d) (p : S.Point) : (pointHomeomorph S p).val = p.val := rfl
example (S : SkewSeed d) (p : S.Point) (j : Fin d) : (pointHomeomorph S p).a j = p.a j := rfl
example (S : SkewSeed d) (p : (S.toSeed).Point) : ((pointHomeomorph S).symm p).val = p.val := rfl
```

`conjFlow`, as printed, with no time reversal and no reparametrization:

```
def ClusterSkeleton.SkewSeed.conjFlow : {d : ℕ} → (S : SkewSeed d) → Flow ℝ S.toSeed.Point → Flow ℝ S.Point :=
fun {d} S Φ =>
  { toFun := fun t p => S.pointHomeomorph.symm (Φ.toFun t (S.pointHomeomorph p)), … }
```

and, since the homeomorphism is the identity on values,

```lean
example (S : SkewSeed d) (Φ : Flow ℝ ((S.toSeed).Point)) (t : ℝ) (p : S.Point) :
    (SkewSeed.conjFlow S Φ t p).val = (Φ t (SkewSeed.pointHomeomorph S p)).val := rfl
```

i.e. the conjugate flow at time `t` is literally the given flow at the **same**
`t`, read in the same ambient coordinates.

The three old loci, as printed, are the baseline definitions on the old carrier:

```
SkewSeed.initialTorus  = fun {d} S => {p | ∀ (j : Fin d), p.a j ≠ 0}
SkewSeed.coordinateCap = fun {d} S => {p | (∀ f ∉ S.mutable, ‖p.a f‖ = 1) ∧
                           ∀ (i : S.Mutable), ‖p.a ↑i‖ ≤ 1 ∧ ↑(1 - ‖p.a ↑i‖ ^ 2) * p.b i = 0}
SkewSeed.lambdaStratum = fun {d} S I => {p | (∀ (i : S.Mutable), ↑i ∈ I → ‖p.a ↑i‖ ≤ 1 ∧ p.b i = 0) ∧
                           ∀ j ∉ I, ‖p.a j‖ = 1}
```

compared character for character with `e62c101`'s `CoordinateLoci.lean:56-57`,
`CapSet.lean:25-28`, `CapStrata.lean:28-30`: **identical**, with `p.a`/`p.b` the
same two projections `p.1.1`, `p.1.2` (`SkewSeedRecovery.lean:70-79`;
`e62c101:Seed.lean:55-61`). `trappedSet` is unchanged from the baseline
(`TrappedSet.lean` is byte-identical to `e62c101`):

```
def ClusterSkeleton.trappedSet := fun {X} [TopologicalSpace X] flow => {x | IsCompact (closure (flow.forwardOrbit x))}
```

Finally, clause (a) delta-unfolds to the explicit weighted target — this
`example` elaborates at F, which is a machine check that no clause of
`LiouvilleSkeletonTarget` is hidden behind the abbreviation:

```lean
example (S : SkewSeed d) (h : S.Unimodular) :
    Dense (initialTorus S.toSeed) ∧
    ∃ (P : SmoothPresentation S.toSeed) (L : LiouvilleData P),
      (∀ (p : (S.toSeed).Point), p ∈ initialTorus S.toSeed → ∀ v w,
        evalTwo (P.manifold.exteriorDerivative L.primitive) p v w =
          P.logarithmicImaginaryValue p v w) ∧
      trappedSet L.completeFlow.flow = coordinateCap S.toSeed :=
  SkewSeed.liouvilleSkeletonTarget S h
```

### 1.3 The four required confirmations

1. **Universally quantified over `d` and `S : SkewSeed d`.** Yes:
   `∀ {d : ℕ} (S : SkewSeed d)` in every declaration; no `Fin d` restriction, no
   `d ≠ 0`, no instance argument, no `[Fact …]`.
2. **The only hypothesis is `S.Unimodular`.** Yes for
   `skeleton_recovery` and `liouvilleSkeletonTarget`. The elaborated type after
   the binders is `S.Unimodular → …` and nothing else.
   `skeleton_recovery_of_parameters` additionally takes the three *cutoff*
   hypotheses `0 < ε`, `2 * ε + 1 ≤ κ`, `0 < δ`; these are the weighted
   library's auxiliary construction parameters, they do not constrain the seed or
   any coordinate, and `skeleton_recovery` discharges them at `(1, 3, 1)` —
   exactly the baseline pattern (`e62c101:FullSkeleton.lean:90-93`).
3. **One existential `(P, L)` carries all clauses.** Yes: a single
   `∃ P L` whose body is the conjunction of the anchor clause and both skeleton
   identities, so the presentation, the Liouville datum and therefore the flow
   `L.completeFlow.flow` are the *same* in all three. The density clause sits
   outside the existential, which is the shape of `LiouvilleSkeletonTarget`
   itself.
4. **Nothing is assumed about a flow, completeness or either inclusion.** Yes.
   `L : LiouvilleData P` is existentially bound, and `completeFlow :
   CompleteLiouvilleFlow P.manifold L.field` is one of its **fields**, so the
   complete jointly smooth flow is constructed, not supplied. No hypothesis of
   the form `(Φ : Flow ℝ …)`, no `trappedSet … ⊆ …` or `… ⊆ trappedSet …`
   premise, and no cap-invariance premise occurs anywhere in the module. The two
   auxiliary lemmas that *do* take a flow —
   `SkewSeed.trappedSet_conjFlow_eq_coordinateCap (Φ) (h : trappedSet Φ = coordinateCap S.toSeed)`
   and `trappedSet_conjFlow (Φ)` — are transport lemmas, and in the recovery the
   hypothesis `h` is discharged by `FullSkeleton.liouvilleData_trappedSet`
   (`SkewSeedSkeleton.lean:115-117`), i.e. by a theorem, not an assumption.

**Verdict item 1: PASS.**

---

## 2. Is this the old theorem? — PASS, with carried risk R-N1

### 2.1 `SkewSeed` is the baseline `Seed` structure, textually

`e62c101:ClusterSkeleton/Seed.lean:21-25` versus `F:ClusterSkeleton/SkewSeed.lean:44-48`:
the four fields `B`, `mutable`, `skew`, `acyclic` are identical token for token,
including the docstring sentence "The arrow convention is `B i j > 0` for an
arrow from `i` to `j`". `Unimodular`, `Mutable`, `positiveMonomial`,
`negativeMonomial`, `Point` and `Independent` are also identical token for token
(`e62c101:Seed.lean:32-35`, `:38-52`, `:99-101` versus `SkewSeed.lean:55-58`,
`:61-79`).

The baseline declarations of `Seed` that `SkewSeed` does **not** repeat are
`Point.exchange`, `Point.frozen_ne_zero`, `Point.zeroSet`, `mem_zeroSet`,
`unitPoint`, `unitPoint_a`, `unitPoint_b`, `point_nonempty` and
`wellFounded_iff_no_directed_cycle`. All of them are available for `S.toSeed`
from the weighted `Seed` (whose own versions are byte-identical to the
baseline's), and the two projections `Point.a`, `Point.b` are re-supplied for the
old carrier in `SkewSeedRecovery.lean:72-79` as the same `p.1.1`, `p.1.2`. In
particular nonemptiness of the old carrier is obtained from
`Seed.point_nonempty S.toSeed` transported along `pointHomeomorph`, not assumed.

### 2.2 `toSeed` has `E := B`, `D = 1`, hence `K = B`: no sign flip, no time reversal

```lean
def toSeed : Seed d where
  E := S.B
  mutable := S.mutable
  D := fun _ => 1
  …
@[simp] theorem toSeed_K (i j : Fin d) : (S.toSeed).K i j = (S.B i j : ℚ) := by simp [Seed.K]
```

with `Seed.K i j = (S.E i j : ℚ) * S.D j` (`Seed.lean:69-70`). So
`K = B` — **not** `-B`, **not** `Bᵀ`. The weighted target's form coefficient is
`(S.K i j : ℂ)` (`GeometryTarget.lean:82`; the baseline's was `(S.B i j : ℂ)`,
`e62c101:GeometryTarget.lean:79` — the *only* non-docstring difference between the
two files, confirmed by `diff`). Composing,
`toSeed_K_complex : (((S.toSeed).K i j : ℚ) : ℂ) = (S.B i j : ℂ)`, so

```lean
theorem torus_anchor_old_matrix (P : SmoothPresentation S.toSeed) (p) (v w) :
    P.logarithmicImaginaryValue p v w =
      ((1 / 2 : ℂ) * ∑ i, ∑ j, (S.B i j : ℂ) *
        ((P.coordinateDifferential i p v / p.a i) * (P.coordinateDifferential j p w / p.a j) -
         (P.coordinateDifferential i p w / p.a i) * (P.coordinateDifferential j p v / p.a j))).im
```

is the baseline's `logarithmicImaginaryValue` **expression for expression**: the
factor `1/2`, the index order `i` then `j`, the antisymmetrized product, the
division by `p.a i`/`p.a j`, the outer `.im`, and the `Int`-cast coefficient
`(S.B i j : ℂ)`. No transpose, no extra factor, **no sign flip** — hence the
Liouville field (determined by `ι_Z dλ = λ`, and unique by
`LiouvilleData.field_eq_liouvilleVector`) is not negated and the flow is not
time reversed. This matters because `trappedSet` is a **forward**-orbit
condition and is not invariant under time reversal; the sign is therefore the
pivotal clause of acceptance check 2, and it is proved, not asserted.
`SkewSeed.lean`'s module docstring states why the alternative `E := Bᵀ` (which
gives `K = -B`) would have been wrong.

### 2.3 The two carriers are the same subset, and `pointHomeomorph` is the identity on ambient coordinates

`carrier_set_eq` (elaborated):

```
@SkewSeed.carrier_set_eq : ∀ {d : ℕ} (S : SkewSeed d),
  {x | (∀ (i : S.Mutable), x.1 ↑i * x.2 i = S.positiveMonomial x.1 ↑i + S.negativeMonomial x.1 ↑i) ∧
       ∀ f ∉ S.mutable, x.1 f ≠ 0} =
  {x | (∀ (i : S.toSeed.Mutable), x.1 ↑i * x.2 i = S.toSeed.positiveMonomial x.1 ↑i + S.toSeed.negativeMonomial x.1 ↑i) ∧
       ∀ f ∉ S.toSeed.mutable, x.1 f ≠ 0}
```

— an equality of two subsets of the **same** ambient type
`(Fin d → ℂ) × (S.Mutable → ℂ)` (`S.toSeed.mutable = S.mutable := rfl`, so
`S.toSeed.Mutable` and `S.Mutable` are the same type). The proof is
`carrier_predicate_iff`, which rests on `toSeed_monomial_sum`: the two exchange
monomials are *interchanged* (`toSeed_positiveMonomial`,
`toSeed_negativeMonomial`, by skew symmetry `[B j i]_+ = [-B i j]_+`) and only
their sum enters the exchange equation. `pointHomeomorph` is the identity map on
`.val` (§1.2, three `rfl`s), so the identification is not a choice of
coordinates — it is the identity.

### 2.4 Baseline clause map

Baseline statement at `e62c101`: `FirstGeometricTarget :=
∀ (d) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S` with

```lean
def LiouvilleSkeletonTarget (S : Seed d) : Prop :=
  Dense (initialTorus S) ∧
  ∃ (P : SmoothPresentation S) (L : LiouvilleData P),
    (∀ (p : S.Point), p ∈ initialTorus S → ∀ v w,
      evalTwo (P.manifold.exteriorDerivative L.primitive) p v w =
        P.logarithmicImaginaryValue p v w) ∧
    trappedSet L.completeFlow.flow = coordinateCap S
```

plus the baseline's separate theorems for the stratified form, stratum
compactness and the chart rank. Clause by clause, with the type each recovered
clause lives on:

| baseline clause (where) | recovered Lean clause | lives on |
| --- | --- | --- |
| carrier = exchange subtype, inherited topology (`Seed.Point`) | `S.Point` itself, and `S.toSeed.Point` via `carrier_set_eq` + `pointHomeomorph` (identity on `.val`, homeomorphism) | **`S.Point`** and `S.toSeed.Point`, identified |
| charted space of dimension `2*d` (`SmoothPresentation.charts`, model `Model (2*d)`) | `P : SmoothPresentation S.toSeed` inside `∃ P`, witness `SmoothAtlas.presentation S.toSeed _` | `S.toSeed.Point` **only** (R-N1) |
| `IsManifold … ∞` (`SmoothPresentation.smooth`) | field of the same `P` | `S.toSeed.Point` **only** (R-N1) |
| ambient inclusion smooth (`inclusion_smooth`) | field of the same `P` | `S.toSeed.Point` **only** (R-N1) |
| ambient inclusion immersive (`inclusion_immersion`) | field of the same `P` | `S.toSeed.Point` **only** (R-N1) |
| dense initial torus `T = {z₁⋯zₙ ≠ 0}` (`Dense (initialTorus S)`) | `SkewSeed.dense_initialTorus : Dense (initialTorus S)`, first conjunct of `skeleton_recovery`; proof transports `ClusterSkeleton.dense_initialTorus S.toSeed` along `(pointHomeomorph S).symm.isDenseEmbedding` | **`S.Point`** |
| smooth real primitive `λ` (`LiouvilleData.primitive`, `.smooth_primitive`) | fields of `L` inside `∃ L`; witness `FullSkeleton.liouvilleData S.toSeed _ 1 3 1` | `S.toSeed.Point` **only** (R-N1) |
| `ω = dλ` nondegenerate and closed on all of the space (`LiouvilleData.symplectic : IsSymplecticOn … Set.univ`) | field of the same `L` | `S.toSeed.Point` **only** (R-N1) |
| torus anchor with coefficient `(S.B i j : ℂ)` (the anchor clause) | the anchor conjunct of `skeleton_recovery`, coefficient `↑(S.B i j)` = the old **integer** matrix; `SkewSeed.liouvilleData_torus_anchor_old_matrix` for the canonical witness; `SkewSeed.torus_anchor_old_matrix` for any `P` | `S.toSeed.Point` (points of the weighted torus; §2.5) |
| Liouville field `Z`, smooth, `ι_Z ω = λ` (`LiouvilleData.field`, `.smooth_field`, `.contraction`) | fields of the same `L` | `S.toSeed.Point` **only** (R-N1) |
| complete jointly smooth flow for all real times (`CompleteLiouvilleFlow.flow`, `.smooth_action`, `.solves`) | field `L.completeFlow`; read on the old carrier as `S.conjFlow L.completeFlow.flow`, the same flow at the same times (§1.2) | flow constructed on `S.toSeed.Point`; **`S.Point`** for its orbits/trapped set |
| `trappedSet = coordinateCap` (last conjunct) | `trappedSet (S.conjFlow L.completeFlow.flow) = S.coordinateCap`; `SkewSeed.liouvilleData_trappedSet_conjFlow` for the canonical witness | **`S.Point`** |
| stratified form `C_B = ⋃_I Λ_I` (`e62c101:CapStrata.lean`, `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`) | `trappedSet (S.conjFlow …) = ⋃ I, S.lambdaStratum ↑I`, indexed by `{I // S.Independent I}` — the **old** independence predicate, with `(S.toSeed).Independent I = S.Independent I := rfl`; also `SkewSeed.coordinateCap_eq_iUnion_lambdaStratum` | **`S.Point`** |
| each `Λ_I` compact, `C_B` compact (`e62c101:CapStrata.lean:86`) | `SkewSeed.isCompact_lambdaStratum S : ∀ I ⊆ S.mutable, IsCompact (S.lambdaStratum I)` and `SkewSeed.isCompact_coordinateCap S : IsCompact S.coordinateCap` | **`S.Point`** |
| chart rank `complementRank = d − 2|I|` (`e62c101:IndependentNodeSmooth.lean:264-266`) | the same theorem, textually unchanged at F, instantiated at `S.toSeed`; verified by the elaborating `example` below | statement about `complementRank`, no carrier involved |

The chart-rank clause needs no transport at all, which the following `example`
(elaborates at F) makes precise:

```lean
example (S : SkewSeed d) (I : Finset (Fin d)) (h : S.Unimodular) (hI : S.Independent I) :
    SplitIntegerRows.complementRank (independentRowRightInverse S.toSeed I) = d - 2 * I.card :=
  IndependentNodeChart.complementRank_eq_sub_two_mul_card S.toSeed I h hI
```

It typechecks because `toSeed_unimodular_iff` and `toSeed_independent_iff` are
both `Iff.rfl`, so the baseline hypotheses are literally the weighted ones.
`diff` confirms the block `e62c101:IndependentNodeSmooth.lean:255-280` is
byte-identical at F.

### 2.5 What is NOT literally re-obtained on the old subtype `S.Point`

Exhaustively, and without softening:

1. **The charted space and the manifold structure.** There is no
   `ChartedSpace (Model (2*d)) S.Point` and no `IsManifold … S.Point` anywhere at
   F. The dimension-`2d` smooth structure is asserted only for
   `S.toSeed.Point`.
2. **The smooth immersive ambient inclusion.** `inclusion_smooth` and
   `inclusion_immersion` are asserted for `fun p : (S.toSeed).Point => p.val`,
   not for `fun p : S.Point => p.val`. (The two functions agree after composing
   with `pointHomeomorph`, whose `.val` identity is `rfl`, but no Lean statement
   says so about smoothness, because there is no smooth structure on the source.)
3. **The primitive, the two-form, its nondegeneracy, the field and the
   contraction equation.** All are fields of `L : LiouvilleData P` with
   `P : SmoothPresentation S.toSeed`, so they are forms and vector fields on
   `S.toSeed.Point`. Nothing of the kind is defined on `S.Point`.
4. **The completeness data of the flow** (`smooth_action`, `solves`) is asserted
   for the flow on `S.toSeed.Point`. What is re-obtained on `S.Point` is the
   conjugate flow as a `Flow ℝ S.Point` (continuity and both group laws proved)
   and its trapped set; joint smoothness in `(t, p)` on the old carrier is not
   stated — it cannot be, for lack of a smooth structure there.
5. **The anchor clause quantifies over the weighted torus.** The packaged
   statement reads `∀ p ∈ initialTorus S.toSeed`, while the density conjunct
   reads `Dense S.initialTorus` on the old carrier. The two sets correspond under
   the identity-on-coordinates homeomorphism (`mem_initialTorus_iff` is
   `Iff.rfl`; `preimage_initialTorus`, `image_initialTorus` both proved), so no
   content is lost, but the package does mix the two carriers across its clauses.
6. **No single Lean proposition is "the baseline target for `S : SkewSeed d`".**
   The baseline `LiouvilleSkeletonTarget` is defined only for `Seed`, so the old
   theorem as a self-contained Prop over the old carrier does not exist at F; the
   recovery is the conjunction (a) + (b) + (c).

What *is* literally re-obtained on `S.Point` — and this is the whole
topological/dynamical content — is: the carrier and its inherited topology,
density of the old torus, the skeleton identity `Skel = C_B` for the same flow at
the same times, its stratified form over the old independence index set, and
compactness of each old stratum and of the old cap.

### 2.6 Judgement on acceptance check 2

Acceptance check 2 asks for "a proved recovery of the old `D = I` theorem,
preserving the actual geometry and convention/sign matching", and the roadmap's
input paragraph adds: "If preserving an internal row convention, prove the exact
convention equivalence, including the exchange space and form sign. Monomial
interchange alone is insufficient when `D` is not the identity."

Measured against that text:

* **Convention equivalence of the exchange space: proved,** not argued —
  `carrier_set_eq` (an equality of subsets of one ambient space), with
  `pointHomeomorph` the identity on coordinates and `carrier_predicate_iff`
  reducing it to `toSeed_monomial_sum`. Monomial interchange alone is *not* what
  is relied on: the set equality is proved, and separately the form coefficient
  is matched.
* **Form sign: proved** — `toSeed_K : K = B`, no transpose, no negation, no extra
  factor, lifted to the target's actual form by `torus_anchor_old_matrix` and
  stated for the constructed Liouville datum by
  `liouvilleData_torus_anchor_old_matrix`. Consequently no time reversal, which
  is exactly what the forward-orbit skeleton needs.
* **The actual geometry: preserved** in the sense the baseline itself uses.
  The baseline quantifies the smooth structure, primitive, field and flow
  **existentially**; the recovery supplies exactly such witnesses, on a carrier
  that is the same subset of the same ambient space, and returns every
  point-level conclusion of the baseline on the old subtype.
* **The route is the prescribed one.** The stage-A audit item 4 specifies "the
  minimal adequate package" as precisely (a) the instantiation, (b)
  `torus_anchor_old_matrix`, (c) the transported old objects, and its RISK R1(2)
  says: "transporting a *smooth* structure requires pushing `SmoothPresentation`
  along it …, **or** stating recovery directly for `S.toSeed` as in (a)+(b)+(c).
  State which, and do not leave the old smooth structure implicitly claimed."
  The stage-B audit's R7 repeats the same alternative. F takes the second branch
  and **states which**: `SkewSeedSkeleton.lean`'s module docstring says "No
  transported smooth structure on `S.Point` is claimed — `pointHomeomorph` is a
  homeomorphism, not a diffeomorphism — and no term identity of the recovered
  flow with the baseline library's constructed flow is claimed", and
  `docs/weighted-recovery-plan.md` §2 records the decision with its reasons. So
  the old smooth structure is not implicitly claimed anywhere, and the
  requirement attached to the route by the reviewer is met.
* The stronger pointwise claim that R7 flags as *true* (at `D = 1` the weighted
  primitive is pointwise the baseline's) is **not** claimed here, and R7 itself
  records that *stating* it needs either the smooth transport or the missing
  `rho_neg`/`vartheta_neg` lemmas of RISK R5 — both outside final assembly's
  scope.

**Verdict item 2 / acceptance check 2: PASS.** The recovery is a genuine
recovery: nothing is weakened, no sign is flipped, the flow is not reversed, the
hypothesis is the baseline's and nothing more, and the old-carrier conclusions
are literal. The six items of §2.5 are a *scope* limitation of the chosen,
pre-approved route, not an error, and they are documented in the source itself.
They are recorded as the carried risk **R-N1** so that the maintainer accepts
check 2 with them in view rather than unknowingly.

Minimal additional Lean statements that would close R-N1, with honest sizes:

* **(i) Cheap, recommended: make the package self-contained on the old
  carrier.** Add to `skeleton_recovery` (and
  `skeleton_recovery_of_parameters`) a clause quantified over the *old* torus,
  and the ambient-identity clause:
  ```lean
  (∀ p : S.Point, p ∈ initialTorus S → ∀ v w : P.manifold.Tangent (pointHomeomorph S p),
      evalTwo (P.manifold.exteriorDerivative L.primitive) (pointHomeomorph S p) v w =
        ((1 / 2 : ℂ) * ∑ i, ∑ j, (S.B i j : ℂ) * (…)).im) ∧
  (∀ p : S.Point, (pointHomeomorph S p).val = p.val)
  ```
  Both follow from `liouvilleData_torus_anchor_old_matrix` with
  `mem_initialTorus_iff` (`Iff.rfl`) and from `pointHomeomorph_val` (`rfl`).
  **Size: ~12-20 lines, no new mathematics, one file.** This removes the
  carrier-mixing of §2.5 item 5 and §2.5 item 6's "no old-carrier form clause"
  reading, and is cheap enough that it is worth requiring.
* **(ii) The full `SmoothPresentation`-level transport along `pointHomeomorph`**
  (closing §2.5 items 1-4 literally). Route: `ChartedSpace (Model (2*d)) S.Point`
  by pushing `P.charts` along `(pointHomeomorph S).symm` — Mathlib has
  `Homeomorph.chartedSpace` (`Mathlib/Geometry/Manifold/ChartedSpace.lean:610`),
  but it routes through `IsLocalHomeomorph.localInverseAt` and a `choose`, so a
  hand-built atlas `{h ≫ₕ e | e ∈ P.atlas}` with
  `Homeomorph.toOpenPartialHomeomorph` is cleaner; then
  `IsManifold`/`HasGroupoid` for it, because the transition maps
  `(h ≫ₕ e).symm ≫ₕ (h ≫ₕ e')` are `EqOnSource`-equal to `e.symm ≫ₕ e'` and
  `contDiffGroupoid` is closed under `EqOnSource`; then `inclusion_smooth` and
  `inclusion_immersion` via `ContMDiff.comp` and the chain rule, using that
  `(fun p : S.Point => p.val) = (fun q => q.val) ∘ pointHomeomorph` is `rfl`;
  then `LiouvilleData` by FsFltz's `SmoothManifold.pullback` with
  `exteriorDerivative_pullback` (`FsFltz/Geometry/ExteriorDerivative.lean:252`)
  and `CompleteLiouvilleManifold.map_field`
  (`FsFltz/Geometry/LiouvilleNaturality.lean:26`), nondegeneracy through
  `Diffeomorph.mfderivToContinuousLinearEquiv`, and `CompleteLiouvilleFlow`
  with `flow := conjFlow` (already built), `smooth_action` and `solves`
  transported through the new diffeomorphism. Mathlib supplies no
  `IsManifold` transport and FsFltz supplies no wholesale transport of a
  `CompleteLiouvilleManifold` along a `SmoothEquiv`, so all of this is new.
  **Size: ~300-600 lines in one new module, no new mathematics**, consistent with
  `docs/weighted-recovery-plan.md` §2's own assessment ("a separate
  construction, not a corollary of `pointHomeomorph_val = rfl`").
* **(iii) The literal baseline proposition for `SkewSeed`** — duplicating
  `SmoothPresentation`, `LiouvilleData` and `LiouvilleSkeletonTarget` over
  `SkewSeed` and proving the duplicate. **Size: ~60-80 lines of statements plus
  (ii) as its proof**; strictly more work than (ii) and no extra content, so it
  is not recommended.

---

## 3. Non-skew instance — PASS

### 3.1 The literals, entry by entry against the roadmap

Roadmap check 3 (at `e62c101:docs/roadmap.md`): "a consumer instantiating the
final theorem on `E = [[0,1,-1,0],[-2,0,0,-1],[1,0,0,0],[0,1,0,0]]`,
`D = diag(1,2,1,2)`, `M = {0,1}` in Lean's zero-based indexing."

`Examples.nonSkewSeed` is *defined* by those literals
(`ClusterSkeleton/Examples/NonSkew.lean:28-41`):

```lean
def nonSkewMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, -1, 0;
    -2, 0, 0, -1;
     1, 0, 0, 0;
     0, 1, 0, 0]
def nonSkewWeights : Fin 4 → ℚ := ![1, 2, 1, 2]
def nonSkewMutable : Finset (Fin 4) := {0, 1}
def nonSkewSeed : Seed 4 where E := nonSkewMatrix; mutable := nonSkewMutable; D := nonSkewWeights; …
```

and `nonSkewSeed_side_checks` re-asserts them as *literals*, as elaborated:

```
Examples.nonSkewSeed_side_checks : Examples.nonSkewSeed.E = !![0, 1, -1, 0; -2, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] ∧
  Examples.nonSkewSeed.D = ![1, 2, 1, 2] ∧
    Examples.nonSkewSeed.mutable = {0, 1} ∧ …
```

Entry by entry, zero-based, each line verified by an elaborating `example` with
`norm_num [nonSkewSeed_E, nonSkewMatrix]` at F:

| index | roadmap | Lean `nonSkewSeed.E` |
| --- | --- | --- |
| row 0 | `0, 1, -1, 0` | `E 0 0 = 0`, `E 0 1 = 1`, `E 0 2 = -1`, `E 0 3 = 0` |
| row 1 | `-2, 0, 0, -1` | `E 1 0 = -2`, `E 1 1 = 0`, `E 1 2 = 0`, `E 1 3 = -1` |
| row 2 | `1, 0, 0, 0` | `E 2 0 = 1`, `E 2 1 = 0`, `E 2 2 = 0`, `E 2 3 = 0` |
| row 3 | `0, 1, 0, 0` | `E 3 0 = 0`, `E 3 1 = 1`, `E 3 2 = 0`, `E 3 3 = 0` |

`D`: `D 0 = 1`, `D 1 = 2`, `D 2 = 1`, `D 3 = 2` — i.e. `diag(1,2,1,2)`, verified
entry by entry. `M`: `nonSkewSeed.mutable.card = 2` with `0 ∈`, `1 ∈`, `2 ∉`,
`3 ∉` (all by `decide` at F), so `{0,1}` really is the two-element set of the
zero-based vertices 0 and 1 and not a degenerate `Fin 4` literal. **All sixteen
matrix entries, all four weights and the mutable set match the roadmap exactly.**

### 3.2 The five side facts are proved, not assumed

`nonSkewSeed_side_checks`'s proof term is
`⟨nonSkewSeed_E, nonSkewSeed_D, nonSkewSeed_mutable, nonSkewSeed_unimodular,
nonSkewSeed.D_pos, nonSkewSeed.skewSymmetrizable, nonSkewSeed.acyclic,
nonSkewSeed_not_skew⟩` — every component is a theorem or a structure field of a
`def`, with no hypothesis and no `sorry`:

1. **`det E = 1`** — `nonSkewSeed_unimodular : nonSkewSeed.Unimodular`, proved by
   `norm_num [Seed.Unimodular, nonSkewMatrix, Matrix.det_succ_row_zero,
   Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]`. Axioms: exactly
   `[propext, Classical.choice, Quot.sound]` (checked by `#print axioms`); **no
   `Lean.ofReduceBool`**, i.e. no `native_decide`.
2. **`0 < D i`** — `nonSkewSeed.D_pos`, the structure field, proved
   `fin_cases i <;> norm_num [nonSkewWeights]`.
3. **`(E i j : ℚ) * D j = -((E j i : ℚ) * D i)`** — `nonSkewSeed.skewSymmetrizable`,
   proved `fin_cases i <;> fin_cases j <;> norm_num [nonSkewMatrix, nonSkewWeights]`,
   i.e. all 16 pairs checked.
4. **Mutable-block acyclicity, in the orientation of the `Seed.acyclic` field** —
   `nonSkewSeed.acyclic : WellFounded (fun i j : {i // i ∈ nonSkewMutable} => 0 < nonSkewSeed.E i j)`,
   proved by `Measure` descent on `i.1.val` plus a four-case analysis. The
   elaborated side-check conjunct is
   `WellFounded fun i j => 0 < Examples.nonSkewSeed.E ↑i ↑j` — the field's own
   orientation `0 < E i j` (`Seed.lean:43`), not the exponent orientation
   `0 < B i j = 0 < E j i`. Correct as stated.
5. **`E` is NOT skew** — `nonSkewSeed_not_skew : ¬ ∀ i j, nonSkewSeed.E i j = -nonSkewSeed.E j i`,
   proved from `E 0 1 = 1` and `E 1 0 = -2` (`nonSkewSeed_entries`), plus
   `nonSkewSeed_weights_ne : D 0 ≠ D 1` which rules out a single-constant
   rescaling.

### 3.3 The skeleton statement comes from the universal theorem

```lean
theorem nonSkewSeed_liouvilleSkeletonTarget : LiouvilleSkeletonTarget nonSkewSeed :=
  FullSkeleton.liouvilleSkeletonTarget nonSkewSeed nonSkewSeed_unimodular

theorem nonSkewSeed_target_of_firstGeometricTarget : LiouvilleSkeletonTarget nonSkewSeed :=
  FullSkeleton.firstGeometricTarget 4 nonSkewSeed nonSkewSeed_unimodular
```

The second is the quantified theorem itself applied at `d = 4` and this seed —
no separate argument, no specialized construction. The flow statements
`nonSkewSeed_trappedSet` and `nonSkewSeed_trappedSet_iUnion` are
`FullSkeleton.liouvilleData_trappedSet` and
`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` applied at `nonSkewSeed`. The
following `example` elaborates at F, confirming the instantiation route
independently of the file:

```lean
example : LiouvilleSkeletonTarget Examples.nonSkewSeed :=
  FullSkeleton.firstGeometricTarget 4 Examples.nonSkewSeed Examples.nonSkewSeed_unimodular
```

### 3.4 "Supplements, and never replaces, the universal theorem"

`FullSkeleton.firstGeometricTarget : FirstGeometricTarget` is unchanged
(`ClusterSkeleton/FullSkeleton.lean` is **byte-identical to `e62c101`**, `diff`
exit 0; `ClusterSkeleton/GeometryTarget.lean` differs from `e62c101` only in the
form coefficient and a docstring, and is byte-identical to `114d639`), and
`FirstGeometricTarget` still elaborates to
`∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S` (verified by
`example … := rfl`). Nothing in the example modules touches it; the consumer adds
declarations and removes none (item 4). No `native_decide`, `decide +native`,
`Lean.ofReduceBool`, `unsafe` or `implemented_by` occurs anywhere in
`ClusterSkeleton.lean`, `ClusterSkeleton/` or `verification/` (grep, item 5).

**Verdict item 3 / acceptance check 3: PASS.**

---

## 4. Consumers — PASS

`verification/FullSkeletonConsumer.lean` at F, compared with `e62c101` and with
`114d639`:

* Lines 1-64 are **byte-identical** to both baselines except for two added
  `import` lines (`ClusterSkeleton.SkewSeedSkeleton`,
  `ClusterSkeleton.Examples.NonSkewSkeleton`) and a blank line before the new
  section (`diff` output: `1a2,3` and `62a65,67` only). In particular
  ```lean
  theorem original_general_target : FirstGeometricTarget :=
    FullSkeleton.firstGeometricTarget
  ```
  is present and **unchanged in type**, as are `compact_forward_iff_cap`,
  `compact_forward_iff_coordinates`, `initially_zero_partner`,
  `forward_cap_is_trapped`, `complete_manifold_skeleton` and `original_target`.
  Nothing was removed (+108 lines, −0).
* `namespace NonSkewConsumer` genuinely applies the final theorem:
  `non_skew_target := nonSkewSeed_liouvilleSkeletonTarget` (itself
  `FullSkeleton.liouvilleSkeletonTarget …`),
  `non_skew_compact_forward_iff_cap` and `…_coordinates` are the *generic*
  consumer lemmas `FullSkeletonConsumer.compact_forward_iff_cap/_coordinates`
  applied at `nonSkewSeed` with `nonSkewSeed_unimodular`, and
  `non_skew_skeleton_iUnion := nonSkewSeed_trappedSet_iUnion hε hκ hδ`. The only
  variables in the section are the cutoff parameters `{ε κ δ}` with their
  admissibility hypotheses — the seed's unimodularity is supplied by the
  **proved** `nonSkewSeed_unimodular`, never restated as a hypothesis.
* `namespace RecoveryConsumer` genuinely applies the recovery theorem:
  `old_recovery` writes out the whole conjunction by hand and closes it with
  `:= skeleton_recovery S hdet`; `old_skeleton_isCompact` destructures the
  existential (`obtain ⟨-, P, L, -, hcap, -⟩ := skeleton_recovery S hdet`) and
  concludes with `hcap ▸ isCompact_coordinateCap S`, which is a real use of the
  old-carrier compactness; `old_weighted_target := SkewSeed.liouvilleSkeletonTarget S hdet`.
  The only hypothesis is `(hdet : S.Unimodular)`, the theorem's own.
* No `sorry`, no local `axiom`, no `opaque`, no restated hypothesis anywhere in
  the file (grep, §5.4).
* `lake env lean verification/FullSkeletonConsumer.lean` → **exit 0, no output**.

**Verdict item 4: PASS.** The consumer supplements the universal theorem: the
quantified `original_general_target` is untouched and the new sections are
additional applications.

---

## 5. Axiom audit — PASS on coverage and axioms, RISK R-N2 on the root list

### 5.1 Module array versus `ClusterSkeleton/**/*.lean`

Counted programmatically at F from the `modules := #[…]` array of
`verification/AxiomAudit.lean` and from the filesystem:

| commit | audit module array | `ClusterSkeleton/**/*.lean` | symmetric difference |
| --- | --- | --- | --- |
| `e62c101` (baseline) | 58 | 58 | ∅ |
| `114d639` (stage C) | 58 | 62 | `SkewSeed`, `SymmetrizerAlgebra`, `SeedAlgebra`, `Examples.NonSkew` **unaudited** |
| **F** | **65** | **65** | **∅** |

So F closes the module half of the final statement review's **DEFECT A1**
exactly (and the seven names added are the four A1 names plus the three new
modules). This is the equality `scripts/verify.py:105` enforces
(`set(audited_modules) != expected_modules → RuntimeError`). *Correction to the
handoff's §E:* the array at `114d639` had **58** entries, not 60.

The import closure of `ClusterSkeleton.lean` was walked independently: **65
modules, equal to the file set** (no module outside the closure, no closure
entry without a file), so the library build is the whole-library check.

### 5.2 `#print axioms` roots: 25, and what is missing

F's root list is the **11 baseline roots unchanged** —
`FullSkeleton.trappedSet_eq_coordinateCap`, `.liouvilleData`,
`.liouvilleData_flow`, `.torus_anchor`, `.liouvilleData_trappedSet`,
`.liouvilleSkeletonTarget_of_parameters`, `.liouvilleSkeletonTarget`,
`.firstGeometricTarget`, `.trappedSet_eq_iUnion_lambdaStratum`,
`coordinateCap_eq_iUnion_lambdaStratum`,
`IndependentNodeChart.complementRank_eq_sub_two_mul_card` — plus **14 new
roots**: `SkewSeed.liouvilleSkeletonTarget`, `.skeleton_recovery`,
`.skeleton_recovery_of_parameters`, `.dense_initialTorus`,
`.torus_anchor_old_matrix`, `.liouvilleData_torus_anchor_old_matrix`,
`.trappedSet_conjFlow_eq_coordinateCap`, `.liouvilleData_trappedSet_conjFlow`,
`.liouvilleData_trappedSet_conjFlow_iUnion`, `Examples.nonSkewSeed_side_checks`,
`.nonSkewSeed_liouvilleSkeletonTarget`,
`.nonSkewSeed_target_of_firstGeometricTarget`, `.nonSkewSeed_trappedSet`,
`.nonSkewSeed_trappedSet_iUnion`. `scripts/verify.py:23`'s
`FINAL_TARGET = 'ClusterSkeleton.FullSkeleton.firstGeometricTarget'` is among
them, as that script requires.

Compared with the final statement review's item 6 PDF-clause map and the root
list its DEFECT A1 proposes (read at `24b7bef8…`), the following clauses a reader
needs for the **full** PDF theorem are **not** roots at F:

| PDF clause | missing root |
| --- | --- |
| (4) each `Λ_I` compact; `C_E` compact | `ClusterSkeleton.isCompact_lambdaStratum`, `ClusterSkeleton.isCompact_coordinateCap` |
| `U_I ≅ N^I × (C*)^{n−2|I|}` | `ClusterSkeleton.IndependentNodeChart.homeomorph` |
| `2|I| ≤ n` | `ClusterSkeleton.IndependentNodeChart.two_mul_card_le` |
| real dimension `2n` of the node space | `ClusterSkeleton.IndependentNodeChart.vector_finrank_real` |
| weighted algebra facts the proof rests on | `Seed.K_transpose`, `Seed.det_K_of_unimodular`, `Seed.acyclic_exponent`, `SeedAlgebra.isUnit_det_Kreal`, `SeedAlgebra.exists_inverse_bound_Kreal`, `SeedAlgebra.c_inv_K`, `SymmetrizerAlgebra.K_transpose`, `SymmetrizerAlgebra.isUnit_det_K` |
| the old-carrier compactness clauses of the recovery | `SkewSeed.isCompact_coordinateCap`, `SkewSeed.isCompact_lambdaStratum` (used by `RecoveryConsumer.old_skeleton_isCompact`) |

(`dense_initialTorus` and the stratified form need no separate root: the first is
inside `LiouvilleSkeletonTarget` and the second is root
`coordinateCap_eq_iUnion_lambdaStratum`.)

This is **RISK R-N2**, severity low: the `run_cmd` loop audits *every*
declaration of *every* listed module, so all of the above are in fact axiom-
audited (they live in `CapStrata`, `IndependentNodeChart`/`IndependentNodeSmooth`,
`Seed`, `SeedAlgebra`, `SymmetrizerAlgebra`, `SkewSeedRecovery`, all of which are
in the 65). What is short is the receipt's `audited_final_declarations` list,
i.e. the human-legible clause inventory. **Minimal fix:** append those 17
`#print axioms` lines to `verification/AxiomAudit.lean`. **Size: 17 lines, no
proof work.** `verification/` is owned by the verification/receipts mission and is
deliberately untouched here and by final assembly.

### 5.3 The audit is still substantive — quoted mechanisms

Unchanged at F from the baseline (only the module array and the root block grew):

* **Forbidden-axiom failure**, inside the per-declaration loop:
  ```lean
  for axiomName in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Forbidden axiom {axiomName} in {name}"
  ```
  i.e. a hard `throwError` (non-zero exit), not a log line.
* **Nonzero-count check per module**:
  ```lean
  for i in [:modules.size] do
    if counts[i]! == 0 then
      throwError "No declarations audited in {modules[i]!}"
  ```
  so a mistyped or vacuous module name fails the audit.
* **Generated-declaration supplement**, a second `run_cmd` over
  `FsFltz.Geometry.SmoothManifold.evalTwo.eq_1` and
  `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1`, with
  `unless env.contains name do throwError "Missing generated declaration {name}"`
  and the same allowlist check.
* The traversal is over `env.constants.toList` filtered by
  `env.getModuleIdxFor?`, so **private and generated declarations are included**,
  and `collectAxioms` is the native transitive collector.
* On top of that, `scripts/verify.py` (read only) re-parses the log, requires
  `set(expected) == reported` for the `#print axioms` roots, requires
  `FINAL_TARGET` among them, re-checks `actual - ALLOWED == ∅` per root,
  requires the audited-module set to equal `ClusterSkeleton/**/*.lean`, greps
  every library file for `^\s*(axiom|opaque)\b`, and re-verifies dependency
  revisions and source hashes before and after the build.

### 5.4 Runs on the reviewed commit

| check | result |
| --- | --- |
| `horizon-lean-check ClusterSkeleton` | `status: "passed"`, `returncode: 0`, `snapshot_verified: true`, **9029 jobs**, `Lake 5.0.0-src+5045d00 / Lean 4.34.1`, cache `local` |
| `lake env lean verification/FullSkeletonConsumer.lean` | **exit 0**, empty output |
| `lake env lean verification/AxiomAudit.lean` | **exit 0** |
| modules audited | **65**, equal to `ClusterSkeleton/**/*.lean` (§5.1) |
| total audited declarations | **`TOTAL_AUDITED: 1811`** (1811 `AUDIT` lines; the two `GENERATED AUDIT` lines are separate) |
| `#print axioms` roots reported | **25 of 25**, zero "does not depend on any axioms" |
| axiom set of **every** root | exactly `[propext, Classical.choice, Quot.sound]` (after whitespace normalization of the wrapped log lines; non-conforming roots: **none**) |
| axiom sets over all 1811 declarations | 1703 × `{propext, Classical.choice, Quot.sound}`, 87 × `{propext}`, 18 × `{propext, Quot.sound}`, 3 × `∅`, 2 × `{Quot.sound}` — every one a **subset** of the allowlist, zero non-conforming |
| generated declarations | both present, both `[propext, Classical.choice, Quot.sound]` |
| per-module counts, new modules | `SkewSeedRecovery` 44, `SkewSeedSkeleton` 7, `Examples.NonSkewSkeleton` 5; for reference `SeedAlgebra` 101, `SkewSeed` 52, `SymmetrizerAlgebra` 35, `Examples.NonSkew` 22, `GeometryTarget` 51, `FullSkeleton` 10, `Seed` 77 |
| forbidden constructs | `grep -rnE "\bsorry\b\|\badmit\b\|^\s*(axiom\|opaque)\b\|native_decide\|decide \+native\|Lean\.ofReduceBool\|\bunsafe\b\|implemented_by\|extern\|@\[csimp\]"` over `ClusterSkeleton.lean`, `ClusterSkeleton/`, `verification/` → **no hits** |

### 5.5 Receipt state (observation, not a defect)

`verification/accepted-library.json` at F still pins the **skew-symmetric
baseline**: `accepted_commit: 4c02c1e5bbc68907552632344ae04017d82a30b4`, 58
file hashes, of which 30 now differ and 7 library files are absent from it; and
`verification/publication-check.json` is the 2026-11-08 baseline receipt. So
`scripts/verify.py` would **fail at F** at
`'Library differs from the accepted source manifest'` (line 102) before reaching
the module comparison. This is by design — roadmap check 5 says "update the
accepted source manifest only after reviewed integration" and check 6 requires
new receipts — and both files are byte-identical to `114d639`, i.e. untouched.
The verification/receipts mission must refresh `accepted-library.json` to the
reviewed commit (65 files) and regenerate `publication-check.json`,
`axioms.log`, `build.log`, `final-consumer.log`, `toolchain.log`.

**Verdict item 5: PASS** on module coverage, audit substance and axiom results;
**RISK R-N2** on the `#print axioms` root list (17 missing clause roots named in
§5.2, fix = 17 lines, owner = verification/receipts mission).

---

## 6. Additivity versus the reviewed tree `114d639` — PASS

`git diff --name-status 114d639 F` and a blob-OID comparison of the trees give
**12 paths** (the handoff's "exactly 11" is a miscount of its own list of
6 + 6), `+3104 / −6`:

**New files (6):**

| path | note |
| --- | --- |
| `ClusterSkeleton/SkewSeedRecovery.lean` | recovery scaffolding, 44 audited declarations |
| `ClusterSkeleton/SkewSeedSkeleton.lean` | the recovery theorem, 7 declarations |
| `ClusterSkeleton/Examples/NonSkewSkeleton.lean` | the non-skew instance, 5 declarations |
| `docs/weighted-recovery-plan.md` | documentation |
| `docs/reviews/stage-a-semantic-audit.md` | documentation |
| `docs/reviews/stage-b-semantic-audit.md` | documentation |

**Changed files (6), with the exact textual change:**

| path | change |
| --- | --- |
| `ClusterSkeleton.lean` | exactly **three added `import` lines** (`ClusterSkeleton.SkewSeedRecovery`, `ClusterSkeleton.SkewSeedSkeleton`, `ClusterSkeleton.Examples.NonSkewSkeleton`); nothing else, no removal |
| `ClusterSkeleton/NodeCoordinates.lean` | **docstring only**: +6 lines in the module docstring and a rewritten docstring of `exchangeCharacter_eq_zpow_product` (the final statement review's DEFECT D1 fix) |
| `ClusterSkeleton/ZeroSet.lean` | **docstring only**: rewritten docstring of `Seed.Point.outgoing_ne_zero` (DEFECT D2) |
| `ClusterSkeleton/CapIndependence.lean` | **docstring only**: rewritten docstring of `coordinateCap_outgoing_not_interior` (DEFECT D2) |
| `verification/AxiomAudit.lean` | +25 lines: 7 module names, 14 `#print axioms` roots, 2 comment lines |
| `verification/FullSkeletonConsumer.lean` | +108 lines, −0: 2 imports, the `NonSkewConsumer` and `RecoveryConsumer` sections |

The docstring-only claim for the three modified library modules was **verified
mechanically**, not read off the diff: with block comments (`/- … -/`,
iteratively) and line comments stripped and whitespace normalized, the remaining
code of each file at F is **character-for-character identical** to `114d639`
(4390 / 2235 / 3524 characters respectively, equal on both sides). So **no
statement, no declaration name and no proof token changed**; the three renamings
that the docstrings discuss (`outgoing_ne_zero`,
`coordinateCap_outgoing_not_interior`) were deliberately *not* performed, and the
docstrings say so.

Byte-identical to `114d639` (unchanged blob OIDs): every other
`ClusterSkeleton/**` file including `FullSkeleton.lean`, `GeometryTarget.lean`,
`Seed.lean`, `SkewSeed.lean`, `Examples/NonSkew.lean`; all of
`verification/` except the two files above (so `accepted-library.json`,
`publication-check.json`, `statement-review.md`, `README.md`, the committed logs
are untouched); all of `scripts/`; `README.md`; both PDFs; `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain`. No file was deleted or renamed.

**Verdict item 6: PASS — the change is strictly additive** (new modules, three
root imports, docstring-only edits, additive consumer and audit), so nothing the
final statement review certifies at `114d639` is disturbed.

---

## 7. Appendix — replacement paragraphs for `verification/statement-review.md`

To be installed by the verification/receipts mission, which owns
`verification/`. The path is `verification/statement-review.md`; there is no
`docs/statement-review.md`. These two blocks are written to sit **next to** the
final statement review's Appendix B text (`24b7bef8…`), extending its "Outcome"
list and its "Exact boundary" section; they replace that appendix's single
`D = I` bullet, which they subsume.

```markdown
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
```

And for the "Exact boundary" section:

```markdown
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
```

---

## Method and limitations

* Every type quoted here was elaborated at F with `lake env lean` on a scratch
  file at the repository root (`#check @…`, `#print …`, `#print axioms …`, and
  `example … := rfl` / `:= <term>` delta-unfolding checks, 0 errors, 0
  warnings); the scratch files were deleted before committing and `git status`
  is clean at the published commit.
* Comparisons with `e62c101` and `114d639` were made on the git objects in this
  checkout (`git show`, `git diff`, `git ls-tree` blob OIDs), not from any
  handoff.
* This review does not re-prove the weighted library, does not re-review the
  universal theorem (assignment `776a49f6-…`, `docs/reviews/final-statement-review.md`
  at `24b7bef8…`), and makes no claim about the PDFs beyond the clause map it
  quotes from that review.
* Output scope respected: the single new file `docs/reviews/recovery-nonskew-review.md`
  on branch `weighted/recovery-review` based on F. No Lean, `verification/`,
  `README.md`, `scripts/` or manifest file was added or modified.
