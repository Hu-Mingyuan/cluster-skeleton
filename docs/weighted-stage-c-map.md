# Stage-C migration map: every `S.B`, `⁻¹`, `.det` and `S.skew` site of the dynamics chain

> Scope. This is a **migration plan**, not a verified claim about the weighted
> library. It classifies every site of the `D = I` baseline dynamics modules by
> the role its matrix plays, names the `ClusterSkeleton.SeedAlgebra` lemma that
> replaces it, and records the expected weighted shape of the equations derived
> from `tex/proof-blueprint.tex`. Nothing in the stage-B/C modules is edited
> here. Expectations that depend on stage B2's sign convention are marked
> **[B2]** and must be confirmed against B2's handoff before they are relied on.

Inputs.

* Baseline modules and line numbers: the working tree of this branch, which
  agrees with `e62c10176919227d13a901b383cd2c2ef13e72f7` on every module listed
  below (stage A touched only `ClusterSkeleton.lean`, `CapAngularTangency`,
  `CapIndependence`, `CapStrata`, `Examples/A2`, `GeometryTarget`,
  `IndependentNodeChart`, `NodeCoordinates`, `Seed`, `ZeroSet`).
* Weighted seed: `ClusterSkeleton/Seed.lean` at stage A commit
  `de58cd2c5a12942c6571c816d922ffd0bb837ac8`.
* New algebra: `ClusterSkeleton/SeedAlgebra.lean` (this branch), specializing
  `ClusterSkeleton/SymmetrizerAlgebra.lean` from
  `933961f18e11187aad53dd721d7fc93c5e60ee57`.
* Reference: `docs/tex/proof-blueprint.tex`, section *Skeleton in the acyclic
  case*, equations `eq:acyclic-ltor-split`, `eq:acyclic-H-near`,
  `eq:acyclic-flow`, `eq:acyclic-angle-flow`, `eq:acyclic-radial`.
* Baseline convention audit: `docs/skeleton-audit.md` §1.2–1.8.

The inventory can be regenerated with

```
grep -n 'S\.B\|⁻¹\|\.det\|S\.skew' ClusterSkeleton/<module>.lean
```

Counts (occurrences of the pattern, not distinct lines):

| module | `S.B` | `⁻¹` | `.det` | `S.skew` |
| --- | --- | --- | --- | --- |
| `TorusLiouvilleDynamics` | 52 | 19 | 7 (5 lines) | 0 |
| `GlobalLiouvilleField` | 2 | 1 | 0 | 0 |
| `InteriorPartnerPropagation` | 32 | 3 | 0 | 2 |
| `LocalAngularDynamics` | 10 | 2 | 4 (3 lines) | 1 |
| `AllStrataGrowth` | 4 | 1 | 4 (3 lines) | 0 |
| `BoundaryTangency` | 9 | 1 | 0 | 1 |
| `CompactInteriorRigidity` | 9 | 0 | 0 | 2 |
| `NativeRadialOrbit` | 2 | 0 | 0 | 0 |
| `FiniteTimeConfinement` | 2 | 0 | 0 | 0 |
| `ZeroStratumEscape` / `ZeroStratumInvariance` / `ZeroStratumPartnerDynamics` | 0 | 0 | 0 | 0 |
| `ConstructedFlowCapInclusion` / `ConstructedFlowReverseInclusion` / `FullSkeleton` | 0 | 0 | 0 | 0 |

The mission statement quotes "5 `.det`" for `TorusLiouvilleDynamics`: that is the
number of *lines* carrying a determinant (423–426 and 739–744); the raw pattern
count is 7 because two lines mention two determinants.

---

## 0. The conventions this map rests on

### 0.1 What `S.B`, `S.E`, `S.K` mean after stage A

| object | weighted definition | baseline (`D = I`) reading |
| --- | --- | --- |
| `S.E i j` | integral exchange matrix, **not** skew | `B_old i j` |
| `S.B i j` | `S.Eᵀ i j = S.E j i`, the **column exponent** of the monomials | `B_old j i = -B_old i j` |
| `S.K i j` | `(S.E i j : ℚ) * S.D j`, skew-symmetric | `B_old i j` |
| `S.D i` | positive rational weight `d_i` | `1` |

The single scalar identity that drives the whole migration is
`SeedAlgebra.K_eq_neg_D_mul_B`:

```
(S.K i j : ℝ) = -(S.D i : ℝ) * (S.B i j : ℝ)          (K_{ij} = -d_i B_{ij})
(S.K j i : ℝ) =  (S.D i : ℝ) * (S.B i j : ℝ)          (K_transpose_eq_D_mul_B)
```

So at `D = I` the two matrices differ **by a sign**: `K = -B_new = B_old`. That
is exactly the convention `SkewSeed.toSeed` was built to preserve
(`SkewSeed.toSeed_K : (S.toSeed).K i j = (S.B i j : ℚ)`); it is also why a
baseline occurrence of `S.B` cannot be migrated by a single global rule — the
role decides whether it becomes `S.K`, stays `S.B`, or stays `S.B` with a weight.

### 0.2 Consequences for the logarithmic dictionary

With `u_j = log‖z_j‖`, `θ_j = arg z_j`, `c_i(x) = ∑_j E_{ji} x_j = ∑_j (S.B i j) x_j`:

| quantity | baseline (`skeleton-audit.md` §1.3–1.4) | after stage A |
| --- | --- | --- |
| `exchangeCharacter p i = ∏ j, p.a j ^ S.B i j` | `t_i⁻¹` | `t_i` (`= z^{c_i}`) |
| `TorusCorrection.rowLog p i = ∑ j, (S.B i j) * A p j` | `-v_i` | `+v_i = c_i(u)` |
| `arg (exchangeCharacter p i)` | `-η_i` | `+η_i` |
| `PrimitiveLocalization.angle p i = arg (-exchangeCharacter p i)` | `-(η_i - π)` | `+(η_i - π)` |
| `PrimitiveLocalization.nodeLog p i` | `-Log(-t_i)` | `+Log(-t_i)` |

**Every one of these five sign flips is a consequence of `S.B_new = S.B_oldᵀ`,
and none of them changes a Lean source line**: the definitions are written with
`S.B` and keep their text. What changes is their *reference meaning*, and hence
the sign bookkeeping of `H` and of the primitive — see §4 **[B2]**.

Two cutoffs absorb the remaining difference, exactly as in the baseline:
`PrimitiveCutoffs.rho` is even (so `rho (rowLog …) = ρ(v_i)` either way) and
`deriv (PrimitiveCutoffs.vartheta δ)` is even (so
`deriv (vartheta δ) (arg (-exchangeCharacter p i)) = β'(η_i)` either way).
`PrimitiveCutoffs.vartheta δ` itself is **odd**, which is where the sign of `H`
is decided.

### 0.3 Role legend

| role | meaning | replacement |
| --- | --- | --- |
| **(a)** exponent | `S.B i j` is the exponent of `z_j` in `P_i^±`, or a `.toNat` exponent | stays `S.B i j = S.E j i`; keep one orientation per proof site |
| **(b)** adjacency / sign | only `S.B i j = 0`, `≠ 0`, or the diagonal is used | stays `S.B`; replace `S.skew` by `Seed.B_eq_zero_iff` / `Seed.B_diag_zero` |
| **(c)** form coefficient | `S.B i j` is the coefficient of the logarithmic two-form or of `λ_tor` | becomes `(S.K i j : ℝ)` / `SeedAlgebra.Kreal S` |
| **(d)** character / log | `rowLog = ∑ j, B i j * log‖a j‖`, i.e. `v_i`, or `∑ j, B i j * (…).im`, i.e. `η_i` | stays `S.B`; it *is* `c_i` |
| **(e)** inverse in dynamics | a matrix inverse solving the flow equations | `(SeedAlgebra.Kreal S)⁻¹` with `c_inv_K` / `Breal_mulVec_inv_K`, or the `B`-system via `Kreal_mulVec_eq_iff` |
| **(f)** integer inverse | `det B = 1` used only to cancel an integer matrix | unchanged: `SeedAlgebra.det_Breal`, `isUnit_det_Breal`, `Breal_vecMul_injective`, `exists_inverse_bound_Breal` |
| **(g)** weight in `H` | a summand of `H` carries `d_i`; the factors cancel in the radial equation | multiply the summand by `(S.D i : ℝ)` |
| **(h)** scalar inverse | `⁻¹` of a complex/real scalar (`b⁻¹`, `(p.a j)⁻¹`, `(-exchangeCharacter p i)⁻¹`) | **not a matrix inverse**; unchanged |

---

## 1. Expected weighted statement shapes

All of this is derived from the blueprint; the Lean sign conventions are fixed by
`TorusPrimitive.alpha` and `TorusCorrection.H`, which stage B2 owns.

### 1.1 The two contraction equations

`Im Ω = ∑_{k,l} K_{kl} du_k ∧ dθ_l` and `λ_tor = u^T K dθ`, so
`ι_Z Im Ω = λ_tor + dH` splits into (blueprint, before `eq:acyclic-flow`)

```
K^T u̇ = K^T u + ∂_θ H ,        -K θ̇ = ∂_u H .
```

Writing `a_i := h(u_i) χ_i ρ(v_i) β'(η_i)` and using `d_i c_i = K e_i`
(`SeedAlgebra.K_mulVec_single`),

```
∂_θ H = ∑_{i∈M} d_i a_i c_i = K a ,   i.e.   (∂_θ H)_j = ∑_i K_{ji} a_i = ∑_i d_i a_i (S.B i j) .
```

Since `K^T = -K` (`SeedAlgebra.Kreal_transpose`), `K^T(u̇ - u) = K a = -K^T a`,
and cancelling `K^T` (`SeedAlgebra.Kreal_vecMul_injective`, which needs only
`isUnit_det_Kreal`, **not** a determinant equal to `1`) gives `u̇ = u - a`:
**the weights cancel from the radial equation**, as the roadmap states.

### 1.2 `TorusLiouvilleDynamics.omega_real` (lines 115–130) — role (c)

```
evalTwo (omega S hdet) p v w
  = (∑ i, ∑ j, (S.K i j : ℝ) * (…v…/p.a i).re * (…w…/p.a j).im)
  - (∑ i, ∑ j, (S.K i j : ℝ) * (…w…/p.a i).re * (…v…/p.a j).im)
```

i.e. the baseline statement with `S.B` replaced by `S.K` in both sums. The
antisymmetry step that the baseline got from `S.skew` is
`SeedAlgebra.sum_sum_K_antisymm`; `Kreal_transpose` is the matrix form.

### 1.3 `radial_matrix_equation` (lines 402–416) — roles (c), (g)

Contracting §1.1 against the angular tangent at index `j`:

```
∑ i, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p i).re
  = ∑ i, (S.K i j : ℝ) * TorusCorrection.A S p i
  - ∑ i ∈ S.mutable, amplitude S ε κ i (TorusCorrection.A S p)
      * deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i))
      * (S.K i j : ℝ)
```

**Shape = the baseline statement with `S.B ↦ S.K` at all three occurrences.**
The `d_i` of the `H` summand (role (g)) is absorbed by
`d_i a_i (S.B i j) = -a_i (S.K i j)` (`K_eq_neg_D_mul_B`), which is why no weight
survives in the displayed statement. The sign of the last term is **[B2]**-dependent
(§4).

### 1.4 `real_logarithmicComponents` (lines 418–437) — role (e)/(c), *not* (f)

Statement **unchanged**:

```
(logarithmicComponents S hdet ε κ δ p i).re
  = TorusCorrection.A S p i - radialCorrection S ε κ δ p i
```

Proof change: the baseline builds `R : Matrix … := fun i j => (S.B i j : ℝ)`,
proves `R.det = 1`, and cancels with `Matrix.vecMul_injective_of_isUnit`. The
weighted proof uses `SeedAlgebra.Kreal S` and
`SeedAlgebra.Kreal_vecMul_injective S hdet`. There is **no** `det = 1` for `K`:
`SeedAlgebra.det_Kreal_of_unimodular` gives `det K = ∏ d_i`, and
`isUnit_det_Kreal` is the fact to use.

### 1.5 `mutable_radial_equation` (439–447), `frozen_radial_equation` (449–453) — unchanged

```
(logarithmicComponents … p i).re = TorusCorrection.A S p i
  - PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i)
    * DominanceCutoff.dominance S ε i (TorusCorrection.A S p)
    * PrimitiveCutoffs.rho (TorusCorrection.rowLog S p i)
    * deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i))
```

**Verbatim the baseline statement**, including the minus sign: the weights
cancel (§1.1), `rowLog` is now `+v_i` but `rho` is even, and
`deriv (vartheta δ)` is even. This is blueprint `eq:acyclic-flow` line 2 and
`eq:acyclic-radial`. Sign **[B2]**-dependent only through §4.

### 1.6 `angular_equation` (132–143) and its logarithmic forms (668–689) — role (c)

```
∑ j, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im
  = ± differentialCovector … (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i)
```

from `-K θ̇ = ∂_u H`. The `B`-form, which is the one the blueprint's
`eq:acyclic-angle-flow` uses, follows by `SeedAlgebra.sum_K_row`:

```
∑ j, (S.K i j : ℝ) * θ̇ j = -(S.D i : ℝ) * ∑ j, (S.B i j : ℝ) * θ̇ j = -(S.D i : ℝ) * η̇ i
```

so `η̇_i = (1/d_i) ∂_{u_i} H` — the weight appears **here**, not in the radial
equation. Equivalently, `SeedAlgebra.Kreal_mulVec_eq_iff` converts the `K`-system
into the `B`-system:

```
(Kreal S).mulVec θ̇ = ∂_u H   ↔   (Breal S).mulVec θ̇ = fun i => -(∂_u H) i / (S.D i : ℝ)
```

The `±` is **[B2]**-dependent (§4).

### 1.7 `v̇_i`: the row form — role (d), no inverse

Blueprint `eq:acyclic-angle-flow` second half,
`v̇_i = v_i - ∑_{k∈M} B_{ki} a_k`, is in our convention

```
∑ k, (S.B i k : ℝ) * (logarithmicComponents … p k).re
  = ∑ k, (S.B i k : ℝ) * TorusCorrection.A S p k
  - ∑ k ∈ S.mutable, (S.B i k : ℝ) * amplitude S ε κ k (…) * deriv (vartheta δ) (…)
```

i.e. `rowLog` of the radial components. It is a corollary of §1.5 by summation
and needs **no** matrix algebra; it stays written with `S.B` (role (d)). Note the
index orientation: §1.3 pairs over the *first* index (the two-form), §1.7 over
the *second* (the character `c_i`). Keeping these apart is the main bookkeeping
hazard of the migration.

### 1.8 `full_matrix_inverse_bound` (734–770) — role (e), with (f) still available

Baseline statement:

```
∃ C, 0 ≤ C ∧ ∀ y b, (∀ i, ∑ j, (S.B i j : ℝ) * y j = b i) → ∑ j, |y j| ≤ C * ∑ j, |b j|
```

Both consumers (`imaginary_components_growth`, line 960, and
`AllStrataGrowth.nu_center_growth`, line 163) feed it with the **angular**
equation, whose left-hand side becomes the `K`-pairing (§1.6). So the weighted
chain should use

* `SeedAlgebra.exists_inverse_bound_Kreal S hdet` — same statement with `S.K`;
* and keep `SeedAlgebra.exists_inverse_bound_Breal S hdet` (role (f), proved from
  `det_Breal`) for any site that really solves a `B`-system.

Both are already proved in `SeedAlgebra`; the baseline's local
`R`/`hd`/`hu`/`R⁻¹`/`hentry`/calc block (lines 738–770) is deleted and replaced
by one `obtain`.

### 1.9 `LocalAngularDynamics.nu` (112–114) and `angularRhs` (102–109) — roles (e), (g)

`nu` inverts the **full** real matrix, frozen rows and columns included. Weighted
form:

```
def nu (ε κ δ : ℝ) (p q : S.Point) : Fin d → ℝ :=
  (SeedAlgebra.Kreal S)⁻¹.mulVec (angularRhs S ε κ δ p q)
```

* `nu_eq_torus` (lines 222–239): replace `R`, `hd : R.det = 1`,
  `hu : IsUnit R.det` by `SeedAlgebra.isUnit_det_Kreal S hdet`, and the final
  `Matrix.nonsing_inv_mul` step by `SeedAlgebra.Kreal_inv_mulVec S hdet`.
* `AllStrataGrowth.full_matrix_nu_equation` (112–127) becomes
  `∑ k, (S.K j k : ℝ) * nu S ε κ δ p q k = angularRhs S ε κ δ p q j`, proved by
  `SeedAlgebra.Kreal_mulVec_inv S hdet`.
* `angularRhs` is `∂_{u_j} H` in masked form, so each summand gains its weight
  (role (g)):

  ```
  angularRhs S ε κ δ p q j = ∑ i : S.Mutable, (S.D i : ℝ) *
    (if (i : Fin d) ∈ p.zeroSet then (PrimitiveLocalization.nodeLog q i).im * (Pi.single j 1) i
     else if i ∈ RegularCorrection.surviving S p.zeroSet then
       TorusCorrection.angular S δ q i *
         fderiv ℝ (amplitude S ε κ i) (maskedLogs S p.zeroSet q) (Pi.single j 1)
     else 0)
  ```

  The zero-stratum branch is blueprint `eq:acyclic-H-near`:
  `∂_{u_i} H = d_i (η_i - π)` there, and `(nodeLog q i).im = +(η_i - π)` after
  stage A (§0.2).
* **Alternative** (if a worker prefers to keep an integer inverse): define
  `nu := (SeedAlgebra.Breal S)⁻¹.mulVec (fun i => -(angularRhs S ε κ δ p q i) / (S.D i : ℝ))`
  and use `SeedAlgebra.Kreal_mulVec_eq_iff` / `Breal_mulVec_inv_K` to connect the
  two. This keeps `det_Breal` (role (f)) but pushes `1/d_i` into every consumer;
  the `K` form above is recommended because `c_inv_K` is stated for it.

### 1.10 `c_i(K⁻¹ x) = -x_i/d_i`

This is the identity that makes `η̇_i = (1/d_i) ∂_{u_i} H` provable from
`θ̇ = -K⁻¹ ∂_u H` directly, without inverting anything by hand:

```
SeedAlgebra.c_inv_K            : ∑ j, (S.E j i : ℝ) * ((Kreal S)⁻¹.mulVec x) j = -(x i) / (S.D i : ℝ)
SeedAlgebra.Breal_mulVec_inv_K : (Breal S).mulVec ((Kreal S)⁻¹.mulVec x) = fun i => -(x i) / (S.D i : ℝ)
SeedAlgebra.vecMul_Ecol_inv_Kreal : vecMul (fun j => (S.E j i : ℝ)) (Kreal S)⁻¹ = -(S.D i : ℝ)⁻¹ • Pi.single i 1
```

Use `Breal_mulVec_inv_K` wherever the baseline wrote `∑ j, (S.B i j : ℝ) * nu … j`
after an inversion.

---

## 2. Per-module site inventory

Format: `line` — role — what to do. `decl` is the enclosing declaration.

### 2.1 `ClusterSkeleton/TorusLiouvilleDynamics.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 118 | `S.B` | `omega_real` | (c) | `(S.K i j : ℝ)`; see §1.2 |
| 121 | `S.B` | `omega_real` | (c) | `(S.K i j : ℝ)`; antisymmetry from `sum_sum_K_antisymm` |
| 134 | `S.B` | `angular_equation` | (c) | `(S.K i j : ℝ)`; §1.6 |
| 147, 148 | `⁻¹` | `hasFDerivAt_normalized_log` | (h) | scalar `b⁻¹`; unchanged |
| 160 | `⁻¹` | `hasFDerivAt_localAngle` | (h) | unchanged |
| 168 | `⁻¹` | `hasFDerivAt_vartheta_arg` | (h) | unchanged |
| 179 | `⁻¹` | `hasFDerivAt_log_norm` | (h) | unchanged |
| 200 | `⁻¹` | `differential_A` | (h) | `(p.a i)⁻¹`; unchanged |
| 205, 206 | `S.B` | `hasFDerivAt_character` | (a) | exponent of `∏ j, y j ^ S.B i j`; unchanged (`S.B i j = S.E j i`) |
| 207 | `S.B`, `⁻¹` | `hasFDerivAt_character` | (a), (h) | coefficient of `dlog`; this `S.B i j` is the exponent derivative, **stays** `S.B` |
| 212 | `S.B`, `⁻¹` | `hasFDerivAt_character` | (a), (h) | unchanged |
| 220 | `S.B` | `differential_character` | (a)/(d) | `dlog (exchangeCharacter_i) = ∑ j, (S.B i j) dlog a_j = dlog t_i`; stays `S.B` |
| 228 | `S.B` | `differential_character` | (a) | unchanged |
| 234 | `S.B` | `differential_character` | (a) | unchanged |
| 235 | `S.B`, `⁻¹` | `differential_character` | (a), (h) | unchanged |
| 249 | `S.B` | `differential_angular` | (d) | `∑ j, (S.B i j) * (…).im = η̇_i`; stays `S.B` |
| 262 | `⁻¹` | `differential_angular` | (h) | `(-exchangeCharacter p i)⁻¹`; unchanged |
| 271 | `S.B` | `amplitude` | (d) | `rho (∑ j, (S.B i j) * a j) = ρ(v_i)`; stays `S.B` (`rho` even) |
| 275 | `S.B` | `amplitude_smooth` | (d) | unchanged |
| 325 | `S.B` | `differential_H` | (d) | the `rho`-argument differential; stays `S.B` |
| 378 | `S.B` | `differential_H_angular` | (g) | `∂_{θ_j} H = ∑ i ∈ mutable, d_i · angular'_i · amplitude_i · (S.B i j)`; multiply by `(S.D i : ℝ)`, then convert to `-(S.K i j)` with `K_eq_neg_D_mul_B` |
| 404, 405, 408 | `S.B` | `radial_matrix_equation` | (c) | `(S.K i j : ℝ)`; §1.3 |
| 423 | `S.B` | `real_logarithmicComponents` | (e) | delete `R`; use `SeedAlgebra.Kreal S` |
| 424 | `.det` | `real_logarithmicComponents` | (e) | **no** `det = 1`; use `isUnit_det_Kreal` |
| 425, 426 | `S.B`, `.det` | `real_logarithmicComponents` | (e) | delete the `map_det` block; `Kreal_vecMul_injective S hdet` |
| 514 | `S.B` | `logarithmicHamiltonian` | (d) | the angle germ `arg(-χ_i) + ∑ j, (S.B i j) * (z j).im`; stays `S.B` |
| 520, 524, 526, 529, 530 | `S.B` | `angular_logarithmic_identity` | (a)/(d) | `∏ (q.a j/p.a j)^(S.B i j)` and its argument; stays `S.B` |
| 624, 630 | `S.B` | `fderiv_logarithmicHamiltonian` | (d) | stays `S.B` |
| 670 | `S.B` | `angular_equation_logarithmic` | (c) | `(S.K i j : ℝ)`; §1.6 |
| 680 | `S.B` | `angular_equation_partial_deriv` | (c) | `(S.K i j : ℝ)`; §1.6 |
| 695, 696 | `S.B` | `amplitude_abs_le` | (d) | `rho`-argument; stays `S.B` |
| 736 | `S.B` | `full_matrix_inverse_bound` | (e) | restate with `S.K`, or delete and use `SeedAlgebra.exists_inverse_bound_Kreal`; §1.8 |
| 738–744 | `S.B`, `.det` | `full_matrix_inverse_bound` | (e)/(f) | delete; `exists_inverse_bound_Kreal` / `exists_inverse_bound_Breal` |
| 745, 749, 752, 753, 755, 757, 758, 762, 763 | `⁻¹` | `full_matrix_inverse_bound` | (e) | delete; the one-norm calc now lives in `SeedAlgebra.exists_inverse_bound_of_isUnit` |
| 863, 865, 866, 868 | `S.B` | `fderiv_amplitude_apply` | (d) | `rho`-argument and its row covector; stays `S.B` |
| 896, 898, 899, 901 | `S.B` | `amplitude_partial_bound` | (d) | the entrywise bound `∑ i ∑ j |S.B i j|`; stays `S.B` (it bounds `c`, not the form) |
| 913, 914, 930, 931, 938, 939 | `S.B` | `amplitude_partial_bound` | (d) | stays `S.B`; line 938–939 is the `Pi.single` row evaluation |

Lines 423–426 and 738–744 are the only two genuine matrix sites in this module;
everything else is exponent/character bookkeeping or a scalar inverse.

### 2.2 `ClusterSkeleton/GlobalLiouvilleField.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 99 | `⁻¹` | `differential_A` | (h) | `(p.a j)⁻¹`; unchanged |
| 114 | `S.B` | `mutable_radial_equation` | (d) | `rho (∑ j, (S.B i j) * A S p j)`; stays `S.B`; §1.5 |
| 131 | `S.B` | `angular_equation_partial_deriv` | (c) | `(S.K i j : ℝ)`; this is the glued form of §1.6 |

The remaining content of this module (`Z`, `logarithmicComponents`,
`L_eq_logarithmicComponents`, the glued radial equations) is matrix-free and
transports once `TorusLiouvilleDynamics` is migrated.

### 2.3 `ClusterSkeleton/InteriorPartnerPropagation.lean`

All 32 `S.B` sites are role **(a)** or **(b)** and keep `S.B`; the three `⁻¹` are
role **(h)**. The two `S.skew` uses are the ones that must change.

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 23 | `S.B` | `initial_neighbor_unit` | (b) | `S.B i j ≠ 0` hypothesis; unchanged |
| 60 | `S.B` | `neighbors_unit_forward` | (b) | unchanged |
| 66, 69 | `S.B` | `negativeMonomial_ne_zero` | (a)/(b) | unchanged |
| 76 | `S.B` | `partners_zero_of_character` | (b) | unchanged |
| 98, 99, 100 | `S.B` | `hasFDerivAt_character_row` | (a) | exponent; unchanged |
| 101 | `S.B`, `⁻¹` | `hasFDerivAt_character_row` | (a), (h) | unchanged |
| 105 | `S.B` | `hasFDerivAt_character_row` | (b) | unchanged |
| 112 | `⁻¹` | `hasFDerivAt_character_row` | (h) | unchanged |
| 113 | `S.B` | `hasFDerivAt_character_row` | (a) | unchanged |
| 122, 132 | `S.B` | `mdifferentiableAt_character_row` | (a) | unchanged |
| 139, 143, 151, 157 | `S.B` | `differential_character_row` | (a)/(d) | unchanged |
| 158 | `S.B`, `⁻¹` | `differential_character_row` | (a), (h) | unchanged |
| 168 | `S.B` | `angularRhs_eq_self_of_unit_neighbors` | (b) | unchanged |
| **182** | `S.B`, `S.skew` | `angularRhs_eq_self_of_unit_neighbors` | (b) | `have hh := S.skew i i; omega` → `Seed.B_diag_zero S i` (it is `@[simp]`, so `simp` closes it too) |
| 196, 200 | `S.B` | `angularRhs_eq_self_of_unit_neighbors` | (b) | unchanged |
| **203** | `S.skew` | `angularRhs_eq_self_of_unit_neighbors` | (b) | goal `S.B j i = 0` from `he : S.B i j = 0`: `exact (Seed.B_eq_zero_iff S i j).mp he` |
| 213, 219, 223, 229 | `S.B` | `differential_character_of_unit_neighbors` | (b) | unchanged |
| 236, 240, 243, 248, 252 | `S.B` | `differential_character_of_unit_neighbors` | (d) | `∑ j, (S.B i j) * nu … j = η̇_i`; stays `S.B`, but the value of `nu` changes (§1.9) |
| 419 | `S.B` | `shifted_character_hasDerivAt` | (b) | unchanged |

### 2.4 `ClusterSkeleton/LocalAngularDynamics.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 38, 57, 58, 61 | `S.B` | `amplitude_fderiv_congr` | (b)/(d) | `rho`-argument congruence; unchanged |
| **113** | `S.B`, `⁻¹` | `nu` | (e) | `(SeedAlgebra.Kreal S)⁻¹`; §1.9 (or the `Breal`+`1/d_i` alternative) |
| 212, 213 | `S.B` | `angularRhs_eq_radial` | (b) | unchanged |
| **217** | `S.skew` | `angularRhs_eq_radial` | (b) | goal `S.B i k = 0` from `he : S.B k i = 0`: `exact (Seed.B_eq_zero_iff S k i).mp he` |
| 225 | `S.B` | `nu_eq_torus` | (e) | delete `R`; `SeedAlgebra.Kreal S` |
| 226, 228, 231 | `.det` | `nu_eq_torus` | (e) | `isUnit_det_Kreal S hdet`; there is no `det = 1` |
| 227 | `S.B` | `nu_eq_torus` | (e) | delete the `map_det` block |
| 238 | `⁻¹` | `nu_eq_torus` | (e) | `SeedAlgebra.Kreal_inv_mulVec S hdet` |

Also in this module (no pattern match, but affected): `angularRhs` (102–109)
gains the `(S.D i : ℝ)` factor of role (g) — §1.9.

### 2.5 `ClusterSkeleton/AllStrataGrowth.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 114 | `S.B` | `full_matrix_nu_equation` | (e)/(c) | `∑ k, (S.K j k : ℝ) * nu … k = angularRhs … j` |
| 116 | `S.B` | `full_matrix_nu_equation` | (e) | delete `M`; `SeedAlgebra.Kreal S` |
| 117, 119, 122 | `.det` | `full_matrix_nu_equation` | (e) | `isUnit_det_Kreal S hdet` |
| 118 | `S.B` | `full_matrix_nu_equation` | (e) | delete the `map_det` block |
| 124 | `⁻¹` | `full_matrix_nu_equation` | (e) | `SeedAlgebra.Kreal_mulVec_inv S hdet` |

`nu_center_growth` (line 163) consumes `full_matrix_inverse_bound`; switch it to
`SeedAlgebra.exists_inverse_bound_Kreal S hdet` (§1.8).

### 2.6 `ClusterSkeleton/BoundaryTangency.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 179 | `S.B` | `deep_radius_torus` | (d) | `rho`-argument; unchanged |
| 208 | `S.B` | `differential_nodeLog_torus` | (a)/(d) | `dlog t_i`; unchanged |
| 225 | `⁻¹` | `differential_nodeLog_torus` | (h) | `(-exchangeCharacter q i)⁻¹`; unchanged |
| 235, 243 | `S.B` | `row_real_drift_torus` | (d)/(b) | the row drift `∑ j, (S.B i j) * …`; unchanged |
| 258 | `S.B` | `amplitude_partial_nonadjacent` | (b) | `S.B j i = 0` hypothesis; unchanged |
| 329 | `S.B` | `amplitude_partial_adjacent` | (b) | unchanged |
| 370 | `S.B` | `local_H_radial` | (b) | unchanged |
| **371** | `S.B`, `S.skew` | `local_H_radial` | (b) | goal `S.B j i = 0` from `hij : S.B i j = 0`: `exact (Seed.B_eq_zero_iff S i j).mp hij` |
| 387 | `S.B` | `nodeLog_drift_torus` | (d) | unchanged |

`local_H_radial` also carries role (g): the local `H` germ near `{z_i = 0}` is
`d_i (u_i + a)(η_i - π) + H'` (`eq:acyclic-H-near`), so its radial derivative
gains `(S.D i : ℝ)`.

### 2.7 `ClusterSkeleton/CompactInteriorRigidity.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 122 | `S.B` | `row_single` | (d) | `∑ j, (S.B i j) * Pi.single i a j = 0`; unchanged |
| **124** | `S.B`, `S.skew` | `row_single` | (b) | `Seed.B_diag_zero S i` |
| **138** | `S.B`, `S.skew` | `amplitude_single_deep` | (b) | `Seed.B_diag_zero S i` |
| 236 | `S.B` | `interior_matrix_eq_zero` | (b) | `S.B i j = 0` conclusion; unchanged |
| 242 | `S.B` | `initial_neighbor_unit` | (b) | unchanged |
| 249 | `S.B` | `neighbors_unit_forward` | (b) | unchanged |
| 268 | `S.B` | `shifted_character_hasDerivAt` | (b) | unchanged |
| 284, 290 | `S.B` | `negativeMonomial_norm_eq_one` | (a)/(b) | unchanged |

### 2.8 `ClusterSkeleton/NativeRadialOrbit.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 29, 30 | `S.B` | `amplitude_abs_le_radial` | (d) | `rho`-argument bounds; unchanged |

The radial orbit statements themselves rest on §1.5, which is unchanged.

### 2.9 `ClusterSkeleton/FiniteTimeConfinement.lean`

| line | pattern | decl | role | action |
| --- | --- | --- | --- | --- |
| 253, 254 | `S.B` | `monomials_uniformly_bounded` | (a) | `A ^ (S.B i j).toNat`, `A ^ (-S.B i j).toNat`: the literal monomial exponents; unchanged |

### 2.10 `ZeroStratumEscape`, `ZeroStratumInvariance`, `ZeroStratumPartnerDynamics`

**No `S.B`, `⁻¹`, `.det` or `S.skew` site.** These modules only consume
`GlobalLiouvilleField.Z`, `BoundaryTangency.deep_radius`,
`NormalizedPartnerNormDrift.*`, `PrimitiveLocalization.nodeLog` and
`ZeroSet`/`RegularCorrection` lemmas. They migrate with **no edit** provided:

* the divisor rate stays `Z|z_i|² = -2κ|z_i|²` — blueprint
  `eq:acyclic-divisor-flow` gives `u̇_i = -a` there, with no `d_i`, because the
  weights already cancelled in §1.1;
* the partner rate stays `Z|y_i|² = 2(1+κ)|y_i|²` — `eq:acyclic-partner-flow`,
  likewise weight-free;
* `(nodeLog q i).im = +(η_i - π)` (§0.2) does not change the *statement* of
  `coordinate_zero_iff` or `normSq_eq_exp_mul`, but it does change the sign
  bookkeeping inside `BoundaryTangency`/`NormalizedPartnerNormDrift` — see §4.

### 2.11 `ConstructedFlowCapInclusion`, `ConstructedFlowReverseInclusion`, `FullSkeleton`

**No `S.B`, `⁻¹`, `.det` or `S.skew` site.** They are pure inclusion/assembly
arguments over `NativeCompleteFlow.completeFlow`, `coordinateCap`,
`lambdaStratum` and `Seed.Independent`. They migrate unchanged, with two caveats
that are *not* sites in these files:

* `Seed.Independent` is stated with `S.E i j = 0` (stage A) and is equivalent to
  the exponent form by `Seed.Independent.exponent_eq_zero`; `FullSkeleton`'s
  `⋃ I : {I // S.Independent I}` therefore needs no change.
* `FullSkeleton.liouvilleData`/`torus_anchor` reference
  `GlobalPrimitive.alpha` and the two-form, both of which become `S.K`-based in
  stage B2; the *statement* of `trappedSet_eq_coordinateCap` and
  `trappedSet_eq_iUnion_lambdaStratum` is unaffected.

---

## 3. Role index (which lines carry which role)

A line can carry two roles (e.g. an exponent and a scalar inverse); it is listed
under each. `TLD` = `TorusLiouvilleDynamics`, `GLF` = `GlobalLiouvilleField`,
`IPP` = `InteriorPartnerPropagation`, `LAD` = `LocalAngularDynamics`,
`ASG` = `AllStrataGrowth`, `BT` = `BoundaryTangency`,
`CIR` = `CompactInteriorRigidity`, `NRO` = `NativeRadialOrbit`,
`FTC` = `FiniteTimeConfinement`.

| role | lines |
| --- | --- |
| **(a)** exponent → stays `S.B i j = S.E j i` | TLD 205, 206, 207, 212, 220, 228, 234, 235, 520, 524, 526, 529, 530; IPP 66, 98, 99, 100, 101, 113, 122, 132, 139, 143, 151, 157, 158; FTC 253, 254 |
| **(b)** adjacency/sign → `Seed.B_eq_zero_iff` / `Seed.B_diag_zero` | IPP 23, 60, 66, 69, 76, 105, 168, 182, 196, 200, 203, 213, 219, 223, 229, 243, 419; LAD 38, 61, 212, 213, 217; BT 243, 258, 329, 370, 371; CIR 124, 138, 236, 242, 249, 268, 284, 290 |
| **(c)** form coefficient → `S.K` | TLD 118, 121, 134, 404, 405, 408, 670, 680; GLF 131; ASG 114 |
| **(d)** character / log (`rowLog`, `rho`-argument, `nu`-pairing) → stays `S.B` | TLD 220, 249, 271, 275, 325, 514, 520, 524, 526, 529, 530, 624, 630, 695, 696, 863, 865, 866, 868, 896, 898, 899, 901, 913, 914, 930, 931, 938, 939; GLF 114; IPP 139, 143, 151, 157, 236, 240, 243, 248, 252; LAD 57, 58; BT 179, 208, 235, 387; CIR 122; NRO 29, 30 |
| **(e)** inverse in dynamics → `(Kreal S)⁻¹`, `isUnit_det_Kreal`, `Kreal_vecMul_injective`, or `Kreal_mulVec_eq_iff` | TLD 423, 424, 425, 426, 736, 738, 739, 740, 741, 744, 745, 749, 752, 753, 755, 757, 758, 762, 763; LAD 113, 225, 226, 227, 228, 231, 238; ASG 114, 116, 117, 118, 119, 122, 124 |
| **(f)** integer inverse → unchanged (`det_Breal`) | no site *requires* it after the migration; it stays available (`det_Breal`, `isUnit_det_Breal`, `Breal_vecMul_injective`, `exists_inverse_bound_Breal`) for the `Breal`-based alternative of §1.9 |
| **(g)** `H` summands carry `d_i`, cancelling in the radial equation | TLD 378 (`differential_H_angular`) and `differential_H_radial` (383–395, no pattern match); LAD `angularRhs` 102–109 (no pattern match); BT `local_H_radial` 354–375 (no pattern match) |
| **(h)** scalar inverse, not a matrix inverse → unchanged | TLD 147, 148, 160, 168, 179, 200, 207, 212, 235, 262; GLF 99; IPP 101, 112, 158; BT 225 |
| `S.skew` — **must change** (the field does not exist in stage A's `Seed`) | IPP 182, 203; LAD 217; BT 371; CIR 124, 138 |

The six `S.skew` sites are the only ones that **cannot elaborate at all** against
stage A's `Seed`; every other site elaborates but may mean the wrong thing until
it is reclassified. The role-(c) and role-(e) lines are the complete list of
sites where the *mathematics* changes; everything else is renaming or
bookkeeping.

---

## 4. **[B2]** What depends on stage B2's sign convention

Stage B2 owns `TorusPrimitive.beta`, `TorusPrimitive.alpha`,
`TorusCorrection.H` and `TorusCorrection.angular`. The baseline situation
(`docs/skeleton-audit.md` §1.2–1.6) was:

```
beta  = ∑ i ∑ j (S.B i j) * log‖a_i‖ • angleCovector j       (= u^T K dθ, since K_old = B_old)
alpha = beta - d H                                           (TorusPrimitive.alpha)
rowLog = -v_i ,  angle = -(η_i - π) ,  nodeLog = -Log(-t_i)
H_Lean = -H_reference      (rho even, vartheta odd)
⟹ alpha = λ_tor + dH_reference = λ_ac                        ✔
```

After stage A the three inner sign flips **disappear** (§0.2): `rowLog = +v_i`,
`angle = +(η_i - π)`, `nodeLog = +Log(-t_i)`. Since
`PrimitiveCutoffs.vartheta δ` is odd, that means

```
H_Lean = + H_reference        (with `angular = vartheta δ (arg (-exchangeCharacter p i))` unchanged)
```

and therefore `alpha = beta - dH` would give `λ_tor - dH_reference`, **not**
`λ_ac`. One of two corrections is needed, and B2 decides which:

| B2 option | `angular` | `alpha` | `H_Lean` | consequence for stage C |
| --- | --- | --- | --- | --- |
| **O1 (expected)** | unchanged | `beta + d H` | `+H_ref` | `radial_matrix_equation` keeps its baseline minus sign (§1.3); `angular_equation` acquires a **minus**: `∑ j, (S.K i j) * (…).im = -∂_{u_i} H` |
| **O2** | negated (`-vartheta δ (arg (-exchangeCharacter p i))`) | `beta - d H` (unchanged) | `-H_ref` | both `radial_matrix_equation` and `angular_equation` keep their baseline shapes verbatim, but every `H`-valued statement in `BoundaryTangency`, `PrimitiveLocalization` and `AllStrataGrowth` changes sign |

In addition, B2 must make `beta` the blueprint's `λ_tor = u^T K dθ`, i.e. replace
its `S.B` coefficient by `S.K`; otherwise `d beta ≠ Im Ω` and §1.2 fails.

Items whose **sign** the stage-C worker must confirm against B2's handoff, and
must not assume:

1. the sign of the correction term in `radial_matrix_equation` (§1.3) and hence
   in `radialCorrection`;
2. the sign in `angular_equation` / `angular_equation_logarithmic` /
   `angular_equation_partial_deriv` and in `GlobalLiouvilleField.angular_equation_partial_deriv` (§1.6);
3. the sign of `angularRhs`'s zero-stratum branch
   `(PrimitiveLocalization.nodeLog q i).im` (§1.9) and of
   `TorusCorrection.angular` throughout `BoundaryTangency.local_H_radial`;
4. whether `η̇_i = +(1/d_i) ∂_{u_i} H` or `-(1/d_i) ∂_{u_i} H` in the Lean
   statement (the blueprint value is `+`; the Lean sign follows O1/O2).

Items that are **sign-independent** and may be relied on now:

* `mutable_radial_equation` and `frozen_radial_equation` keep their baseline
  statements verbatim (§1.5) — `rho` and `deriv (vartheta δ)` are both even, and
  the weights cancel;
* every role-(a), (b), (d), (h) site above;
* the matrix facts: `Kreal_transpose`, `det_Kreal`, `isUnit_det_Kreal`,
  `det_Breal`, `sum_K_row`, `sum_K_col`, `K_mulVec_single`,
  `K_eq_neg_D_mul_B`, `sum_sum_K_antisymm`, `Kreal_mulVec_eq_iff`, `c_inv_K`,
  `Breal_mulVec_inv_K`, `exists_inverse_bound_Breal`,
  `exists_inverse_bound_Kreal`;
* the weight-free divisor and partner rates of §2.10.

---

## 5. Migration order suggested for stage C

1. `TorusLiouvilleDynamics.omega_real` → `S.K` (§1.2), with
   `sum_sum_K_antisymm`.
2. `differential_H_angular` / `differential_H_radial` → add `(S.D i : ℝ)`
   (role (g)) and convert with `K_eq_neg_D_mul_B`.
3. `radial_matrix_equation` → `S.K` (§1.3), then `real_logarithmicComponents`
   via `Kreal_vecMul_injective` (§1.4). `mutable_radial_equation` and
   `frozen_radial_equation` should then close **unchanged**.
4. `angular_equation` and its two logarithmic forms → `S.K` (§1.6); fix the sign
   against B2's handoff.
5. `full_matrix_inverse_bound` → delete, use `exists_inverse_bound_Kreal`
   (§1.8); repair `imaginary_components_growth` and
   `AllStrataGrowth.nu_center_growth`.
6. `LocalAngularDynamics.angularRhs` (lines 102–109, +`(S.D i : ℝ)`) and `nu`
   (`(Kreal S)⁻¹`), then `nu_eq_torus` and
   `AllStrataGrowth.full_matrix_nu_equation` (§1.9).
7. The six `S.skew` sites → `Seed.B_diag_zero` / `Seed.B_eq_zero_iff` (§3);
   these are mechanical and can be done first to get the files elaborating.
8. `GlobalLiouvilleField`, `BoundaryTangency`, `InteriorPartnerPropagation`,
   `CompactInteriorRigidity`, `NativeRadialOrbit`, `FiniteTimeConfinement`:
   role (a)/(b)/(d)/(h) only, plus the role-(g) germ in `local_H_radial`.
9. `ZeroStratum*`, `Constructed*`, `FullSkeleton`: expected to need no edit
   (§2.10, §2.11).
