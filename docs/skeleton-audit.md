# Audit of the supplied skeleton proof against the Lean construction

Scope: the **skew-symmetric unimodular** case with **mutable acyclicity** and
**variable frozen coordinates**, i.e. the specialization `D̃ = I`, `K = E = B` of
the supplied reference. Nothing below claims, implies, or proposes a weighted
(`D̃ ≠ I`) theorem; the weighted notation of the reference is retained there only
as notation.

**Summary.** The supplied proof has a Lean counterpart in
`ClusterSkeleton/*.lean` in the scope stated above. The stratified cap identity
is proved by `coordinateCap_eq_iUnion_lambdaStratum` and
`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`; the explicit chart rank is
proved by `IndependentNodeChart.complementRank_eq_sub_two_mul_card`.
The entries **G1** and **G2** below give the exact declarations. **G3** is an
optional determinant convention, outside the required statement.
The convention comparisons **N1-N9** require no additional Lean changes.
Three sign and duality facts are used together: the exchange monomials are
interchanged (1.2), the exchange ratio and node character are inverted (1.3,
1.4), and the Lean `H` is the negative of the reference's `H` while the Lean
primitive subtracts `dH` (1.6).

Inputs compared:

* reference proof: [`tex/proof-blueprint.tex`](tex/proof-blueprint.tex),
  [`target-theorem.md`](target-theorem.md) and
  [`proof-blueprint.md`](proof-blueprint.md);
* accepted Lean source identified by
  [`../verification/accepted-library.json`](../verification/accepted-library.json).

**Verification method.** Declaration names and types were checked with
`lake env lean` in the pinned Lean 4.34.1, Mathlib and FsFltz environment.
The full build and transitive axiom evidence are recorded in
[`../verification/README.md`](../verification/README.md). The current PDFs
include the stratified identity and explicit chart rank; their independent
typesetting check is [`../verification/document-check.json`](../verification/document-check.json).

* **Names and types.** Every Lean declaration cited below was confirmed with
  `#check`. Two citations were corrected by that pass: `PrimitiveLocalization`
  has no `logNorms` of its own (it reuses `DominanceCutoff.logNorms`), and
  `dense_initialTorus` is `ClusterSkeleton.dense_initialTorus`, declared in
  `InitialTorusDensity.lean` outside the `IndependentNodeChart` namespace.
* **Definitional claims.** Each quoted unfolding was confirmed by `rfl`: the row
  exponents of `positiveMonomial`/`negativeMonomial` (1.2), `exchangeCharacter`
  and `normalizedPartner` (1.3), `rowLog`, `angular` and `nodeLog` (1.4), the
  exact `H` sum and `alpha = beta - dH` (1.6), the formulas for `radial`,
  `radialLength`, `rho`, `vartheta`, `angularWindow`, `angularRadius`, `chi` and
  `dominance` (1.8), and the `coordinateCap` description (1.9). The constant
  identifications `a = κ` (`radial = A + κ` for `A ≤ -(2κ-2ε)`) and `δ₀ = 2ε`
  (`radial = 0` for `A ≥ -2ε`) were derived from `radial_tail` and
  `radial_eq_zero`.
* **The sign argument.** Its three ingredients were *proved* in scratch, not
  merely read: `rho (-x) = rho x`, `vartheta δ (-T) = -vartheta δ T`, and
  therefore `deriv (vartheta δ) (-T) = deriv (vartheta δ) T` (via
  `deriv_comp_neg`). These are what make `H_Lean = -H_reference` and make the
  radial equation of 1.7 transport verbatim.
* **The statements in part 3.** The **G1** and **G2** statements are
  implemented in the accepted library. Their proofs and exact declarations
  are reproduced with each entry.

Compilation and the transitive axiom audit of the compared Lean sources are
independently recorded in [`../verification/build.log`](../verification/build.log)
and [`../verification/axioms.log`](../verification/axioms.log). The verifier reports
`FULL_GEOMETRIC_TARGET_VERIFIED` with 58 modules and 1492 declarations at
accepted source commit `4c02c1e5bbc68907552632344ae04017d82a30b4`, axioms
limited to `propext`, `Classical.choice`, `Quot.sound` throughout.

**Citation convention.** Declarations are cited as `File.name`, where `File` is
the module file under `ClusterSkeleton/`. Two files carry a namespace different
from their name: `IndependentNodeSmooth.lean` continues the namespace
`ClusterSkeleton.IndependentNodeChart` (so `IndependentNodeSmooth.basis_cardinality`
has the full name `ClusterSkeleton.IndependentNodeChart.basis_cardinality`), and
`FiniteTimeConfinement.lean` also contains the namespace
`ClusterSkeleton.CoordinateBounds` (cited below as
`FiniteTimeConfinement.CoordinateBounds.*`), and `InitialTorusDensity.lean`
opens `ClusterSkeleton.IndependentNodeChart` for its local lemmas while
`dense_initialTorus` itself is `ClusterSkeleton.dense_initialTorus`. A few cited
helpers are `private` in their file and are marked as such; a proposed statement
that needs one of them must either re-prove it or drop the `private` modifier.

---

## 1. Convention map

### 1.1 Data and hypotheses

| Reference | Lean | Remark |
| --- | --- | --- |
| index sets `M ⊔ F`, `n = \|M\|+\|F\|` | `S.mutable : Finset (Fin d)` inside `Fin d`, `d = n` | `Seed.lean`; frozen = complement of `S.mutable` |
| `E ∈ GL_n(ℤ)`, mutable columns `B̃`, `K = E D̃` skew, `D̃ = I` so `K = E` | `S.B : Matrix (Fin d) (Fin d) ℤ` with `S.skew : ∀ i j, B i j = -B j i` | the identification used throughout is **entrywise**: `E_{jl} = K_{jl} = S.B j l`, `d_i = 1` |
| `B = E_{M,M}` acyclic (no directed cycle of positive entries) | `S.acyclic : WellFounded (fun i j : S.Mutable => 0 < S.B i j)` | equivalence with the cycle formulation: `Seed.wellFounded_iff_no_directed_cycle` |
| unimodular completion `E ∈ GL_n(ℤ)` | `Seed.Unimodular S : S.B.det = 1` | see **N1**: for an integral skew-symmetric matrix `det B = Pf(B)²`, so `det B = ±1 ⇔ det B = 1`; the two hypotheses coincide in this scope |
| frozen `z_j` invertible variables | `Point` carries `∀ f ∉ S.mutable, p.a f ≠ 0`; no frozen value is fixed | `Seed.Point` |
| exchange relations `z_i z_i' = P_i^+ + P_i^-` | `p.a i * p.b i = S.positiveMonomial p.a i + S.negativeMonomial p.a i` | `Seed.Point.exchange`; carrier is the actual complex point set with the inherited subtype topology |
| `𝒜(B̃)` closed in `ℂ^{2m} × (ℂ*)^f` | `CapSet.isClosed_ambientCap` (private), `FiniteTimeConfinement.CoordinateBounds.isClosed_ambientBox` (private) / `isCompact_coordinateBox` | the reference uses closedness only for compactness arguments; Lean proves exactly those |
| independence of `I ⊂ M` | `Seed.Independent I : I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.B i j = 0` | includes the diagonal, which is automatic from `skew` |

### 1.2 The two exchange monomials are interchanged

Reference (column exponents, `B̃_{ji}` over the column `i`):
`P_i^± = ∏_j z_j^{[±B̃_{ji}]_+}`.
Lean (row exponents, `Seed.lean`):

```
positiveMonomial a i = ∏ j, a j ^ (S.B i j).toNat
negativeMonomial a i = ∏ j, a j ^ (-S.B i j).toNat
```

With `E = B` entrywise and `B` skew, `[B i j]_+ = [-B j i]_+`, hence

```
Lean positiveMonomial = reference P_i^-,      Lean negativeMonomial = reference P_i^+ .
```

The **two monomials are interchanged**, their sum is unchanged, so the carrier
`Seed.Point` is literally the reference's exchange variety. Every statement that
uses only the sum (`Seed.Point.exchange`, `CapSet.coordinateCap_norm_b_le`,
`unitPoint`) is insensitive to the interchange; the statements that use one
monomial separately are the ones where the interchange must be read (next item).

### 1.3 The exchange ratio is inverted; node coordinates

```
exchangeCharacter p i = positiveMonomial p.a i / negativeMonomial p.a i = ∏ j, p.a j ^ (S.B i j)
```

(`NodeCoordinates.exchangeCharacter`, `exchangeCharacter_eq_zpow_product`),
while the reference's `t_i = P_i^+/P_i^- = z^{c_i}` with `c_i = E e_i`. Hence

```
exchangeCharacter p i = (t_i)⁻¹ ,     c_i(u) = -rowLog,  (see 1.4).
```

Node data:

| Reference | Lean |
| --- | --- |
| `x = z_i` | `p.a i` |
| `y = z_i'/P_i^-` | `normalizedPartner p i = p.b i / negativeMonomial p.a i = y/t_i` |
| `t = t_i` | `exchangeCharacter p i = 1/t_i` |
| `𝒩 = {xy = 1+t, t ∈ ℂ*}` | `IndependentNodeChart.Node = {uv : ℂ × ℂ // uv.1*uv.2 ≠ 1}`, equation `normalized_node_equation : p.a i * normalizedPartner p i = 1 + exchangeCharacter p i` |

The map `(x,y,t) ↦ (x, y/t, 1/t)` is an isomorphism of `{xy = 1+t, t ≠ 0}`, so
the Lean node is the reference node in reciprocal coordinates. The divisor
conditions are invariant under it: `t = -1 ⇔ exchangeCharacter = -1`, and
`y = 0 ⇔ normalizedPartner = 0 ⇔ p.b i = 0` (on an independent locus, where
both monomials are units: `positiveMonomial_ne_zero_on_independent_locus`,
`negativeMonomial_ne_zero_on_independent_locus`).

### 1.4 Torus logarithmic coordinates, and the sign of `v` and `η`

| Reference | Lean | Relation |
| --- | --- | --- |
| `u_j = log\|z_j\|` | `TorusCorrection.A S p j = Real.log ‖p.a j‖` (also `GlobalLiouvilleField.A` and `DominanceCutoff.logNorms`, which `PrimitiveLocalization` reuses) | equal |
| `θ_j = arg z_j` | `Complex.arg (p.a j)`, used only through `TorusPrimitive.angleCovector` (`Im(da_j/a_j)`) | equal |
| `v_i = log\|t_i\| = c_i(u)` | `TorusCorrection.rowLog S p i = ∑ j, (B i j) * A p j` | `rowLog = -v_i` |
| `η_i = arg t_i = c_i(θ)` | `arg (exchangeCharacter p i)` | `arg(exchangeCharacter p i) = -η_i` in `ℝ/2πℤ` |
| `η_i - π` (signed distance to the divisor) | `PrimitiveLocalization.angle p i = (Complex.log (-exchangeCharacter p i)).im = arg(-exchangeCharacter p i)` | `= -(η_i - π)` |
| `Log(-t_i) = v_i + i(η_i-π)` | `PrimitiveLocalization.nodeLog p i = Complex.log (1 - p.a i * normalizedPartner p i) = Complex.log (-exchangeCharacter p i)` | `nodeLog = -Log(-t_i)` |

So **`v`, `η-π` and `Log(-t)` all change sign** when passing to the Lean
variables, while `u` and `θ` do not. Two places absorb this automatically:
`PrimitiveCutoffs.rho` is even in its argument (`rho x = smoothTransition (2 - x^2)`),
and `PrimitiveCutoffs.vartheta δ` is odd (`arcsin (sin T)` times an even window),
see 1.6 and 1.8.

### 1.5 Sign of the logarithmic two-form and of `λ_tor`

`GeometryTarget.SmoothPresentation.logarithmicImaginaryValue` is

```
Im ( (1/2) ∑ i ∑ j (B i j) * ( (da_i v / a_i)(da_j w / a_j) - (da_i w / a_i)(da_j v / a_j) ) )
```

i.e. exactly `Im ( (1/2) ∑_{i,j} B_{ij} dlog a_i ∧ dlog a_j )` with the
convention `(α ∧ β)(v,w) = α(v)β(w) - α(w)β(v)`. With `K = B` entrywise this is
the reference's `Im Ω` **with the same sign, no transpose and no extra factor**;
on the torus both equal `∑_{j,l} K_{jl} du_j ∧ dθ_l` (the computation
`Im Ω = ∑ K_{jl} du_j ∧ dθ_l` uses only `K^T = -K`). The Lean side is pinned by
`GlobalTwoForm.omega_torus` and re-exported in the final theorem as
`FullSkeleton.torus_anchor`.

`TorusPrimitive.beta` is `∑_i ∑_j (B i j) * log‖a_i‖ • angleCovector j`, i.e.
`u^T K dθ = λ_tor` with the reference's sign (`evalOne_beta`: "no factor one
half, minus sign, or inverse matrix"); `d λ_tor = ∑ K_{jl} du_j ∧ dθ_l = Im Ω`
is consistent with the sign fixed in the previous paragraph, and is what
`TorusCorrection.exteriorDerivative_alpha` proves.

In the node block the two readings agree as well: `∑_l B_{il} dlog a_l = dlog(exchangeCharacter_i)
= -dlog t_i`, so the `i`-block of `Im Ω` is `dlog t_i ∧ dlog z_i`, which is the
reference's node form `d log t ∧ d log x` (equivalently `dy ∧ dx/(xy-1)`).

### 1.6 Sign of `H`, and why the primitive still matches

Reference: `H = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)`, `λ_ac = λ_tor + dH`.

Lean (`TorusCorrection.H`, `manuscript_formula`):

```
H = ∑ i ∈ S.mutable, radial ε κ (A p i) * dominance S ε i (A p) * rho (rowLog p i)
                      * vartheta δ (arg (-exchangeCharacter p i))
alpha = TorusPrimitive.alpha S hdet H = beta - d H          (TorusPrimitive.alpha)
```

Because `rho` is even (`rowLog = -v`), and `vartheta δ` is odd with
`vartheta δ (-(η-π)) = -vartheta δ (η-π)`, writing `β(η) := vartheta δ (η-π)`
gives

```
H_Lean = - H_reference ,        alpha_Lean = λ_tor - dH_Lean = λ_tor + dH_reference = λ_ac .
```

**The two sign flips (the angular variable and the minus sign in front of `dH`)
cancel exactly**; the Lean primitive is the reference's `λ_ac`, not its negative.
This is the single most error-prone point of the translation and should be quoted
whenever a reference formula containing `β` or `H` is transported.

Consistency check at the node, from `NodePrimitiveCancellation.cancellation`
(`A • dT - S • dθ - d((A+κ)T) = lambda κ`): with `A = u_i`, `S = Re nodeLog = -v_i`,
`T = Im nodeLog = -(η_i-π)` this is

```
lambda κ = v_i dθ_i - u_i dη_i + d((u_i+κ)(η_i-π)) ,
```

which is the reference's local node primitive `v dθ - u dη + d(hρβ)` in the
plateau regime `h(u) = u+a`, `ρ = 1`, `β(η) = η-π`, with `a = κ`. Equivalently
`lambda κ = -Im(nodeLogQuotient • du + κ • dL)` equals the reference's
`Im(Log(1-z y)/z dz) + a d arg(1-z y)` because `nodeLog_Lean = -Log(-t)` (1.4);
again two reciprocal sign flips cancel. Smooth extension across `{z_i = 0}` with
value `-y` on the divisor is `NodeLogExtension.nodeLogQuotient`,
`nodeLogQuotient_zero`, `analyticOnNhd_nodeLogQuotient`.

### 1.7 Liouville field and angle flow

* Reference convention `ι_Z dλ = λ`. Lean `LiouvilleData.contraction`:
  `evalTwo (exteriorDerivative primitive) p (field p) v = evalOne primitive p v`,
  i.e. the **same** convention; uniqueness of the field is
  `LiouvilleData.field_eq_liouvilleVector`, and the constructed field is
  `GlobalLiouvilleField.Z` (`= liouvilleVector (GlobalPrimitive.alpha …)`).
* Reference radial equation `u̇_i = u_i - h(u_i) χ_i ρ(v_i) β'(η_i)` (`i ∈ M`),
  `u̇_j = u_j` (`j ∈ F`). Lean
  `TorusLiouvilleDynamics.mutable_radial_equation` /
  `frozen_radial_equation`, lifted to the glued field by
  `GlobalLiouvilleField.mutable_radial_equation` / `frozen_radial_equation`:

  ```
  (logarithmicComponents … p i).re = A p i
      - radial ε κ (A p i) * dominance … * rho (rowLog p i)
        * deriv (vartheta δ) (arg (-exchangeCharacter p i))
  ```

  `deriv (vartheta δ)` is **even**, so `deriv (vartheta δ) (-(η-π)) = β'(η)`: the
  correction factor carries no sign change, and the Lean equation is the
  reference equation verbatim.
* Reference `v̇_i = v_i - ∑_k B_{ki} h(u_k) χ_k ρ(v_k) β'(η_k)`. Lean
  `TorusLiouvilleDynamics.radial_matrix_equation` is exactly this identity in the
  paired form `∑_i B_{ij} Re(comp_i) = ∑_i B_{ij} A_i - ∑_{i∈M} amplitude_i · ϑ'_i · B_{ij}`
  (note `∑_i B_{ij} A_i = -rowLog_j = v_j`), and `real_logarithmicComponents`
  inverts `B` (using `det B = 1`) to recover the componentwise form.
* Reference angle equation `η̇_i = (1/d_i) ∂_{u_i} H`. Lean
  `TorusLiouvilleDynamics.angular_equation` /
  `angular_equation_logarithmic` / `angular_equation_partial_deriv`:
  `∑_j B_{ij} Im(comp_j) = ∂H_Lean/∂u_i` in the smooth logarithmic germ. Since
  `∑_j B_{ij} Im(comp_j) = d/dt arg(exchangeCharacter_i) = -η̇_i` and
  `H_Lean = -H_ref`, this is the reference equation with both sides negated.
* Reference `θ̇ = -K^{-1} ∂_u H` is not stated separately in Lean; it is the same
  contraction identity as `radial_matrix_equation` before inverting `B`, and the
  inverted form is `real_logarithmicComponents` (see **N4**).

### 1.8 Cutoff dictionary

| Reference | Lean | Correspondence and properties |
| --- | --- | --- |
| `h ≤ 0`, `0 ≤ h' ≤ 1`, `u - h(u) < 0` on `u<0`, `h(u) = u+a` for `u ≤ -L`, `h = 0` near `[0,∞)` | `PrimitiveCutoffs.radial ε κ A = -radialLength ε κ * transitionPrimitive ((-A-2ε)/radialLength ε κ)`, `radialLength ε κ = 2(κ-2ε)` | `radial_nonpos`, `radial_deriv_nonneg`, `radial_deriv_le_one`, `radial_gt`, `radial_tail` (`radial = A + κ` for `A ≤ -radialLength-2ε`), `radial_eq_zero` (`= 0` for `A ≥ -2ε`), `radial_abs_le`/`radial_linear_growth` (`\|h(u)\| ≤ \|u\|+L`) |
| `a` | `κ` | from `radial_tail`; also the divisor rate: `Z\|z_i\|² = -2κ\|z_i\|²` |
| `L` | `2κ - 2ε` (`= radialLength ε κ + 2ε`) | tail threshold of `radial` |
| `δ₀` with `h = 0` on `(-δ₀,∞)` | `2ε` | `radial_eq_zero` |
| `L > a > 0` | `0 < ε`, `2ε + 1 ≤ κ` | `2ε+1 ≤ κ` gives `a = κ > 0`, `L - a = κ - 2ε ≥ 1 > 0`, and `1 + κ > 0` for the partner rate |
| `ρ ∈ C_c^∞(ℝ,[0,1])`, `ρ = 1` near `0` | `PrimitiveCutoffs.rho x = smoothTransition (2 - x^2)` | `rho_eq_one` (`\|x\| ≤ 1`), `rho_eq_zero` (`\|x\| ≥ 2`), `rho_compactSupport`; **even**, which absorbs `rowLog = -v` |
| `β ∈ C^∞(ℝ/2πℤ)`, `supp β ⊂ (π-ε,π+ε)`, `β(η)=η-π` near `π`, `(η-π)β ≥ 0`, `β' ≤ 1` | `PrimitiveCutoffs.vartheta δ T = arcsin (sin T) * angularWindow δ T`, applied to `T = arg(-exchangeCharacter)` | `vartheta_periodic`, `vartheta_representative_independent` (no angle lift is chosen — this replaces the reference's "lift in `(-ε,ε)`"), `vartheta_eq_self` (`= T` near `0`), `vartheta_support_principal`/`vartheta_tsupport_principal` with radius `angularRadius δ = min (δ/2) (π/4)`, `vartheta_local_sign` (`T·ϑ(T) ≥ 0`), `vartheta_deriv_le_one` |
| `ε` of `supp β ⊂ (π-ε,π+ε)`, `0<ε<π` | `angularRadius δ = min (δ/2) (π/4)` | **name collision**: the reference's `ε` is the angular support radius, the Lean `ε` is the dominance separation width. They are unrelated. |
| `ϑ : ℝ → [0,1]` nonincreasing, `=1` on `(-∞,-1]`, `=0` on `[0,∞)` | `DominanceCutoff.chi ε x = smoothTransition ((-2x-ε)/ε)` | `chi_eq_one_iff` (`x ≤ -ε`), `chi_eq_zero_iff` (`x ≥ -ε/2`), `chi_nonneg`, `chi_le_one`, `exists_chi`; Lean's cutoff vanishes already at `-ε/2`, a strictly stronger localization |
| `χ_i = ∏_{j∈M, B_{ji}≠0} ϑ(u_i-u_j)` | `DominanceCutoff.dominance S ε i A = ∏_{j ∈ mutableNeighbors S i} chi ε (A i - A j)`, `mutableNeighbors S i = S.mutable.filter (B i j ≠ 0)` | index sets agree because `B i j ≠ 0 ↔ B j i ≠ 0`; `dominance_eq_one_of`, `dominance_eq_zero_iff` |
| `χ_iχ_j = 0` when `B_{ij} ≠ 0` | `DominanceCutoff.adjacent_exclusion` | identical statement |
| final admissible constants | `ε = 1`, `κ = 3`, `δ = 1` in `FullSkeleton.liouvilleSkeletonTarget` | gives `a = 3`, `L = 4`, `δ₀ = 2`, angular radius `min(1/2, π/4) = 1/2`; `GlobalPrimitive.exists_global_primitive` additionally exhibits `(1, 3, π/2)` |

### 1.9 Cap description

Lean (`CapSet.coordinateCap`):

```
coordinateCap S = {p | (∀ f ∉ S.mutable, ‖p.a f‖ = 1) ∧
                       ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧ ((1 - ‖p.a i‖^2 : ℝ) : ℂ) * p.b i = 0}
```

This is **literally** the reference's "equivalent coordinate cap"
`{|z_f| = 1 (f∈F), |z_i| ≤ 1, (1-|z_i|²)z_i' = 0 (i∈M)}` of the reference's
*Formalization target and convention matching* section. The reference's primary
description `⋃_{I independent} Λ_I`,
`Λ_I = {z_i' = 0, |z_i| ≤ 1 (i∈I), |z_j| = 1 (j ∉ I)}`, **has no Lean
counterpart**: there is no definition of `Λ_I` anywhere in `ClusterSkeleton/`
(the only `⋃` over independent sets is the chart cover
`CoordinateLoci.iUnion_independent_candidateChartLocus`). The equality of the two
descriptions is gap **G1** below; all its ingredients already exist
(`CapIndependence.coordinateCap_strictCapIndices_independent`,
`CapSet.coordinateCap_b_eq_zero`, `CapAngularTangency.norm_eq_one_of_not_strict`).

---

## 2. Step table

`hdet : S.Unimodular`, `hε : 0 < ε`, `hκ : 2*ε+1 ≤ κ`, `hδ : 0 < δ` are the
standing Lean hypotheses; "at least as strong" is judged in the skew-symmetric
scope of this audit.

| # | Reference step | Lean declaration(s) (module.name) | Status in the skew-symmetric scope |
| --- | --- | --- | --- |
| 1 | Lemma (i): `{i ∈ M : z_i(p)=0}` is independent (acyclic maximal-path argument) | `ZeroSet`: `Seed.Point.outgoing_ne_zero`, `matrix_eq_zero_of_coordinates_zero`, `zeroSet_independent` | present; **stronger**: proved by `S.acyclic.induction` for arbitrary multiplicities, without unimodularity, and includes the diagonal |
| 2 | Lemma (ii): `U_I ≅ 𝒩^I × (ℂ*)^{m+f-2\|I\|}` with `(x,y,t) = (z_i, z_i'/P_i^-, t_i)` | `CoordinateLoci.candidateChartLocus`, `isOpen_candidateChartLocus`; `NodeCoordinates.normalized_node_equation`, `normalized_node_product_ne_one`, `independentRowMatrix_mul_rightInverse`, `independent_rows_linearIndependent`; `IntegralBasisCompletion.SplitIntegerRows.splittingEquiv`, `basis`, `independentRowBasis`; `IndependentNodeChart.forward`, `backward`, `backward_forward`, `forward_backward`, `homeomorph`; `IndependentNodeSmooth.basis_cardinality`, `vector_finrank_complex`, `vector_finrank_real`, `modelEquiv`; `IndependentLaurentCoordinates.independentRowLaurentHomeomorph`; `LaurentCoordinates.monomialHomeomorph` | present as a homeomorphism onto `({i∈I} → Node) × (ℂ*)^{complementRank}` in reciprocal node coordinates (1.3). `basis_cardinality` gives `\|I\| + complementRank = d - \|I\|`, and the exponent `m+f-2\|I\|` is now literal as `IndependentNodeSmooth.complementRank_eq_sub_two_mul_card` (`complementRank (independentRowRightInverse S I) = d - 2 * I.card`), with `IndependentNodeSmooth.two_mul_card_le` for `2*\|I\| ≤ d`: gap **G2** closed. The ring-theoretic part (`𝒪(U_I)` presentation) is deliberately absent: **N2** |
| 3 | Lemma (iii): the `U_I` cover `𝒜(B̃)` | `ZeroSet.exists_independent_nonvanishing_locus`, `CoordinateLoci.exists_independent_candidateChartLocus`, `iUnion_independent_candidateChartLocus`, `NodeNondegeneracy.zeroSet_chart_mem` | present; equal strength |
| 4 | Exchange model `𝒜(B̃) = ℂ[z,z',z_F^{±1}]/(z_iz_i'-P_i^+-P_i^-)` (BFZ III, Cor. 1.21) | no counterpart (by design): `Seed.Point` is the actual complex point set with inherited topology; `CapSet.isClosed_ambientCap`, `FiniteTimeConfinement.CoordinateBounds.isCompact_coordinateBox` supply the only consequences used | **N2**: no Lean change needed |
| 5 | Smooth atlas on the actual variety (separate obligation flagged in the reference) | `SmoothAtlas.rawChart`, `chart`, `chart_mem_atlas`, `contDiffOn_transition`, `smooth`, `inclusion_smooth`, `inclusion_immersion`, `presentation`; `GeometryNativeBridge.SmoothPresentation.inclusion_isDiffImmersionAt` | present; **stronger** than the reference's remark: the inclusion is proved smooth and immersive, not assumed |
| 6 | `Ω = (1/2)∑K_{jl} dlog z_j ∧ dlog z_l` and its symplectic extension; `Im Ω` on the torus | `GeometryTarget.SmoothPresentation.logarithmicImaginaryValue`; `NodeTwoForm.complexForm`, `realForm`, `localForm`, `localForm_torus`, `localForm_boundary`, `LocalCompatibility`, `GlobalClosedExtension`; `NodeNondegeneracy.localForm_boundary_nondegenerate`, `zeroSet_localForm_nondegenerate`; `LocalFormGluing.glue`, `existsUnique_smooth_gluing`; `GlobalTwoForm.omega`, `omega_eq_localForm`, `isSmoothForm_omega`, `omega_torus`, `exteriorDerivative_omega`, `globalClosedExtension`; `GlobalSymplectic.nondegenerate_omega`, `isSymplecticOn_omega`; `FormExtensionUniqueness.smoothAtlas_twoForm_extension_unique` | present as a **real** smooth closed nondegenerate extension of `Im Ω`, unique by torus density; the reference's holomorphic `Ω` itself is not constructed: **N3** (explicitly out of scope, not claimed) |
| 7 | `λ_tor = u^T K dθ` | `TorusPrimitive.angleCovector`, `beta`, `evalOne_beta`, `alpha`, `evalOne_alpha`, `matrixForm_real`, `exteriorDerivative_alpha` | present with the same sign (1.5) |
| 8 | Split of `λ_tor` over an independent `I` (`eq:acyclic-ltor-split`) | `PrimitiveResidual.split_sum` (finite matrix identity), `beta_decomposition` (form-level), `residual`, `tau`, `logRow`, `tau_eq_nodeAngle_differential`; `NativeNodePrimitive.lambda_torus`, `block_torus` | present and literal: the bracket `A_i ∑_j B_{ij}T_j - (∑_j B_{ij}A_j) T_i` is `v_i dθ_i - u_i dη_i` in reference variables (1.4); proved for all points, needing no nonvanishing |
| 9 | `χ_i`, `H = ∑ d_i h(u_i)χ_iρ(v_i)β(η_i)`, `λ_ac = λ_tor + dH` | `DominanceCutoff.dominance`; `TorusCorrection.H`, `manuscript_formula`, `contMDiffOn_H`, `alpha`; `TorusLiouvilleDynamics.amplitude`, `logarithmicHamiltonian`, `H_logarithmic_identity`, `differential_H`, `differential_H_angular`, `differential_H_radial` | present with `H_Lean = -H_ref` and `alpha = beta - dH_Lean = λ_ac` (1.6) |
| 10 | Near-divisor form of `H` (`eq:acyclic-H-near`) and smooth extension of `λ_ac` over `W` | `PrimitiveLocalization.region`, `region_mem_nhds`, `neighborhood`, `plateaus`, `adjacent_dominance_zero`, `correction_eq_affine`, `adjacent_correction_zero`, `correction_eventuallyEq`, `correction_mfderiv_eq`; `RegularCorrection.surviving`, `regularH`, `singularH`, `H_split`, `H_eventuallyEq`, `differential_H_split`, `literal_formula`; `NodePrimitiveCancellation.lambda`, `cancellation`, `cancellation_oneForm`, `lambda_zero`, `numerical_sign`; `NodeLogExtension.nodeLogQuotient`, `nodeLogQuotient_zero`, `analyticOnNhd_nodeLogQuotient`, `contDiffAt_nodeLogQuotient_zero`; `NativeNodePrimitive.nodeMap`, `locus`, `lambda`, `block`, `lambda_boundary`; `LocalPrimitive.eta`, `locallySmooth_eta`, `differential_H_eq_sum`, `eta_eq_torus`, `local_cover`, `agree_on_torus`, `covers`; `GlobalPrimitive.alpha`, `alpha_eq_eta`, `isSmoothForm_alpha`, `alpha_eq_torus`, `exteriorDerivative_alpha`, `nondegenerate_exteriorDerivative_alpha`, `isSymplecticOn_exteriorDerivative_alpha` | present; the reference's `W` is `PrimitiveLocalization.region`/`LocalPrimitive.neighborhood`, the `H'` independence argument is `RegularCorrection.H_split` + `PrimitiveLocalization.adjacent_dominance_zero`, and the removable quotient `Log(1-z y)/z ↦ -y` is `NodeLogExtension`. Lean additionally proves gluing uniqueness (`LocalFormGluing.existsUnique_smooth_gluing`) |
| 11 | Flow equations (`eq:acyclic-flow`, `eq:acyclic-angle-flow`) for `u`, `θ`, `η`, `v` | `TorusLiouvilleDynamics.Z`, `contraction`, `omega_real`, `radialTangent`, `angularTangent`, `angular_equation`, `radial_matrix_equation`, `real_logarithmicComponents`, `radialCorrection`, `mutable_radial_equation`, `frozen_radial_equation`, `angular_equation_logarithmic`, `angular_equation_partial_deriv`; `GlobalLiouvilleField.Z`, `contraction_exteriorDerivative`, `contraction_omega`, `Z_eq_torus`, `logarithmicComponents`, `L`, `L_eq_logarithmicComponents`, `mutable_radial_equation`, `frozen_radial_equation`, `frozen_radial_equation_torus`, `angular_equation_partial_deriv`, `L_eq_A_of_collar`, `L_eq_A_of_nonneg`, `L_negative_bound`; `LocalAngularDynamics.angularRhs`, `nu`, `angularRhs_eq_radial`, `nu_eq_torus`, `nu_eq_logarithmicComponents`, `coordinate_drift`, `partner_drift`, `partner_drift_zero`, `coordinate_hasDerivWithinAt`, `partner_hasDerivWithinAt` | present; sign dictionary in 1.7. Lean proves them for the **glued global** field, then extends off the torus by density, which the reference only does pointwise on `W` |
| 12 | Radial bound `\|u̇_j\| ≤ C(1+\|u_j\|)`, `C = (1+max\|β'\|)(1+L)`, and `u̇_i ≤ u_i - h(u_i)` on `{u_i<0}` | `PrimitiveCutoffs.radial_abs_le`, `radial_linear_growth`; `TorusLiouvilleDynamics.amplitude_abs_le`, `real_components_growth`, `imaginary_components_growth`, `full_matrix_inverse_bound`, `dominance_partial_bound`, `amplitude_partial_bound`, `logarithmic_linear_growth`; `GlobalLiouvilleField.logarithmic_linear_growth`, `L_negative_bound`; `NativeRadialOrbit.amplitude_abs_le_radial`, `uniform_radial_error_bound`, `c_le_one`, `L_eq_A_sub_radial_mul_c`; `AllStrataGrowth.R`, `radial_growth`, `uniform_growth`, `integralCurve_growth`; `ScalarOrbitDynamics.RadialEquation`, `radial_velocity_le`, `radial_affine_bound`, `radial_antitone`, `radial_tendsto_atBot`, `radial_exp_tendsto_zero`, `radial_eq_exp_of_nonneg`, `radial_zero`, `radial_positive` | present; **stronger**: a single constant bounds radial *and* angular components *and* the partner drift simultaneously, uniformly over all zero strata, with honest within-derivatives along curves (`integralCurve_growth`) |
| 13 | Divisor flow `Z\|z_i\|² = -2a\|z_i\|²`, `ṫ_i = t_i Log(-t_i)`, invariance of `{z_i=0}` | `BoundaryTangency.deep_radius_torus`, `deep_radius` (`Re(comp_i) = -κ`), `nodeLog_drift_torus`, `nodeLog_drift` (`Z nodeLog_i = nodeLog_i`, equivalent to `ṫ = t Log(-t)` since `nodeLog = -Log(-t)`), `nodeProduct_drift`, `zero_coordinate_tangent`, `coordinate_tangent`; `ZeroStratumInvariance.normSq_drift` (`= -2κ\|z_i\|²`), `normSq_hasDerivWithinAt`, `coordinate_zero_iff`, `zeroSet_eq`, `coordinate_ne_zero_iff`; `CapAngularTangency.*` | present with `a = κ`; **stronger**: zero/nonzero persistence is proved in **both** time directions on an arbitrary preconnected domain, and the zero set is constant along curves |
| 14 | Partner flow `Z\|y_i\|² = 2(1+a)\|y_i\|²` on `{z_i=0}`, `\|y_i(φ^τ p)\| = e^{(1+a)τ}\|y_i(p)\|`, and the general `Z log\|y_i\| = Re φ(t_i)+a` | `NormalizedPartnerNormDrift.partner_smooth`, `differential_partner`, `quotient_smooth`, `partner_drift_of_ne_zero`, `pairing_sub`, `normSq_drift_of_ne_zero`, `normSq_drift` (general near-node law with `nodeLogQuotient`, the analogue of `Re φ(t)+a`), `normSq_drift_zero` (`= 2(1+κ)\|y\|²`), `normSq_hasDerivWithinAt`, `normSq_hasDerivWithinAt_zero`; `ZeroStratumPartnerDynamics.exp_law_of_hasDerivWithinAt`, `normSq_hasDerivWithinAt`, `normSq_eq_exp_mul`, `partner_zero_iff`, `partner_ne_zero_iff`, `normSq_lt`, `strictMonoOn_normSq` | present with `a = κ`; **stronger**: the exponential law holds on arbitrary preconnected time sets in both directions |
| 15 | Completeness of `Z` (maximal curve leaves every compact set) | `FiniteTimeConfinement.radial_component_bound`, `normalizedPartner_norm_le`, `logarithmic_component_bound`, `fixed_mask_log_bound`, `uniform_original_bounds`, `finite_time_compact_confinement`, `bounded_horizon_closure`, `CoordinateBounds.coordinateBox`, `isCompact_coordinateBox`, `partner_eq_normalized_mul`, `partner_eq_div`, `norm_partner_le_of_bounds`; `NativeCompleteFlow.exists_global_integralCurve`, `exists_completeLiouvilleFlow`, `completeFlow`, `exists_global_integralCurve_through`, `exists_extension_Ioo` | present; **stronger**/different route: finite-horizon confinement into a precomputed compact set plus a uniform local lifetime on compacts yields a genuine two-sided `Flow` with joint smoothness, rather than only `τ_± = ±∞` for each maximal curve: **N5** |
| 16 | Inclusion (i) `Skel(Z) ⊂ ⋃_I Λ_I` | `ScalarOrbitDynamics.frozen_log_orbit`, `trapped_frozen_log_bounded`, `trapped_frozen_norm_eq_one`; `NativeRadialOrbit.radialEquation`, `negative_log_laws`, `nonnegative_log_law`, `positive_log_law`, `zero_log_law`, `eventually_not_mem_compact`, `not_isCompact_closure_forward_image`, `original_norm_le_one_of_mem_trappedSet`, `frozen_log_hasDerivAt`, `frozen_norm_eq_one_of_mem_trappedSet`, `trapped_radial_restrictions`; `CompactInteriorRigidity.row_single`, `amplitude_single_deep`, `characterCoefficient_eq_one_deep`, `sin_mul_vartheta_nonneg`, `neg_im_mul_vartheta_arg_nonneg`, `angular_distance_sq_hasDerivAt`, `angular_scalar_eq_neg_one_of_tendsto`, `angular_scalar_eq_neg_one_backward`, `interior_norm_tendsto_zero`, `exists_limit_zero_at_interior`, `frozen_norm_eq_one`, `interior_matrix_eq_zero`, `initial_neighbor_unit`, `neighbors_unit_forward`, `shifted_character_hasDerivAt`, `character_tendsto_neg_one`, `character_eq_neg_one_initial`, `initial_partners_zero`, `compactInteriorRigidityTarget`; `ZeroStratumEscape.compact_zero_slice_bound`, `eventually_not_mem_compact`, `not_isCompact_closure_forward_image`, `partner_eq_zero_of_isCompact_closure`, `partner_eq_zero_of_mem_trappedSet`, `not_mem_trappedSet`; `ConstructedFlowReverseInclusion.compact_forward_image`, `radial_and_frozen_restrictions`, `initially_zero_partner`, `initially_nonzero_interior_partners`, `interior_partner`, `mutable_cap_product`, `trappedSet_subset_coordinateCap`, `constructedFlowReverseInclusionTarget` | present with the conclusion stated as `⊆ coordinateCap`; the independence of the limiting index set is `CapIndependence.coordinateCap_strictCapIndices_independent` / `CompactInteriorRigidity.interior_matrix_eq_zero`. The set-level reconciliation with `⋃_I Λ_I` is now `CapStrata.coordinateCap_eq_iUnion_lambdaStratum`: gap **G1** closed. The angular rigidity route differs from the reference's monotonicity argument: **N6** |
| 17 | Inclusion (ii) `Λ_I ⊂ Skel(Z)` (`Λ_I` compact and forward invariant) | `CapSet.coordinateCap`, `coordinateCap_norm_a_le`, `coordinateCap_b_eq_zero`, `coordinateCap_norm_b_le`, `isCompact_coordinateCap`; `CapIndependence.coordinateCap_outgoing_not_interior`, `coordinateCap_strictCapIndices_independent`; `CapAngularTangency.norm_eq_one_of_not_strict`, `mem_strict_locus`, `normalizedPartner_eq_zero_of_interior`, `exchangeCharacter_eq_neg_one_of_interior`, `angular_eq_zero_of_interior`, `maskedLogs_eq_zero_of_unit`, `radial_and_deriv_zero`, `coordinate_drift_eq_zero_of_unit`, `coordinate_hasDerivWithinAt_zero`; `InteriorPartnerPropagation.unit_norm_forward`, `neighbors_unit_forward`, `partners_zero_of_character`, `angular_scalar_eq_neg_one*`, `character_eq_neg_one_forward`, `propagate`, `interiorPartnerPropagationTarget`; `CapForwardInvariance.zero_forward`, `interior_forward`, `mutable_constraints_forward`, `frozen_norm_forward`, `forward`, `coordinateCapForwardInvarianceTarget`; `TrappedSet.trappedSet`, `mem_trappedSet_of_forwardOrbit_subset`, `subset_trappedSet_of_isCompact_forwardInvariant`; `ConstructedFlowCapInclusion.integralCurveOn`, `forward`, `isForwardInvariant`, `subset_trappedSet`, `isCompact_forwardOrbit_closure`, `constructedFlowCapInclusionTarget` | present; **stronger**: compactness and forward invariance are proved for the whole cap at once (hence, by `CapStrata.coordinateCap_eq_iUnion_lambdaStratum`, for the whole union `⋃_I Λ_I`; per-stratum compactness is `CapStrata.isCompact_lambdaStratum`), and the trapped set is defined purely dynamically |
| 18 | Theorem `thm:acyclic-skeleton`: a Liouville form of `Im Ω` with `Skel = ⋃_I Λ_I` | `GeometryTarget.SmoothPresentation`, `LiouvilleData`, `LiouvilleSkeletonTarget`, `FirstGeometricTarget`; `InitialTorusDensity.dense_initialTorus`; `FullSkeleton.trappedSet_eq_coordinateCap`, `liouvilleData`, `liouvilleData_flow`, `torus_anchor`, `liouvilleData_trappedSet`, `liouvilleSkeletonTarget_of_parameters`, `liouvilleSkeletonTarget`, `firstGeometricTarget` | present as `trappedSet completeFlow.flow = coordinateCap S` for the same constructed flow, with `ε = 1, κ = 3, δ = 1`; equality with the reference's `⋃_I Λ_I` form is now proved as `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`: gap **G1** closed |

---

## 3. Gap list

Ordered by priority: **G1 > G2 > G3**, then the items **N1-N9** that are
classified "no Lean change needed, because ...". "Concrete gap" entries were
proposals when this audit was written; **G1** and **G2** have since been
implemented in the Lean source and are marked closed below, each with its
exact declaration names and the integrating commit. **G3** is still an
optional proposal.

### G1 (high) — **closed**: the cap is now stated as `⋃_{I independent} Λ_I`

*Status.* **Closed** in the Lean source at integrating commit `4c02c1e5bbc68907552632344ae04017d82a30b4`
(implemented by mission `4ba40e77-f6df-4185-bd7b-cda666df0e2c`,
published commit `91c09d44fe3ce2bc132a4c8a1b19f5edd42d3cd6`). The chosen layout
is the new module `ClusterSkeleton/CapStrata.lean` (importing `CapIndependence`,
`CapAngularTangency` and `CoordinateLoci`), with the corollary appended to
`ClusterSkeleton/FullSkeleton.lean`. The delivered declarations are exactly the
statements proposed below, with no added hypothesis and no change to any
existing statement:

| Declaration | Full name |
| --- | --- |
| stratum | `ClusterSkeleton.lambdaStratum` |
| `Λ_I ⊆ C_B` | `ClusterSkeleton.lambdaStratum_subset_coordinateCap` |
| realized index set | `ClusterSkeleton.coordinateCap_subset_lambdaStratum_strictCapIndices` |
| stratified cap | `ClusterSkeleton.coordinateCap_eq_iUnion_lambdaStratum` |
| closedness | `ClusterSkeleton.isClosed_lambdaStratum` |
| per-stratum compactness | `ClusterSkeleton.isCompact_lambdaStratum` |
| stratified skeleton | `ClusterSkeleton.FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` |

All seven depend only on `propext`, `Classical.choice`, `Quot.sound`; the first
six are attributed to `ClusterSkeleton.CapStrata` (6 audited declarations) and
the last to `ClusterSkeleton.FullSkeleton`. The record of the original
difference and the proposed statements is kept below unchanged.

*Difference (as audited).* The reference's skeleton identity is
`Skel(Z) = ⋃_{I⊂M independent} Λ_I` with
`Λ_I = {z_i' = 0, |z_i| ≤ 1 (i∈I), |z_j| = 1 (j∈(M⊔F)\I)}`. Lean states
`trappedSet … = coordinateCap S`, the reference's *equivalent* cap description.
`Λ_I` is not defined in `ClusterSkeleton/`, and no theorem relates the two
descriptions, so the Lean theorem does not literally exhibit the stratified
form. **Apart from the holomorphicity of `Ω` itself (N3, out of scope), this
is the only part of the reference's theorem statement with no Lean
counterpart.**

*Proposed Lean statements, all checked* (target module: `ClusterSkeleton/CapIndependence.lean`,
which already imports `CapSet` and contains the strict-index independence
lemma; alternatively a new `ClusterSkeleton/CapStrata.lean` imported by
`FullSkeleton`):

```lean
/-- The reference's stratum `Λ_I`. -/
def lambdaStratum {d : ℕ} (S : Seed d) (I : Finset (Fin d)) : Set S.Point :=
  {p | (∀ i : S.Mutable, (i : Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧
       (∀ j : Fin d, j ∉ I → ‖p.a j‖ = 1)}

theorem lambdaStratum_subset_coordinateCap {d : ℕ} {S : Seed d}
    {I : Finset (Fin d)} (hI : I ⊆ S.mutable) :
    lambdaStratum S I ⊆ coordinateCap S

theorem coordinateCap_subset_lambdaStratum_strictCapIndices {d : ℕ} {S : Seed d}
    {p : S.Point} (hp : p ∈ coordinateCap S) :
    p ∈ lambdaStratum S p.strictCapIndices

theorem coordinateCap_eq_iUnion_lambdaStratum {d : ℕ} (S : Seed d) :
    coordinateCap S =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val

theorem isCompact_lambdaStratum {d : ℕ} (S : Seed d) (I : Finset (Fin d))
    (hI : I ⊆ S.mutable) : IsCompact (lambdaStratum S I)
```

and the corollary in `ClusterSkeleton/FullSkeleton.lean`:

```lean
theorem trappedSet_eq_iUnion_lambdaStratum :
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val
```

*Proof (checked in scratch against this commit; no new mathematics).*

```lean
theorem lambdaStratum_subset_coordinateCap {S : Seed d} {I : Finset (Fin d)}
    (hI : I ⊆ S.mutable) : lambdaStratum S I ⊆ coordinateCap S := by
  intro p hp
  refine ⟨fun f hf => hp.2 f (fun hfI => hf (hI hfI)), fun i => ?_⟩
  by_cases hi : (i : Fin d) ∈ I
  · exact ⟨(hp.1 i hi).1, by rw [(hp.1 i hi).2, mul_zero]⟩
  · have h1 := hp.2 (i : Fin d) hi
    refine ⟨le_of_eq h1, ?_⟩
    rw [h1]
    norm_num

theorem coordinateCap_subset_lambdaStratum_strictCapIndices {S : Seed d}
    {p : S.Point} (hp : p ∈ coordinateCap S) :
    p ∈ lambdaStratum S p.strictCapIndices := by
  refine ⟨fun i hi => ?_,
    fun j hj => CapAngularTangency.norm_eq_one_of_not_strict S hp j hj⟩
  have hlt : ‖p.a i‖ < 1 := ((p.mem_strictCapIndices i).mp hi).2
  exact ⟨hlt.le, coordinateCap_b_eq_zero hp i hlt⟩

theorem coordinateCap_eq_iUnion_lambdaStratum (S : Seed d) :
    coordinateCap S =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val := by
  refine Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · exact mem_iUnion.mpr
      ⟨⟨p.strictCapIndices, coordinateCap_strictCapIndices_independent hp⟩,
        coordinateCap_subset_lambdaStratum_strictCapIndices hp⟩
  · obtain ⟨I, hI⟩ := mem_iUnion.mp hp
    exact lambdaStratum_subset_coordinateCap I.property.1 hI
```

Compactness needs one auxiliary closedness lemma, also checked:
`isClosed_lambdaStratum` splits the two defining families with
`isClosed_iInter` and a `by_cases` on membership of `I` (each branch is either
`isClosed_le`/`isClosed_eq` against `(continuous_originalCoordinate S j).norm`
and `(continuous_apply i).comp continuous_subtype_val.snd`, or `isClosed_univ`),
and then

```lean
theorem isCompact_lambdaStratum (S : Seed d) (I : Finset (Fin d))
    (hI : I ⊆ S.mutable) : IsCompact (lambdaStratum S I) :=
  (isCompact_coordinateCap S).of_isClosed_subset (isClosed_lambdaStratum S I)
    (lambdaStratum_subset_coordinateCap hI)
```

Note that independence of `I` is *not* needed for either inclusion; it enters
only to index the union by the same family the reference uses, and the
independence of the index set actually realized by a cap point is
`coordinateCap_strictCapIndices_independent`.

*Dependency closed.* `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` now
states equation `eq:acyclic-skeleton` of the reference literally for the same
constructed flow, and `isCompact_lambdaStratum` supplies the reference's
per-stratum compactness used in its inclusion (ii). The delivered proofs are
the ones reproduced above, with `isClosed_lambdaStratum` proved by splitting the
two defining families with `Set.ofPred_forall` and `isClosed_iInter` rather than
by a `by_cases` on membership of `I`; the statements are unchanged.

### G2 (medium) — **closed**: the node-chart torus exponent is now literal

*Status.* **Closed** in the Lean source at integrating commit `4c02c1e5bbc68907552632344ae04017d82a30b4`
(implemented by mission `b1e1f5f9-b96b-45b0-a1be-edeab110c7f9`,
published commit `36e0e8ac48bb4feeea14f39dfee5845474887c6e`), in
`ClusterSkeleton/IndependentNodeSmooth.lean` next to `basis_cardinality` and so
in namespace `ClusterSkeleton.IndependentNodeChart`:

| Declaration | Statement |
| --- | --- |
| `ClusterSkeleton.IndependentNodeChart.complementRank_eq_sub_two_mul_card` | `SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card` |
| `ClusterSkeleton.IndependentNodeChart.two_mul_card_le` | `2 * I.card ≤ d` |

Both take only the standing `hdet : S.Unimodular` and `hI : S.Independent I`,
and both depend only on `propext`, `Classical.choice`, `Quot.sound`. The record
of the original difference and the proposed statement is kept below unchanged.

*Difference (as audited).* The reference's Lemma (ii) asserts
`U_I ≅ 𝒩^I × (ℂ*)^{m+f-2|I|}`. Lean's `IndependentNodeChart.homeomorph` lands in
`({i // i ∈ I} → Node) × NonzeroTorus (Complement S I)` where
`Complement S I = Fin (SplitIntegerRows.complementRank (independentRowRightInverse S I))`
is defined through `Submodule.basisOfPid`. The numeric identity is available
only as `IndependentNodeSmooth.basis_cardinality`
(`card {i ∈ I} + card (Complement S I) = card {j ∉ I}`), never as the stated
exponent.

*Proposed Lean statement, checked* (target module:
`ClusterSkeleton/IndependentNodeSmooth.lean`, next to `basis_cardinality`):

```lean
theorem complementRank_eq_sub_two_mul_card {d : ℕ} (S : Seed d)
    (I : Finset (Fin d)) (hdet : S.Unimodular) (hI : S.Independent I) :
    SplitIntegerRows.complementRank (independentRowRightInverse S I)
      = d - 2 * I.card
```

*Proof (checked in scratch against this commit).*

```lean
theorem complementRank_eq_sub_two_mul_card (S : Seed d) (I : Finset (Fin d))
    (hdet : S.Unimodular) (hI : S.Independent I) :
    SplitIntegerRows.complementRank (independentRowRightInverse S I)
      = d - 2 * I.card := by
  classical
  have hb := IndependentNodeChart.basis_cardinality S I hdet hI
  have hin : Fintype.card {i : Fin d // i ∈ I} = I.card := Fintype.card_coe I
  have hout : Fintype.card {j : Fin d // j ∉ I} = d - I.card := by
    have h := Fintype.card_subtype_compl (fun j : Fin d => j ∈ I)
    simpa [hin] using h
  have hle : I.card ≤ d := by simpa using Finset.card_le_univ I
  have hc : Fintype.card (IndependentNodeChart.Complement S I)
      = SplitIntegerRows.complementRank (independentRowRightInverse S I) := by
    simp [IndependentNodeChart.Complement]
  rw [hin, hout, hc] at hb
  omega
```

*Dependency closed.* Lemma (ii)'s exponent is now literal, and the companion
`two_mul_card_le` documents `2|I| ≤ d` for independent `I`, which was
previously only implicit.

### G3 (low) — unimodularity is stated as `det B = 1`, the reference as `E ∈ GL_n(ℤ)`

Classified as a **concrete but optional** gap; see **N1** for why no change is
mathematically required. If a reviewer prefers the reference's literal
hypothesis, the adaptable statement is

```lean
-- target module: ClusterSkeleton/Seed.lean (definition) + NodeCoordinates.lean (use site)
def Seed.UnimodularUnit {d : ℕ} (S : Seed d) : Prop := IsUnit S.B.det

theorem Seed.unimodular_iff_isUnit_det {d : ℕ} (S : Seed d) :
    S.Unimodular ↔ S.UnimodularUnit
```

The forward direction is immediate; the converse needs
`det B = Pf(B)^2 ≥ 0` for integral skew-symmetric `B`, which Mathlib does not
currently provide. Every downstream use already goes through
`IsUnit S.B.det` (`NodeCoordinates.independent_rows_inverse_pairing`) or through
`det = 1` only to produce a unit (`TorusLiouvilleDynamics.real_logarithmicComponents`),
so replacing the field would be mechanical once the equivalence exists.
Priority is low: in the skew-symmetric scope the two hypotheses have the same
models.

### N1 (no Lean change needed) — `det B = 1` vs `det B = ±1`

For an integral skew-symmetric matrix of even size, `det B = Pf(B)²`, and for
odd size `det B = 0`; hence a skew-symmetric integral `B` with `det B = ±1`
necessarily has `det B = 1`. The Lean hypothesis `Seed.Unimodular : B.det = 1`
therefore covers exactly the reference's `E ∈ GL_n(ℤ)` in this scope, with no
loss of generality. (See G3 for the optional literal restatement.)

### N2 (no Lean change needed) — the algebraic exchange model

The reference uses `eq:acyclic-exchange-model` (BFZ III, Cor. 1.21) twice: to
derive the chart of Lemma (ii), and to know that `𝒜(B̃)` is closed in
`ℂ^{2m} × (ℂ*)^f` for the completeness argument. The Lean development takes the
actual complex solution set of the exchange equations as its carrier
(`Seed.Point`, with the inherited subtype topology), constructs the chart
directly by explicit forward/backward formulas
(`IndependentNodeChart.forward/backward/homeomorph`, with the integral basis
completion replacing the Laurent-ring argument), and proves exactly the needed
closedness/compactness statements (`CapSet.isClosed_ambientCap` (private),
`FiniteTimeConfinement.CoordinateBounds.isClosed_ambientBox` (private),
`isCompact_coordinateBox`). Formalizing the generators-and-relations
presentation would add no step of the skeleton proof.

### N3 (no Lean change needed in scope) — holomorphic `Ω` versus real `Im Ω`

The reference calls `Ω` "its smooth holomorphic symplectic extension". Lean
constructs the **real** smooth closed nondegenerate extension of `Im Ω`
(`GlobalTwoForm.omega`, `GlobalSymplectic.*`), anchored on the dense initial
torus (`GlobalTwoForm.omega_torus`, `FullSkeleton.torus_anchor`) and unique
there (`FormExtensionUniqueness.smoothAtlas_twoForm_extension_unique`,
`LocalFormGluing.existsUnique_smooth_gluing`). The skeleton theorem only uses
`Im Ω`, and `docs/target-theorem.md` explicitly excludes holomorphic extension
from the claim. No holomorphic statement is claimed here, and none is proposed
in this mission.

### N4 (no Lean change needed) — the `θ̇ = -K^{-1}∂_u H` form of the flow

The reference's angular equation is written with `K^{-1}`, and it needs
`c_i(K^{-1}x) = -x_i/d_i` to read `η̇_i` and `v̇_i` off `θ̇`. Lean obtains those
two equations directly from the contraction identity, by pairing `Im Ω` against
`TorusLiouvilleDynamics.radialTangent i` and `angularTangent j`
(`angular_equation`, `radial_matrix_equation`), so no inverse of `K` enters
there. The only inversion Lean performs is on the radial components
(`real_logarithmicComponents`, via `Matrix.vecMul_injective_of_isUnit` and
`det B = 1`), which is the reference's componentwise radial law. Nothing is
missing.

### N5 (no Lean change needed) — route to completeness

The reference argues that a maximal integral curve with finite `τ_±` must leave
every compact set, using the coordinate bounds. Lean instead proves
finite-horizon confinement into a compact set chosen before the curve
(`FiniteTimeConfinement.finite_time_compact_confinement`,
`bounded_horizon_closure`) and combines it with a uniform local lifetime on
compacts, obtaining a genuine two-sided `Flow` with joint smoothness
(`NativeCompleteFlow.exists_completeLiouvilleFlow`, `completeFlow`). This is at
least as strong as the reference's conclusion and is what `LiouvilleData`
requires.

### N6 (no Lean change needed) — angular rigidity without the sign of `∂_{u_i}χ_i`

For `i ∈ I∖I_0` the reference shows `|η_i-π|` is nondecreasing, using
`h' ≥ 0`, `h ≤ 0`, `ρ ≥ 0`, `∂_{u_i}χ_i ≤ 0` and `(η-π)β(η) ≥ 0`. Lean splits
this into (a) the deep regime, where the coefficient is **exactly** `1`
(`CompactInteriorRigidity.amplitude_single_deep`,
`characterCoefficient_eq_one_deep`, using `B i i = 0` and
`CompactInteriorRigidity.row_single`), with the monotone-distance argument
`angular_scalar_eq_neg_one_of_tendsto` whose only sign input is
`sin_mul_vartheta_nonneg`/`neg_im_mul_vartheta_arg_nonneg`
(the lift-free form of `(η-π)β(η) ≥ 0`), and (b) backward Gronwall uniqueness on
the compact collar for an **arbitrary continuous** coefficient
(`InteriorPartnerPropagation.angular_scalar_eq_neg_one_of_bounded`,
`angular_scalar_eq_neg_one`, `CompactInteriorRigidity.angular_scalar_eq_neg_one_backward`).
The Lean route therefore needs no sign hypothesis on `∂_{u_i}χ_i` and covers
coefficients of either sign; it is at least as strong in this scope.

### N7 (no Lean change needed) — generic cutoffs versus one explicit family

The reference allows any `h, ρ, β, ϑ` with the listed properties and any
`L > a > 0`. The theorem is an existence statement, so one admissible family
suffices; Lean fixes the explicit family of 1.8, proves each required property
(`PrimitiveCutoffs.*`, `DominanceCutoff.*`) and also records existence lemmas
(`DominanceCutoff.exists_chi`). The quantitative hypothesis `2ε+1 ≤ κ` is the
Lean form of `L > a > 0` with a uniform margin; `FullSkeleton.liouvilleSkeletonTarget`
discharges it with `ε = 1, κ = 3, δ = 1`.

### N8 (no Lean change needed) — angular representative/lift

The reference fixes "the lift in `(-ε,ε)` on this arc". Lean never chooses a
lift: `PrimitiveCutoffs.vartheta δ` is `2π`-periodic
(`vartheta_periodic`, `vartheta_representative_independent`) and is applied to
`Complex.arg (-exchangeCharacter)`, with the sign facts proved through
`Complex.norm_mul_sin_arg` rather than through a branch. This removes a
side condition rather than adding one.

### N9 (no Lean change needed) — `W` and `O` neighborhoods

The reference's `W` (all plateaus active near a divisor point) and `O`
(`z_i ≠ 0`, neighbors not deep) are realized as the open sets
`PrimitiveLocalization.region`/`neighborhood` and
`LocalPrimitive.neighborhood`, with the plateau conclusions
`PrimitiveLocalization.plateaus` and membership `region_mem_nhds`,
`LocalPrimitive.mem_neighborhood`, `covers`. The reference's "by density"
extensions off the torus are performed in Lean by explicit
continuity-plus-density arguments on these open sets
(`EqOn.of_subset_closure` with `InitialTorusDensity.dense_initialTorus`), e.g.
in `BoundaryTangency.nodeLog_drift`, `ZeroStratumInvariance.normSq_drift`,
`NormalizedPartnerNormDrift.normSq_drift`.

---

## 4. Scope statements

* No weighted claim. Nothing in this audit asserts or proposes a theorem for
  `D̃ ≠ I`, for skew-symmetrizable matrices, or for a weighted seed interface.
  The Lean `Seed` is skew-symmetric by construction (`Seed.skew`), and every
  correspondence above is stated with `d_i = 1`, `K = E = B`.
* Mutable acyclicity (`Seed.acyclic`) and variable frozen coordinates
  (`Seed.Point`'s `∀ f ∉ S.mutable, p.a f ≠ 0`) are retained everywhere; no step
  of the audit suggests removing either, and no principal-coefficient assumption
  appears on either side.
* Unimodularity is retained (`Seed.Unimodular`); see N1/G3.
* Holomorphic extension, finite type, cocores and HMS are not claimed (N3).
* The audit is a statement-level comparison. The closures of G1 and G2 added
  no hypothesis, weakened nothing, and changed no existing statement, so every
  scope statement above still holds verbatim for the integrated source; in
  particular the new `lambdaStratum` and `complementRank` declarations are
  stated with `d_i = 1`, `K = E = B`, retain `Seed.acyclic` and the variable
  frozen coordinates, and make no weighted or principal-coefficient claim. The
  build and transitive axiom evidence for the integrated source is recorded in
  [`../verification/README.md`](../verification/README.md).
* Both PDFs and their editable `docs/tex/` sources state the accepted
  stratified skeleton result and explicit torus rank.
