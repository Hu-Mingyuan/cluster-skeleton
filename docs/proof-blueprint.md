> Scope: this guide records the **weighted (skew-symmetrizable)** library at source
> commit `114d63939d72cfb5c81d6bd22dd0811e053805a3`, whose root `ClusterSkeleton`
> builds. The superseded `D = I` baseline survives only in the explicit
> baseline-versus-weighted comparisons of
> [`skeleton-audit.md`](skeleton-audit.md). The accepted-source manifest,
> the verifier run and the receipts for this source are **not yet produced**; see
> *Verification status* in [`target-theorem.md`](target-theorem.md).

# Geometric proof-to-code map

Read the self-contained [proof blueprint PDF](../proof-blueprint.pdf), with
editable source in [`tex/proof-blueprint.tex`](tex/proof-blueprint.tex). The
[target guide](target-theorem.md) separates definitions and formulation from
proofs, and the [audit](skeleton-audit.md) gives the convention-by-convention
correspondence with its sign derivations.

The input is weighted throughout: an integral `E` that is **not** assumed
skew-symmetric, an arbitrary positive rational diagonal `D` with `K = E D̃`
skew-symmetric, acyclic mutable block, variable frozen coordinates,
`det E = 1`. The blueprint's weights are part of the theorem, not shorthand for
`D̃ = I`.

| Step | Mathematical content | Main Lean modules |
| --- | --- | --- |
| Weighted input and linear algebra | Seed fields `E, mutable, D, D_pos, skewSymmetrizable, acyclic`; `K = E D̃` skew; the sign facts `E_diag_zero`, `E_pos_iff_neg`, `E_eq_zero_iff` replacing the baseline's `Seed.skew`; `det K = ∏ d_i` | `Seed`, `SymmetrizerAlgebra`, `SeedAlgebra` |
| Actual exchange space | Nonempty carrier with the reference's **column** monomials `P_i^± = ∏_j z_j^{[±E_ji]_+}`; independent zero indices; monomial node charts of explicit torus rank `d - 2\|I\|`; inherited topology; native atlas | `Seed`, `ZeroSet`, `CoordinateLoci`, `NodeCoordinates`, `IntegralBasisCompletion`, `IndependentNodeChart`, `IndependentNodeSmooth`, `LaurentCoordinates`, `IndependentLaurentCoordinates`, `InitialTorusDensity`, `SmoothAtlas` |
| Global symplectic form, coefficient `K` | Node extension of `Im Ω` with the weighted coefficient and the node block `-d_i/t_i`; overlap compatibility; weighted node nondegeneracy through the blueprint's normal form | `GeometryTarget`, `GlobalTwoForm`, `TorusNondegeneracy`, `NodeTwoForm`, `NodeNondegeneracy`, `LocalFormGluing`, `FormExtensionUniqueness`, `GlobalSymplectic` |
| Global primitive `λ_tor + dH` | Explicit smooth cutoffs; `λ_tor = u^T K dθ`; `H` with the factor `d_i` in each summand; `alpha = beta + dH`; singular-term cancellation with the per-node weight; gluing and exterior derivative | `PrimitiveCutoffs`, `DominanceCutoff`, `TorusPrimitive`, `PrimitiveResidual`, `TorusCorrection`, `PrimitiveLocalization`, `RegularCorrection`, `NodeLogExtension`, `NodePrimitiveCancellation`, `NativeNodePrimitive`, `LocalPrimitive`, `GlobalPrimitive` |
| Weighted identities | `K e_i = d_i c_i`, `∑_j K_{ji} u_j = d_i v_i`, `∑_l K_{il} θ_l = -d_i η_i`, `c_i^T K^{-1} = -e_i^T/d_i`, `d_i B_{ij} = -K_{ij}`, and the inverse bounds that replace `det B = 1` | `SymmetrizerAlgebra`, `SeedAlgebra` |
| Complete flow | Actual Liouville field; radial equation with the weights cancelled and angular equation with `1/d_i`; all-strata bounds through `K⁻¹`; finite-time confinement; two-sided native integral curves | `TorusLiouvilleDynamics`, `GlobalLiouvilleField`, `LocalAngularDynamics`, `NativeRadialOrbit`, `AllStrataGrowth`, `ScalarOrbitDynamics`, `FiniteTimeConfinement`, `NativeCompleteFlow` |
| Cap is trapped | Compactness and forward invariance, including zero strata; the node-rate statements `Z\|z_i\|² = -2κ\|z_i\|²` and `Z\|y_i\|² = 2(1+κ)\|y_i\|²`, both weight-free | `CapSet`, `CapIndependence`, `BoundaryTangency`, `CapAngularTangency`, `ZeroStratumInvariance`, `ZeroStratumPartnerDynamics`, `NormalizedPartnerNormDrift`, `InteriorPartnerPropagation`, `CapForwardInvariance`, `ConstructedFlowCapInclusion` |
| Trapped points lie in cap | Radial escape, interior partner rigidity, zero-stratum partner escape | `CompactInteriorRigidity`, `ZeroStratumEscape`, `ConstructedFlowReverseInclusion` |
| Stratified cap | The cap as the union of the reference strata `Λ_I` over independent `I`; closedness and per-stratum compactness | `CapStrata` |
| Final existence | Same-flow set equality, its stratified form, and constructed witnesses, for every weighted seed | `FullSkeleton` |
| `D = I` recovery | The old skew-symmetric input, its weighted reading `E := B`, `D := 1` (so `K = B`), the carrier identity and the old loci on the old carrier | `SkewSeed`; `SkewSeedRecovery` (at commit `e7a6d963…`, see below) |
| Inputs the theorem must accept | The weighted `A_2` seed with `D = 1` and the reference's non-skew `4 × 4` input | `Examples.A2`, `Examples.NonSkew` |

The final theorem is `ClusterSkeleton.FullSkeleton.firstGeometricTarget`:

```lean
def ClusterSkeleton.FirstGeometricTarget : Prop :=
  ∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S
```

Both inclusions concern the same `NativeCompleteFlow.completeFlow`.

## The weighted identities, and where each weight goes

The blueprint's `K e_i = d_i c_i` and `c_i^T K^{-1} = -e_i^T/d_i` are the two
identities that explain the cancellations. In Lean they are
`SeedAlgebra.K_mulVec_single` and `SeedAlgebra.c_inv_K` (matrix forms
`SeedAlgebra.vecMul_Ecol_inv_Kreal`, `SeedAlgebra.Breal_mulVec_inv_K`), with the
`SymmetrizerAlgebra` originals `SymmetrizerAlgebra.K_mulVec_single` and
`SymmetrizerAlgebra.vecMul_E_col_inv_K` proved for an arbitrary field. The
scalar identity that drives every migration site is

```lean
theorem SeedAlgebra.K_eq_neg_D_mul_B (i j : Fin d) :
    (S.K i j : ℝ) = -(S.D i : ℝ) * (S.B i j : ℝ)        -- K_{ij} = -d_i B_{ij}
```

Consequently:

* `λ_tor` and the two-form carry `K` (`TorusPrimitive.beta`,
  `GlobalTwoForm.matrixForm`, `PrimitiveResidual.residual`,
  `TorusNondegeneracy.complexMatrix`, `NodeTwoForm.outsideBlock`);
* the **exponent / character** rows keep `S.B = S.Eᵀ`, because `S.B i j` *is*
  `c_i`'s coefficient `E_{ji}` (`TorusCorrection.rowLog`,
  `PrimitiveResidual.tau`/`logRow`, `DominanceCutoff.mutableNeighbors`);
* each summand of `H` gains `d_i` (`TorusCorrection.H`,
  `RegularCorrection.regularH`/`singularH`, `NativeNodePrimitive.block`,
  `TorusLiouvilleDynamics.differential_H`, `LocalAngularDynamics.angularRhs`),
  while the per-index scalars `PrimitiveLocalization.correction` and
  `PrimitiveLocalization.affineCorrection` stay **unweighted** and every consumer
  supplies the weight;
* the radial equations keep the baseline shape, because `d_i B_{ij} = -K_{ij}`
  absorbs the weight before the `K^T` cancellation
  (`TorusLiouvilleDynamics.radial_matrix_equation`,
  `mutable_radial_equation`, `frozen_radial_equation`);
* the weight survives in the **angular** equation only, as `η̇_i = (1/d_i) ∂_{u_i} H`
  (`TorusLiouvilleDynamics.angular_equation_row`,
  `AllStrataGrowth.row_nu_equation`);
* every matrix inversion in the dynamics is of `SeedAlgebra.Kreal` and uses only
  `SeedAlgebra.isUnit_det_Kreal` (`det K = ∏ d_i`, *not* `1`):
  `TorusLiouvilleDynamics.real_logarithmicComponents`,
  `TorusLiouvilleDynamics.full_matrix_inverse_bound` (now one term,
  `SeedAlgebra.exists_inverse_bound_Kreal`), `LocalAngularDynamics.nu`,
  `AllStrataGrowth.full_matrix_nu_equation`. The integer inverse of `E` keeps
  `det = 1` and is unweighted: `Seed.B_det`, `SeedAlgebra.det_Breal`,
  `SeedAlgebra.exists_inverse_bound_Breal`.

Audit §1.5–§1.7 derives each of these from the reference formulas, and §1.10
tabulates them against the baseline.

## The weighted node nondegeneracy

The blueprint does not get nondegeneracy from density: it writes the form in the
node coordinates `(x_i, t_i, s_a)`, where

```
Ω = Σ_{i∈I} d_i dlog t_i ∧ dlog x_i + Ω_0(t,s)
```

because `Σ_j K_{ij} dlog z_j = -d_i dlog t_i`, and eliminates the first two block
rows of

```
( 0    -D_I   0  )
( D_I   A     B_0)
( 0    -B_0ᵀ  C  )
```

In Lean the node coefficient is `NodeTwoForm.complexForm` with the entry
`-(S.D i : ℂ) * (rawParameters S I x (Sum.inl i))⁻¹`, the `x_i` row is
`NodeTwoForm.row_outsideLog_weighted`, the normal form is
`NodeNondegeneracy.normalMatrix` built from `NodeNondegeneracy.weightProjection`
(entry `-(S.D i : ℂ)` on the diagonal), the elimination is
`SymmetrizerAlgebra.residualBlock_eq_zero_of_mulVec_eq_zero` with `δ i ≠ 0` from
`Seed.D_pos`, and the three pairings are
`NodeNondegeneracy.complexForm_boundary_nondegenerate` in the blueprint's order.
Nondegeneracy is then claimed at **every** point of `Seed.Point`
(`GlobalSymplectic.nondegenerate_omega`,
`GlobalSymplectic.isSymplecticOn_omega` on `Set.univ`), the zero locus included,
via each point's own chart (`NodeNondegeneracy.zeroSet_localForm_nondegenerate`,
`GlobalTwoForm.omega_eq_localForm`).

## The stratified form of the skeleton

`ClusterSkeleton.lambdaStratum S I` is the reference's stratum
`Λ_I = {b_i = 0, ‖a_i‖ ≤ 1 (mutable i ∈ I), ‖a_j‖ = 1 (j ∉ I)}` on the actual
exchange points, in [`CapStrata.lean`](../ClusterSkeleton/CapStrata.lean). It is
purely ambient, hence unaffected by the convention change. Two theorems there
identify it with the independently defined cap:

- `coordinateCap_eq_iUnion_lambdaStratum : coordinateCap S = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val`,
  via `lambdaStratum_subset_coordinateCap` and
  `coordinateCap_subset_lambdaStratum_strictCapIndices` (the stratum realized by
  a cap point is indexed by `Seed.Point.strictCapIndices`, independent by
  `coordinateCap_strictCapIndices_independent`);
- `isClosed_lambdaStratum` and `isCompact_lambdaStratum`, the reference's
  per-stratum compactness.

Composing with the equality for the same constructed flow gives the reference's
stratified skeleton identity verbatim:

```lean
theorem FullSkeleton.trappedSet_eq_iUnion_lambdaStratum :
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val
```

Independence is used only to index the union by the same family the reference
uses; neither inclusion needs it.

The node charts carry the reference's explicit torus exponent: for independent
`I`, `ClusterSkeleton.IndependentNodeChart.complementRank_eq_sub_two_mul_card`
proves `SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card`,
so `IndependentNodeChart.homeomorph` lands in
`({i // i ∈ I} → Node) × (ℂ*)^(d - 2|I|)`, with
`IndependentNodeChart.two_mul_card_le : 2 * I.card ≤ d`. Both are in
[`IndependentNodeSmooth.lean`](../ClusterSkeleton/IndependentNodeSmooth.lean),
and in the weighted setting their input
`independent_rows_inverse_pairing` is the blueprint statement itself (the rows of
`S.B = S.Eᵀ` indexed by `I` are the reference columns `c_i = E e_i`).

## `D = I` recovery

`ClusterSkeleton/SkewSeed.lean` holds the old skew-symmetric input `SkewSeed`
(fields `B`, `mutable`, `skew`, `acyclic`) and its weighted reading
`SkewSeed.toSeed` with `E := B`, `D := 1`. The pivotal identity is
`SkewSeed.toSeed_K : (S.toSeed).K i j = (S.B i j : ℚ)` — the weighted form
coefficient at `D = 1` is the old integer matrix with **no** sign change, so the
recovered Liouville field is not time-reversed and the forward-orbit trapped set
is the old one. The carriers coincide as sets (`SkewSeed.carrier_set_eq`, the two
monomials swap and only their sum is used:
`SkewSeed.toSeed_monomial_sum`) and the canonical identification is
`SkewSeed.pointHomeomorph` with `SkewSeed.pointHomeomorph_val` by `rfl`.

The statement of recovery — the old loci `SkewSeed.initialTorus`,
`SkewSeed.coordinateCap`, `SkewSeed.lambdaStratum` on the old carrier, their
image/preimage identifications, the flow conjugation `SkewSeed.conjFlow` and
`SkewSeed.trappedSet_conjFlow_eq_coordinateCap` — is the module
`ClusterSkeleton/SkewSeedRecovery.lean` at commit
`e7a6d9637ac0acec71639a71731f1d6ca27e2e0c`, documented in
[`weighted-recovery-plan.md`](weighted-recovery-plan.md). It is **not** part of
the tree at `114d639`; the final-assembly mission imports it and adds the single
instantiation clause. Audit §1.11 records which clauses are proved, which one is
outstanding, and the recorded decision not to claim a transported smooth
structure.

## Verification status

[`FullSkeletonConsumer.lean`](../verification/FullSkeletonConsumer.lean) and the
rest of [`verification/`](../verification) still bind the superseded baseline
commit `4c02c1e5bbc68907552632344ae04017d82a30b4`. The weighted library builds at
`114d63939d72cfb5c81d6bd22dd0811e053805a3` with the pinned toolchain
(Lean 4.34.1 / Lake 5.0.0). The accepted-source manifest, the weighted verifier
run with its module and declaration counts, the transitive axiom log and the
receipts for this source are **not yet produced**; the closing verification
mission produces them and finalizes this section together with the
corresponding sections of [`target-theorem.md`](target-theorem.md) and
[`skeleton-audit.md`](skeleton-audit.md).

The rewritten PDFs contain only the relevant weighted geometry. They prove a
real smooth extension of the imaginary weighted logarithmic form; later
finite-type, cocore, and categorical statements from the original notes are not
included.
