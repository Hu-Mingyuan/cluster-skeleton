import ClusterSkeleton.NativeNodePrimitive
import ClusterSkeleton.RegularCorrection
import ClusterSkeleton.LocalFormGluing

/-! The local primitive of Lemma 2.4 on a constructed common open cover. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.LocalPrimitive
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The common domain is constructed from the two accepted open loci. -/
def neighborhood (ε κ δ : ℝ) (p : S.Point) : Set S.Point :=
  PrimitiveLocalization.neighborhood ε κ δ p ∩ NativeNodePrimitive.locus S p.zeroSet

theorem isOpen_neighborhood (ε κ δ : ℝ) (p : S.Point) :
    IsOpen (neighborhood S ε κ δ p) :=
  (PrimitiveLocalization.isOpen_neighborhood ε κ δ p).inter
    (NativeNodePrimitive.isOpen_locus S p.zeroSet p.zeroSet_independent)

/-- Every normalized partner is allowed, including zero. -/
theorem mem_node_locus (p : S.Point) : p ∈ NativeNodePrimitive.locus S p.zeroSet := by
  refine ⟨PrimitiveLocalization.mem_zero_locus p, ?_⟩
  intro i hi
  change (p.a i, normalizedPartner p i) ∈ nodeLogDomain
  rw [show p.a i = 0 from ((Seed.Point.mem_zeroSet p i).mp hi).2]
  exact zero_mem_nodeLogDomain _

theorem mem_neighborhood (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) :
    p ∈ neighborhood S ε κ δ p :=
  ⟨PrimitiveLocalization.mem_neighborhood ε κ hδ p, mem_node_locus S p⟩

theorem neighborhood_subset_localization (ε κ δ : ℝ) (p : S.Point) :
    neighborhood S ε κ δ p ⊆ PrimitiveLocalization.neighborhood ε κ δ p :=
  inter_subset_left

theorem neighborhood_subset_locus (ε κ δ : ℝ) (p : S.Point) :
    neighborhood S ε κ δ p ⊆ NativeNodePrimitive.locus S p.zeroSet :=
  inter_subset_right

theorem covers (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ q : S.Point, ∃ p, q ∈ neighborhood S ε κ δ p :=
  fun q => ⟨q, mem_neighborhood S ε κ hδ q⟩

/-- The actual native residual plus regular node block minus surviving correction. -/
def eta (ε κ δ : ℝ) (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  PrimitiveResidual.residual S hdet p.zeroSet +
    NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent -
    RegularCorrection.regularForm S hdet p.zeroSet ε κ δ

/-- Smoothness in every native chart, only over the constructed domain. -/
theorem locallySmooth_eta (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) :
    LocalFormGluing.LocallySmooth (SmoothAtlas.presentation S hdet).manifold
      (neighborhood S ε κ δ p) (eta S hdet ε κ δ p) := by
  letI := SmoothAtlas.charts S hdet
  intro a y hy hp
  simp only [eta, SmoothManifold.formInChart_sub, SmoothManifold.formInChart_add]
  exact ((PrimitiveResidual.contDiffAt_residual_inChart S hdet p.zeroSet a y hy hp.2.1).add
    (NativeNodePrimitive.contDiffAt_block_inChart S hdet κ p.zeroSet
      p.zeroSet_independent a y hy hp.2)).sub
    (RegularCorrection.regularForm_smooth S hdet p.zeroSet p.zeroSet_independent
      ε κ hδ a y hy hp.2.1)

/-- Each affine germ is differentiable where both its logarithms are defined. -/
theorem mdifferentiableAt_affine (κ : ℝ) {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ NativeNodePrimitive.locus S I) (ht : q ∈ initialTorus S) :
    letI := SmoothAtlas.charts S hdet
    MDifferentiableAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      (PrimitiveLocalization.affineCorrection κ i) q := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  have hT : DifferentiableAt ℝ NodePrimitiveCancellation.T
      (NativeNodePrimitive.nodeMap S i q) :=
    Complex.imCLM.differentiableAt.comp _
      ((NodePrimitiveCancellation.contDiffAt_L (hq.2 i hi)).differentiableAt (by simp))
  have hC : DifferentiableAt ℝ
      (fun r => (NodePrimitiveCancellation.A r + κ) * NodePrimitiveCancellation.T r)
      (NativeNodePrimitive.nodeMap S i q) :=
    ((NodePrimitiveCancellation.hasFDerivAt_A (ht i)).differentiableAt.add_const κ).mul hT
  exact hC.mdifferentiableAt.comp q
    ((NativeNodePrimitive.nodeMap_smooth S hdet hI i hi q hq.1).mdifferentiableAt (by simp))

/-- Reindex the accepted filtered mutable sum without dropping any summand. -/
theorem singularH_eq_sum (I : Finset (Fin d)) (hI : S.Independent I) (κ : ℝ) (q : S.Point) :
    RegularCorrection.singularH I κ q = ∑ i : I,
      PrimitiveLocalization.affineCorrection κ ⟨i.val, hI.1 i.property⟩ q := by
  classical
  unfold RegularCorrection.singularH
  refine Finset.sum_bij
    (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : I))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro j hj k hk h
    exact Subtype.ext (congrArg (fun z : I => z.val) h)
  · intro i _
    refine ⟨⟨i.val, hI.1 i.property⟩, by simp [i.property], ?_⟩
    rfl
  · intro j hj
    rfl

/-- Native addition and finite-sum calculus applied to proved local derivatives. -/
theorem differential_H_eq_sum {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ neighborhood S ε κ δ p) (ht : q ∈ initialTorus S) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) q =
      (∑ i : p.zeroSet, differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (PrimitiveLocalization.affineCorrection κ
          ⟨i.val, p.zeroSet_independent.1 i.property⟩) q) +
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (RegularCorrection.regularH S p.zeroSet ε κ δ) q := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  rw [RegularCorrection.differential_H_split hdet hε hκ hδ hq.1 ht]
  have hr := ((RegularCorrection.contMDiffOn_regularH S hdet p.zeroSet
    p.zeroSet_independent ε κ hδ).contMDiffAt
      ((isOpen_candidateChartLocus S p.zeroSet).mem_nhds hq.2.1)).mdifferentiableAt (by simp)
  have hs := HasMFDerivAt.sum (t := Finset.univ) (fun (i : p.zeroSet) _ =>
    (mdifferentiableAt_affine S hdet κ p.zeroSet_independent
      ⟨i.val, p.zeroSet_independent.1 i.property⟩ i.property q hq.2 ht).hasMFDerivAt)
  have he : RegularCorrection.singularH p.zeroSet κ =
      fun r => ∑ i : p.zeroSet, PrimitiveLocalization.affineCorrection κ
        ⟨i.val, p.zeroSet_independent.1 i.property⟩ r :=
    funext (singularH_eq_sum S p.zeroSet p.zeroSet_independent κ)
  rw [he]
  have hf : (∑ i : p.zeroSet, PrimitiveLocalization.affineCorrection κ
      ⟨i.val, p.zeroSet_independent.1 i.property⟩) =
      fun r => ∑ i : p.zeroSet, PrimitiveLocalization.affineCorrection κ
        ⟨i.val, p.zeroSet_independent.1 i.property⟩ r := by
    funext r
    simp
  rw [hf] at hs
  exact (hs.add hr.hasMFDerivAt).mfderiv

/-- Agreement with the literal torus primitive in the original native fiber. -/
theorem eta_eq_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ neighborhood S ε κ δ p) (ht : q ∈ initialTorus S) :
    eta S hdet ε κ δ p q = TorusCorrection.alpha S hdet ε κ δ q := by
  classical
  have hb := congrFun (PrimitiveResidual.beta_decomposition S hdet p.zeroSet
    p.zeroSet_independent) q
  have hn := NativeNodePrimitive.block_torus S hdet κ p.zeroSet
    p.zeroSet_independent q hq.2 ht
  have hd := differential_H_eq_sum S hdet hε hκ hδ p q hq ht
  ext v
  change (PrimitiveResidual.residual S hdet p.zeroSet q v +
    NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent q v) -
    RegularCorrection.regularForm S hdet p.zeroSet ε κ δ q v = _
  rw [hn]
  change _ = TorusPrimitive.beta S hdet q v -
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) q (v 0)
  rw [hb, hd]
  change PrimitiveResidual.residual S hdet p.zeroSet q v +
      (∑ i : p.zeroSet, (Real.log ‖q.a i.val‖ • PrimitiveResidual.tau S hdet i.val q -
        PrimitiveResidual.logRow S i.val q • TorusPrimitive.angleCovector S hdet i.val q -
        differentialCovector (SmoothAtlas.presentation S hdet).manifold
          (PrimitiveLocalization.affineCorrection κ ⟨i.val, p.zeroSet_independent.1 i.property⟩) q)) (v 0) -
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (RegularCorrection.regularH S p.zeroSet ε κ δ) q (v 0) =
    PrimitiveResidual.residual S hdet p.zeroSet q v +
      (∑ i ∈ p.zeroSet, (Real.log ‖q.a i‖ • PrimitiveResidual.tau S hdet i q -
        PrimitiveResidual.logRow S i q • TorusPrimitive.angleCovector S hdet i q)) (v 0) -
      ((∑ i : p.zeroSet, differentialCovector (SmoothAtlas.presentation S hdet).manifold
          (PrimitiveLocalization.affineCorrection κ ⟨i.val, p.zeroSet_independent.1 i.property⟩) q) +
        differentialCovector (SmoothAtlas.presentation S hdet).manifold
          (RegularCorrection.regularH S p.zeroSet ε κ δ) q) (v 0)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_subtype p.zeroSet (fun _ => Iff.rfl),
    Finset.sum_subtype p.zeroSet (fun _ => Iff.rfl)]
  ring

/-- Arbitrary native tangent evaluation retains the full matrix, including frozen columns. -/
theorem evalOne_eta {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    SmoothManifold.evalOne (eta S hdet ε κ δ p) q v =
      (∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖q.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j q v / q.a j).im) -
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) q v := by
  change eta S hdet ε κ δ p q (fun _ => v) = _
  rw [eta_eq_torus S hdet hε hκ hδ p q hq ht]
  exact TorusCorrection.evalOne_alpha S hdet ε κ δ q v

/-- Simultaneous domain facts used by the local logarithms and normalization. -/
theorem node_domains {ε κ δ : ℝ} {p q : S.Point}
    (hq : q ∈ neighborhood S ε κ δ p) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    S.negativeMonomial q.a i ≠ 0 ∧
    -exchangeCharacter q i = 1 - q.a i * normalizedPartner q i ∧
    (q.a i, normalizedPartner q i) ∈ nodeLogDomain ∧
    -exchangeCharacter q i ∈ Complex.slitPlane ∧
    PrimitiveLocalization.angle q i = (PrimitiveLocalization.nodeLog q i).im ∧
    (q ∈ initialTorus S → PrimitiveLocalization.rowLog q i =
      (PrimitiveLocalization.nodeLog q i).re) :=
  PrimitiveLocalization.node_bridges hq.1 i hi

/-- The local block vanishes at a zero stratum with all normalized partners zero. -/
theorem eta_zero_partners (ε κ δ : ℝ) (p : S.Point)
    (hp : ∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet → normalizedPartner p i = 0) :
    eta S hdet ε κ δ p p = PrimitiveResidual.residual S hdet p.zeroSet p -
      RegularCorrection.regularForm S hdet p.zeroSet ε κ δ p := by
  have hb : NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent p = 0 := by
    ext v
    change (∑ i : p.zeroSet, NativeNodePrimitive.lambda S hdet κ
      ⟨i.val, p.zeroSet_independent.1 i.property⟩ p) (v 0) = 0
    rw [ContinuousLinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [NativeNodePrimitive.lambda_boundary S hdet κ p.zeroSet_independent _ i.property
      p (PrimitiveLocalization.mem_zero_locus p) ((p.mem_zeroSet i.val).mp i.property).2,
      hp _ i.property]
    simp
  change _ + NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent p - _ = _
  rw [hb, add_zero]

/-- The constructed family supplies exactly the open-cover input for later gluing. -/
theorem local_cover {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    (∀ p, IsOpen (neighborhood S ε κ δ p)) ∧
    (∀ q : S.Point, ∃ p, q ∈ neighborhood S ε κ δ p) ∧
    (∀ p, LocalFormGluing.LocallySmooth (SmoothAtlas.presentation S hdet).manifold
      (neighborhood S ε κ δ p) (eta S hdet ε κ δ p)) ∧
    (∀ p q, q ∈ neighborhood S ε κ δ p → q ∈ initialTorus S →
      eta S hdet ε κ δ p q = TorusCorrection.alpha S hdet ε κ δ q) :=
  ⟨isOpen_neighborhood S ε κ δ, covers S ε κ hδ, locallySmooth_eta S hdet ε κ hδ,
    eta_eq_torus S hdet hε hκ hδ⟩

/-- Dense-overlap agreement is ready for the accepted gluing interface. -/
theorem agree_on_torus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p r q : S.Point) (ht : q ∈ initialTorus S)
    (hp : q ∈ neighborhood S ε κ δ p) (hr : q ∈ neighborhood S ε κ δ r) :
    eta S hdet ε κ δ p q = eta S hdet ε κ δ r q :=
  (eta_eq_torus S hdet hε hκ hδ p q hp ht).trans
    (eta_eq_torus S hdet hε hκ hδ r q hr ht).symm

end ClusterSkeleton.LocalPrimitive
