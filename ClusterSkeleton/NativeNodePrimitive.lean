import ClusterSkeleton.PrimitiveResidual
import ClusterSkeleton.NodePrimitiveCancellation
import ClusterSkeleton.PrimitiveLocalization

/-! The regular singular block of Lemma 2.4 on actual exchange points. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.NativeNodePrimitive
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The existing raw normalized pair; no change of node coordinates. -/
def nodeMap (i : S.Mutable) (q : S.Point) : ℂ × ℂ :=
  (q.a i, normalizedPartner q i)

/-- The independent coordinate locus intersected with all principal-log preimages. -/
def locus (I : Finset (Fin d)) : Set S.Point :=
  candidateChartLocus S I ∩ {q | ∀ i : S.Mutable, (i : Fin d) ∈ I →
    nodeMap S i q ∈ nodeLogDomain}

/-- The normalization divides only by the proved nonzero exchange monomial. -/
theorem nodeMap_smooth {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) :
    letI := SmoothAtlas.charts S hdet
    ∀ q ∈ candidateChartLocus S I,
      ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ × ℂ) ∞ (nodeMap S i) q := by
  letI := SmoothAtlas.charts S hdet
  intro q hq
  let F : (Fin d → ℂ) × (S.Mutable → ℂ) → ℂ × ℂ :=
    fun x => (x.1 i, x.2 i / S.negativeMonomial x.1 i)
  have hF : ContDiffAt ℂ ∞ F q.val := by
    apply ContDiffAt.prodMk
    · exact (contDiff_apply ℂ ℂ i.val).contDiffAt.comp _ contDiffAt_fst
    · apply ContDiffAt.div
      · exact (contDiff_apply ℂ ℂ i).contDiffAt.comp _ contDiffAt_snd
      · apply contDiffAt_prod
        intro j _
        exact ((contDiff_apply ℂ ℂ j).contDiffAt.comp _ contDiffAt_fst).pow _
      · exact negativeMonomial_ne_zero_on_independent_locus hI hq hi
  exact (hF.restrict_scalars ℝ).contMDiffAt.comp q (SmoothAtlas.inclusion_smooth S hdet q)

theorem isOpen_locus (I : Finset (Fin d)) (hI : S.Independent I) :
    IsOpen (locus S I) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hn : ∀ i : S.Mutable, ∀ hi : (i : Fin d) ∈ I,
      ∀ᶠ p in 𝓝 q, nodeMap S i p ∈ nodeLogDomain := by
    intro i hi
    exact ((continuous_originalCoordinate S i).continuousAt.prodMk
      (PrimitiveLocalization.continuousAt_normalizedPartner hI hq.1 i hi)).preimage_mem_nhds
        (isOpen_nodeLogDomain.mem_nhds (hq.2 i hi))
  have hall : ∀ᶠ p in 𝓝 q, ∀ i : S.Mutable, (i : Fin d) ∈ I →
      nodeMap S i p ∈ nodeLogDomain := by
    exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hn i))
  exact Filter.inter_mem ((isOpen_candidateChartLocus S I).mem_nhds hq.1) hall

/-- The actual native differential of the raw normalized pair. -/
def nodeDifferential (i : S.Mutable) (q : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent q →L[ℝ] (ℂ × ℂ) := by
  letI := SmoothAtlas.charts S hdet
  exact mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ × ℂ) (nodeMap S i) q

/-- Pullback of the accepted regular Euclidean node covector. -/
def lambda (κ : ℝ) (i : S.Mutable) (q : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent q →L[ℝ] ℝ :=
  (NodePrimitiveCancellation.lambda κ (nodeMap S i q)).comp (nodeDifferential S hdet i q)

/-- The simultaneous regular singular block as a native alternating one-form.
Each node summand carries the common symmetrizer factor `d_i`, exactly as the
`I`-block of `eq:acyclic-ltor-split` and of the weighted correction do. -/
def block (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I) :
    (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  covectorForm _ (fun q => ∑ i : I,
    (S.D i.val : ℝ) • lambda S hdet κ ⟨i.val, hI.1 i.property⟩ q)

/-- Tangent transport uses the native chain rule in every chart. -/
theorem nodeDifferential_inChart {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I),
      (nodeDifferential S hdet i ((chartAt (Model (2*d)) a).symm y)).comp
        ((SmoothAtlas.presentation S hdet).manifold.inverseChartTangentMap a y) =
      fderiv ℝ (nodeMap S i ∘ (chartAt (Model (2*d)) a).symm) y := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy hp
  have hc := mfderiv_comp y
    ((nodeMap_smooth S hdet hI i hi _ hp).mdifferentiableAt (by simp))
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2*d))) a).mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at hc
  exact hc.symm

/-- Smooth coefficients at all inverse-chart points in the stated open locus. -/
theorem contDiffAt_block_inChart (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ locus S I),
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (block S hdet κ I hI)) y := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy hp
  let c := chartAt (Model (2*d)) a
  let F := fun z => ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
    (∑ i : I, (S.D i.val : ℝ) • (NodePrimitiveCancellation.lambda κ
      (nodeMap S ⟨i.val, hI.1 i.property⟩ (c.symm z))).comp
      (fderiv ℝ (nodeMap S ⟨i.val, hI.1 i.property⟩ ∘ c.symm) z))
  have hF : ContDiffAt ℝ ∞ F y := by
    apply (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Model (2*d)) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp y
    apply ContDiffAt.sum
    intro i _
    have hc : ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Model (2*d)) ∞ c.symm y :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2*d))) (x := a)).contMDiffAt
        (c.open_target.mem_nhds hy)
    have hf := ((nodeMap_smooth S hdet hI ⟨i.val, hI.1 i.property⟩ i.property _ hp.1).comp y hc).contDiffAt
    refine ContDiffAt.const_smul (S.D i.val : ℝ) ?_
    exact ((NodePrimitiveCancellation.contDiffAt_lambda κ (hp.2 _ i.property)).comp y hf).clm_comp
      (hf.fderiv_right (by simp))
  apply hF.congr_of_eventuallyEq
  have hn := (c.continuousAt_symm hy).preimage_mem_nhds
    ((isOpen_candidateChartLocus S I).mem_nhds hp.1)
  filter_upwards [c.open_target.mem_nhds hy, hn] with z hz hzp
  ext v
  change (∑ i : I, (S.D i.val : ℝ) • lambda S hdet κ ⟨i.val, hI.1 i.property⟩ (c.symm z))
    ((SmoothAtlas.presentation S hdet).manifold.inverseChartTangentMap a z (v 0)) = _
  change (∑ i : I, (S.D i.val : ℝ) • lambda S hdet κ ⟨i.val, hI.1 i.property⟩ (c.symm z))
    ((SmoothAtlas.presentation S hdet).manifold.inverseChartTangentMap a z (v 0)) =
    (∑ i : I, (S.D i.val : ℝ) • (NodePrimitiveCancellation.lambda κ
      (nodeMap S ⟨i.val, hI.1 i.property⟩ (c.symm z))).comp
      (fderiv ℝ (nodeMap S ⟨i.val, hI.1 i.property⟩ ∘ c.symm) z)) (v 0)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hd := nodeDifferential_inChart S hdet hI ⟨i.val, hI.1 i.property⟩ i.property a z hz hzp
  exact congrArg (fun x : ℝ => (S.D i.val : ℝ) * x)
    (congrArg (fun D => NodePrimitiveCancellation.lambda κ
      (nodeMap S ⟨i.val, hI.1 i.property⟩ (c.symm z)) (D (v 0))) hd)

/-- The first component of the derivative is the original coordinate differential. -/
theorem nodeDifferential_fst {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    (nodeDifferential S hdet i q v).1 =
      (SmoothAtlas.presentation S hdet).coordinateDifferential i q v := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  have hc := mfderiv_comp q
    ((ContinuousLinearMap.fst ℝ ℂ ℂ).differentiableAt.mdifferentiableAt)
    ((nodeMap_smooth S hdet hI i hi q hq).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hc
  exact (congrArg (fun D => D v) hc).symm

/-- All zero-divisor tangent values, including a zero normalized partner. -/
theorem lambda_boundary (κ : ℝ) {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) (ha : q.a i = 0)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    lambda S hdet κ i q v = (1 + κ) *
      (normalizedPartner q i * (SmoothAtlas.presentation S hdet).coordinateDifferential i q v).im := by
  change NodePrimitiveCancellation.lambda κ (q.a i, normalizedPartner q i)
    (nodeDifferential S hdet i q v) = _
  rw [ha, NodePrimitiveCancellation.lambda_zero, nodeDifferential_fst S hdet hI i hi q hq v]

/-- Scalar pullback uses the actual native chain rule, with local differentiability. -/
theorem pullback_differential {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) (f : (ℂ × ℂ) → ℝ)
    (hf : DifferentiableAt ℝ f (nodeMap S i q)) :
    (fderiv ℝ f (nodeMap S i q)).comp (nodeDifferential S hdet i q) =
      differentialCovector (SmoothAtlas.presentation S hdet).manifold (f ∘ nodeMap S i) q := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  have hc := mfderiv_comp q hf.mdifferentiableAt
    ((nodeMap_smooth S hdet hI i hi q hq).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  exact hc.symm

/-- The real node logarithm is the full row, including frozen columns. -/
theorem node_real_logRow {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) (ht : q ∈ initialTorus S) :
    NodePrimitiveCancellation.S (nodeMap S i q) = PrimitiveResidual.logRow S i q := by
  have h := PrimitiveLocalization.rowLog_eq_log_re ht i.val
  rw [PrimitiveLocalization.neg_character_node hI hq i hi] at h
  exact h.symm

/-- Exact torus cancellation in the actual native tangent fiber. -/
theorem lambda_torus (κ : ℝ) {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ locus S I) (ht : q ∈ initialTorus S) :
    lambda S hdet κ i q =
      Real.log ‖q.a i‖ • PrimitiveResidual.tau S hdet i q -
      PrimitiveResidual.logRow S i q • TorusPrimitive.angleCovector S hdet i q -
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (fun p : S.Point => (Real.log ‖p.a i‖ + κ) * (PrimitiveLocalization.nodeLog p i).im) q := by
  have hp := hq.2 i hi
  have hT : DifferentiableAt ℝ NodePrimitiveCancellation.T (nodeMap S i q) :=
    Complex.imCLM.differentiableAt.comp _
      ((NodePrimitiveCancellation.contDiffAt_L hp).differentiableAt (by simp))
  have hC : DifferentiableAt ℝ
      (fun p => (NodePrimitiveCancellation.A p + κ) * NodePrimitiveCancellation.T p)
      (nodeMap S i q) :=
    ((NodePrimitiveCancellation.hasFDerivAt_A (ht i)).differentiableAt.add_const κ).mul hT
  have hdt := pullback_differential S hdet hI i hi q hq.1 _ hT
  have hdc := pullback_differential S hdet hI i hi q hq.1 _ hC
  have hrow := PrimitiveResidual.tau_eq_nodeAngle_differential S hdet i q ht hp
  have hreal := node_real_logRow S hI i hi q hq.1 ht
  ext v
  have hc := congrArg (fun D => D (nodeDifferential S hdet i q v))
    (NodePrimitiveCancellation.cancellation κ hp (ht i)).symm
  change NodePrimitiveCancellation.lambda κ (nodeMap S i q)
    (nodeDifferential S hdet i q v) = _
  rw [hc]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have htval : fderiv ℝ NodePrimitiveCancellation.T (nodeMap S i q)
      (nodeDifferential S hdet i q v) = PrimitiveResidual.tau S hdet i q v := by
    exact (congrArg (fun D => D v) hdt).trans (congrArg (fun D => D v) hrow.symm)
  have hcval := congrArg (fun D => D v) hdc
  simp only [ContinuousLinearMap.comp_apply] at hcval
  rw [htval, hreal, hcval]
  congr 2
  simp only [NodePrimitiveCancellation.dtheta, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, NodePrimitiveCancellation.du,
    Complex.imCLM_apply, smul_eq_mul]
  change PrimitiveResidual.logRow S i q *
    ((q.a i)⁻¹ * (nodeDifferential S hdet i q v).1).im = _
  rw [nodeDifferential_fst S hdet hI i hi q hq.1 v]
  rfl

/-- The finite sum agrees as a native alternating form, not just in chosen coordinates. -/
theorem block_torus (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I)
    (q : S.Point) (hq : q ∈ locus S I) (ht : q ∈ initialTorus S) :
    block S hdet κ I hI q =
      covectorForm (SmoothAtlas.presentation S hdet).manifold
        (fun p => ∑ i : I, (S.D i.val : ℝ) •
          (Real.log ‖p.a i.val‖ • PrimitiveResidual.tau S hdet i.val p -
          PrimitiveResidual.logRow S i.val p • TorusPrimitive.angleCovector S hdet i.val p -
          differentialCovector (SmoothAtlas.presentation S hdet).manifold
            (fun r : S.Point => (Real.log ‖r.a i.val‖ + κ) *
              (PrimitiveLocalization.nodeLog r ⟨i.val, hI.1 i.property⟩).im) p)) q := by
  unfold block covectorForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L => (S.D i.val : ℝ) • L)
    (lambda_torus S hdet κ hI ⟨i.val, hI.1 i.property⟩ i.property q hq ht)

@[simp] theorem block_empty (κ : ℝ) (hI : S.Independent ∅) :
    block S hdet κ ∅ hI = 0 := by
  funext q
  ext v
  simp [block, covectorForm]

end ClusterSkeleton.NativeNodePrimitive
