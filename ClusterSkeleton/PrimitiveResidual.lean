import ClusterSkeleton.TorusPrimitive
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The singular/residual splitting in Lemma 2.4, before any cutoff or gluing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.PrimitiveResidual
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Full row: frozen coordinates are included. -/
def tau (i : Fin d) (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p →L[ℝ] ℝ :=
  ∑ j : Fin d, (S.B i j : ℝ) • TorusPrimitive.angleCovector S hdet j p

/-- Full real logarithmic row. -/
def logRow (i : Fin d) (p : S.Point) : ℝ :=
  ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖

/-- Both indices lie outside I. This totalized form is smooth on its stated locus. -/
def residual (I : Finset (Fin d)) : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  covectorForm _ (fun p => ∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ,
    ((S.B i j : ℝ) * Real.log ‖p.a i‖) • TorusPrimitive.angleCovector S hdet j p)

/-- A finite matrix identity, requiring no nonvanishing coordinates. -/
theorem split_sum (I : Finset (Fin d)) (hI : S.Independent I)
    (A T : Fin d → ℝ) :
    (∑ i, ∑ j, (S.B i j : ℝ) * A i * T j) =
      (∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ, (S.B i j : ℝ) * A i * T j) +
      ∑ i ∈ I, ((A i * ∑ j, (S.B i j : ℝ) * T j) -
        (∑ j, (S.B i j : ℝ) * A j) * T i) := by
  let f := fun i j => (S.B i j : ℝ) * A i * T j
  have hs (g : Fin d → ℝ) : (∑ i, g i) = (∑ i ∈ I, g i) + ∑ i ∈ Iᶜ, g i :=
    (Finset.sum_add_sum_compl I g).symm
  have ht : (∑ i ∈ Iᶜ, ∑ j ∈ I, f i j) =
      -(∑ i ∈ I, (∑ j, (S.B i j : ℝ) * A j) * T i) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs (fun j => (S.B i j : ℝ) * A j)]
    have hzero : (∑ j ∈ I, (S.B i j : ℝ) * A j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hI.2 i hi j hj]
    rw [hzero, zero_add, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, S.skew j i, Int.cast_neg]
    ring
  have hr : (∑ i ∈ I, A i * ∑ j, (S.B i j : ℝ) * T j) =
      ∑ i ∈ I, ∑ j, f i j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]; ring
  change (∑ i, ∑ j, f i j) = _
  rw [hs (fun i => ∑ j, f i j)]
  have hc : (∑ i ∈ Iᶜ, ∑ j, f i j) =
      (∑ i ∈ Iᶜ, ∑ j ∈ I, f i j) + (∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ, f i j) := by
    simp_rw [hs (f _)]
    rw [Finset.sum_add_distrib]
  rw [hc, ht, Finset.sum_sub_distrib, hr]
  dsimp [f]
  ring

/-- Exact equality of native forms at every actual exchange point. -/
theorem beta_decomposition (I : Finset (Fin d)) (hI : S.Independent I) :
    TorusPrimitive.beta S hdet = residual S hdet I +
      covectorForm _ (fun p : S.Point => ∑ i ∈ I,
        (Real.log ‖p.a i‖ • tau S hdet i p -
          logRow S i p • TorusPrimitive.angleCovector S hdet i p)) := by
  funext p
  ext v
  simpa [TorusPrimitive.beta, residual, covectorForm, tau, logRow,
    smul_eq_mul] using split_sum S I hI (fun i => Real.log ‖p.a i‖)
      (fun j => TorusPrimitive.angleCovector S hdet j p (v 0))

/-- Complementary coefficients are smooth even when coordinates in I vanish. -/
theorem contDiffAt_residual_inChart (I : Finset (Fin d)) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I),
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (residual S hdet I)) y := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy hp
  let P := SmoothAtlas.presentation S hdet
  let M := P.manifold
  let c := chartAt (Model (2*d)) a
  let q : Model (2*d) → (Fin d → ℂ) := (fun p : S.Point => p.a) ∘ c.symm
  have hq : ContDiffOn ℝ ∞ q c.target :=
    M.contDiffOn_comp_inverseChart (TorusNondegeneracy.original_smooth S P) a
  have hqy := hq.contDiffAt (c.open_target.mem_nhds hy)
  let F := fun z => ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
    (∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ,
      ((S.B i j : ℝ) * Real.log ‖q z i‖) •
        (Complex.imCLM.comp ((q z j)⁻¹ •
          ((ContinuousLinearMap.proj j).comp (fderiv ℝ q z)))))
  have hF : ContDiffAt ℝ ∞ F y := by
    apply (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Model (2*d)) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp y
    apply ContDiffAt.sum; intro i hi
    apply ContDiffAt.sum; intro j hj
    have hi0 : q y i ≠ 0 := hp i (Finset.mem_compl.mp hi)
    have hj0 : q y j ≠ 0 := hp j (Finset.mem_compl.mp hj)
    have hqi := (contDiff_apply ℝ ℂ i).contDiffAt.comp y hqy
    have hqj := (contDiff_apply ℝ ℂ j).contDiffAt.comp y hqy
    apply (contDiffAt_const.mul (ContDiffAt.log (hqi.norm ℂ hi0) (norm_ne_zero_iff.mpr hi0))).smul
    exact contDiffAt_const.clm_comp ((hqj.inv hj0).smul
      (contDiffAt_const.clm_comp (hqy.fderiv_right (by simp))))
  apply hF.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hy] with z hz
  have hdq : (TorusNondegeneracy.originalDifferential S P (c.symm z)).comp
      (M.inverseChartTangentMap a z) = fderiv ℝ q z :=
    M.mfderiv_comp_inverseChart ((TorusNondegeneracy.original_smooth S P).mdifferentiable
      (by simp)) a hz
  ext v
  change (∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ,
    ((S.B i j : ℝ) * Real.log ‖(c.symm z).a i‖) •
      TorusPrimitive.angleCovector S hdet j (c.symm z))
        (M.inverseChartTangentMap a z (v 0)) =
    (∑ i ∈ Iᶜ, ∑ j ∈ Iᶜ,
      ((S.B i j : ℝ) * Real.log ‖q z i‖) •
        (Complex.imCLM.comp ((q z j)⁻¹ •
          ((ContinuousLinearMap.proj j).comp (fderiv ℝ q z))))) (v 0)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hdj : P.coordinateDifferential j (c.symm z)
      (M.inverseChartTangentMap a z (v 0)) = (fderiv ℝ q z (v 0)) j :=
    (TorusNondegeneracy.originalDifferential_apply S P (c.symm z)
      (M.inverseChartTangentMap a z (v 0)) j).symm.trans
        (congrArg (fun L => L (v 0) j) hdq)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.imCLM_apply, ContinuousLinearMap.proj_apply]
  rw [TorusPrimitive.angleCovector_apply, hdj]
  change (S.B i j : ℝ) * Real.log ‖q z i‖ *
    ((fderiv ℝ q z (v 0)) j / q z j).im = _
  rw [div_eq_mul_inv, mul_comm ((fderiv ℝ q z (v 0)) j)]
  rfl

/-- Native Laurent differentiation, with the normalized-node minus sign. -/
theorem hasFDerivAt_log_neg_character
    (i : Fin d) (a : Fin d → ℂ) (ha : ∀ j, a j ≠ 0)
    (hslit : -(∏ j, a j ^ S.B i j) ∈ Complex.slitPlane) :
    HasFDerivAt
      (fun x : Fin d → ℂ => Complex.log (-(∏ j, x j ^ S.B i j)))
      (∑ j : Fin d, (S.B i j : ℂ) •
        ((a j)⁻¹ • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))) a := by
  let χ : (Fin d → ℂ) → ℂ := fun x => ∏ j, x j ^ S.B i j
  let L : (Fin d → ℂ) →L[ℂ] ℂ := ∑ j : Fin d, (S.B i j : ℂ) •
    ((a j)⁻¹ • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))
  have hj (j : Fin d) : HasFDerivAt (fun x : Fin d → ℂ => x j)
      (a j • ((a j)⁻¹ • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))) a := by
    simpa only [smul_smul, mul_inv_cancel₀ (ha j), one_smul] using
      (hasFDerivAt_apply (𝕜 := ℂ) j a)
  have hχ : HasFDerivAt χ (χ a • L) a := by
    apply NodeTwoForm.hasFDerivAt_product_log
    intro j _
    exact NodeTwoForm.hasFDerivAt_zpow_log (hj j) (ha j) (S.B i j)
  have hn : HasFDerivAt (fun x => -χ x) ((-χ a) • L) a := by
    convert hχ.neg using 1
    exact neg_smul (χ a) L
  have hlog := (Complex.hasDerivAt_log hslit).comp_hasFDerivAt a hn
  change HasFDerivAt (fun x => Complex.log (-χ x)) L a
  simpa only [χ, Function.comp_def, smul_smul,
    inv_mul_cancel₀ (Complex.slitPlane_ne_zero hslit), one_smul] using hlog

/-- The branch argument is the negative actual exchange character. -/
theorem node_argument (i : S.Mutable) (p : S.Point) (hp : p ∈ initialTorus S) :
    1 - p.a i * normalizedPartner p i = -(∏ j, p.a j ^ S.B i j) := by
  have hQ : S.negativeMonomial p.a i ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact pow_ne_zero _ (hp j)
  have he : p.a i * normalizedPartner p i = 1 + exchangeCharacter p i := by
    unfold normalizedPartner exchangeCharacter
    rw [← mul_div_assoc, p.exchange i, add_div, div_self hQ, add_comm]
  rw [he, exchangeCharacter_eq_zpow_product]
  ring

/-- The full angular row is the actual native differential of the node logarithm. -/
theorem tau_eq_nodeAngle_differential
    (i : S.Mutable) (p : S.Point) (hp : p ∈ initialTorus S)
    (hlog : 1 - p.a i * normalizedPartner p i ∈ Complex.slitPlane) :
    tau S hdet i p =
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (fun q : S.Point => (Complex.log (1 - q.a i * normalizedPartner q i)).im) p := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  let P := SmoothAtlas.presentation S hdet
  let F := fun a : Fin d → ℂ => (Complex.log (-(∏ j, a j ^ S.B i j))).im
  let L : (Fin d → ℂ) →L[ℂ] ℂ := ∑ j : Fin d, (S.B i j : ℂ) •
    ((p.a j)⁻¹ • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))
  let D := Complex.imCLM.comp (L.restrictScalars ℝ)
  have hF : HasFDerivAt F D p.a :=
    Complex.imCLM.hasFDerivAt.comp p.a
      ((hasFDerivAt_log_neg_character S i p.a hp
        (by rwa [node_argument S i p hp] at hlog)).restrictScalars ℝ)
  have hc := mfderiv_comp p hF.differentiableAt.mdifferentiableAt
    ((TorusNondegeneracy.original_smooth S P p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, hF.fderiv] at hc
  have he : (fun q : S.Point => F q.a) =ᶠ[𝓝 p]
      (fun q : S.Point => (Complex.log (1 - q.a i * normalizedPartner q i)).im) := by
    filter_upwards [(isOpen_initialTorus S).mem_nhds hp] with q hq
    rw [node_argument S i q hq]
  have he' := he.mfderiv_eq (I := 𝓘(ℝ, Model (2*d))) (I' := 𝓘(ℝ, ℝ))
  ext v
  have hh : D (TorusNondegeneracy.originalDifferential S P p v) =
      differentialCovector P.manifold
        (fun q : S.Point => (Complex.log (1 - q.a i * normalizedPartner q i)).im) p v :=
    (congrArg (fun f => f v) hc).symm.trans (congrArg (fun f => f v) he')
  rw [← hh]
  simp [tau, TorusPrimitive.angleCovector_apply, D, L,
    TorusNondegeneracy.originalDifferential_apply,
    div_eq_mul_inv, mul_comm, Complex.mul_im, Complex.mul_re]
  rfl

end ClusterSkeleton.PrimitiveResidual
