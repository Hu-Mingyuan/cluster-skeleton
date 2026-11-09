import ClusterSkeleton.NodeTwoForm
import FsFltz.Geometry.ExteriorDerivative
import FsFltz.Geometry.SmoothForms
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Native compatibility and gluing of the accepted node forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.GlobalTwoForm

-- The two-argument currying proof is adapted from the pinned FsFltz
-- IntrinsicNativeCompletionFamilyExteriorGerms theorem of the same purpose.
theorem contDiffAt_twoForm_compContinuousLinearMap
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x : X} {η : X → F [⋀^Fin 2]→L[ℝ] ℝ} {B : X → E →L[ℝ] F}
    (hη : ContDiffAt ℝ ∞ η x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (fun p => (η p).compContinuousLinearMap (B p)) x := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let cF := (ContinuousAlternatingMap.curryLeftLI
    (𝕜 := ℝ) (E := F) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hc := (ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := F [⋀^Fin 2]→L[ℝ] ℝ) (F := F →L[ℝ] F [⋀^Fin 1]→L[ℝ] ℝ) cF).contDiffAt.comp x hη
  have hLF : ContDiffAt ℝ ∞ (fun _ : X => eF.symm.toContinuousLinearMap) x :=
    contDiffAt_const
  have hd := hLF.clm_comp (hc.clm_comp hB)
  have hf := (LinearIsometryEquiv.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] F →L[ℝ] ℝ) (F := F →L[ℝ] E →L[ℝ] ℝ)
    (ContinuousLinearMap.flipₗᵢ ℝ E F ℝ)).contDiffAt.comp x hd
  have hb := (LinearIsometryEquiv.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)).contDiffAt.comp x
    (hf.clm_comp hB)
  have hLE : ContDiffAt ℝ ∞ (fun _ : X => eE.toContinuousLinearMap) x := contDiffAt_const
  have ha := hLE.clm_comp hb
  have heq : (fun p => eE.toContinuousLinearMap ∘L
      (((eF.symm.toContinuousLinearMap ∘L (cF (η p) ∘L B p)).flip ∘L B p).flip)) =
      (fun p => ((η p).compContinuousLinearMap (B p)).curryLeft) := by
    funext p
    ext v vs
    change η p (Matrix.vecCons (B p v) (fun _ : Fin 1 => B p (vs 0))) =
      η p (fun j => B p (Matrix.vecCons v vs j))
    congr 1
    funext j
    fin_cases j <;> rfl
  change ContDiffAt ℝ ∞ (fun p => eE.toContinuousLinearMap ∘L
    (((eF.symm.toContinuousLinearMap ∘L (cF (η p) ∘L B p)).flip ∘L B p).flip)) x at ha
  rw [heq] at ha
  have hs := ((ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) (F := E [⋀^Fin 2]→L[ℝ] ℝ)
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ (n := 1))).contDiffAt.comp x ha).const_smul (1 / 2 : ℝ)
  convert hs using 1
  funext p
  simp only [Function.comp_apply, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num


variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable (I : Finset (Fin d)) (hI : S.Independent I)
open IndependentNodeChart hiding Model
open NodeTwoForm

/-- Native coefficients of the node pullback in any manifold chart. -/
theorem localForm_inChart :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
    (hy : y ∈ (chartAt (Model (2*d)) a).target)
    (hp : (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I),
    (SmoothAtlas.presentation S hdet).manifold.formInChart a (localForm S I hdet hI) y =
      (realForm S I hdet hI ((SmoothAtlas.rawChart S hdet I hI)
        ((chartAt (Model (2*d)) a).symm y))).compContinuousLinearMap
        (fderiv ℝ ((SmoothAtlas.rawChart S hdet I hI) ∘
          (chartAt (Model (2*d)) a).symm) y) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy hp
  have hc := mfderiv_comp y
    ((chart_smooth S I hdet hI _ hp).mdifferentiableAt (by simp))
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2*d))) a).mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at hc
  rw [hc]
  rfl

/-- Local smoothness includes the actual derivative of the transition to a
fixed native manifold chart. No global smoothness is assumed here. -/
theorem contDiffAt_localForm_inChart :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I),
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (localForm S I hdet hI)) y := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy hp
  let c := chartAt (Model (2*d)) a
  let f := (SmoothAtlas.rawChart S hdet I hI) ∘ c.symm
  have hc : ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Model (2*d)) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2*d))) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hf : ContDiffAt ℝ ∞ f y :=
    ((chart_smooth S I hdet hI _ hp).comp y hc).contDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (realForm S I hdet hI) (f y) :=
    (contDiffOn_realForm S I hdet hI).contDiffAt
      ((isOpen_domain S I).mem_nhds ((SmoothAtlas.rawChart S hdet I hI).map_source hp))
  have hs := contDiffAt_twoForm_compContinuousLinearMap
    (hcoeff.comp y hf) (hf.fderiv_right (by simp))
  apply hs.congr_of_eventuallyEq
  have hn := (c.continuousAt_symm hy).preimage_mem_nhds
    ((isOpen_candidateChartLocus S I).mem_nhds hp)
  filter_upwards [c.open_target.mem_nhds hy, hn] with z hz hzp
  exact localForm_inChart S hdet I hI a z hz hzp

/-- Fixed native chart coefficients are continuous on the local source. -/
theorem continuousOn_localForm_coefficients :
    letI := SmoothAtlas.charts S hdet
    ∀ a : S.Point,
      ContinuousOn (fun p => (SmoothAtlas.presentation S hdet).manifold.formInChart
        a (localForm S I hdet hI) (chartAt (Model (2*d)) a p))
        ((chartAt (Model (2*d)) a).source ∩ candidateChartLocus S I) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a p hp
  have hi : (chartAt (Model (2*d)) a).symm (chartAt (Model (2*d)) a p) ∈
      candidateChartLocus S I := by
    rw [(chartAt (Model (2*d)) a).left_inv hp.1]
    exact hp.2
  exact ((contDiffAt_localForm_inChart S hdet I hI a _
    ((chartAt (Model (2*d)) a).map_source hp.1) hi).continuousAt.comp
    ((chartAt (Model (2*d)) a).continuousAt hp.1)).continuousWithinAt

/-- Agreement on the torus is equality in the actual native tangent fiber. -/
theorem localForm_eq_on_torus (J : Finset (Fin d)) (hJ : S.Independent J)
    (p : S.Point) (hp : p ∈ initialTorus S) :
    localForm S I hdet hI p = localForm S J hdet hJ p := by
  apply FormExtensionUniqueness.twoForm_fiber_ext (SmoothAtlas.presentation S hdet).manifold
    (omega := localForm S I hdet hI) (eta := localForm S J hdet hJ) p
  intro v w
  rw [localForm_torus S I hdet hI p hp, localForm_torus S J hdet hJ p hp]

/-- Density is used only for continuous coefficients on an open overlap.
Native inverse-chart cancellation returns equality in the tangent fiber. -/
theorem localCompatibility : NodeTwoForm.LocalCompatibility S I hdet hI := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro J hJ p hpI hpJ
  let M := (SmoothAtlas.presentation S hdet).manifold
  let e := chartAt (Model (2*d)) p
  let U := (e.source ∩ candidateChartLocus S I) ∩ candidateChartLocus S J
  have hU : IsOpen U := (e.open_source.inter (isOpen_candidateChartLocus S I)).inter
    (isOpen_candidateChartLocus S J)
  have hcontI : ContinuousOn (fun q => M.formInChart p (localForm S I hdet hI) (e q)) U :=
    (continuousOn_localForm_coefficients S hdet I hI p).mono inter_subset_left
  have hcontJ : ContinuousOn (fun q => M.formInChart p (localForm S J hdet hJ) (e q)) U :=
    (continuousOn_localForm_coefficients S hdet J hJ p).mono (fun q hq => ⟨hq.1.1,hq.2⟩)
  have htor : EqOn (fun q => M.formInChart p (localForm S I hdet hI) (e q))
      (fun q => M.formInChart p (localForm S J hdet hJ) (e q)) (U ∩ initialTorus S) := by
    intro q hq
    have ht : e.symm (e q) ∈ initialTorus S := by
      rw [e.left_inv hq.1.1.1]
      exact hq.2
    exact congrArg (fun f => f.compContinuousLinearMap (M.inverseChartTangentMap p (e q)))
      (localForm_eq_on_torus S hdet I hI J hJ _ ht)
  have hd : U ⊆ closure (U ∩ initialTorus S) := fun q hq =>
    hU.inter_closure ⟨hq, dense_initialTorus S hdet q⟩
  have he := htor.of_subset_closure hcontI hcontJ inter_subset_left hd
  have hp : p ∈ e.source := mem_chart_source _ _
  have h := congrArg (fun f => f.compContinuousLinearMap (M.chartTangentMap p p))
    (he ⟨⟨hp,hpI⟩,hpJ⟩)
  exact (M.formInChart_comp_chartTangentMap _ p p hp).symm.trans
    (h.trans (M.formInChart_comp_chartTangentMap _ p p hp))

/-- Select one accepted local form at each actual exchange point. Compatibility
below proves independence of this choice on every chart source. -/
def omega : (SmoothAtlas.presentation S hdet).manifold.Form 2 :=
  fun p => localForm S (SmoothAtlas.chosenIndex S p).val hdet
    (SmoothAtlas.chosenIndex S p).property p

/-- Restriction to every independent locus, including all node axes. -/
theorem omega_eq_localForm (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    omega S hdet p = localForm S I hdet hI p :=
  localCompatibility S hdet (SmoothAtlas.chosenIndex S p).val
    (SmoothAtlas.chosenIndex S p).property I hI p (SmoothAtlas.chosenIndex_mem S p) hp

/-- The selected form is smooth in the pinned native form interface. -/
theorem isSmoothForm_omega : (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm
    (omega S hdet) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy
  let c := chartAt (Model (2*d)) a
  let p := c.symm y
  let J := SmoothAtlas.chosenIndex S p
  have hp : p ∈ candidateChartLocus S J.val := SmoothAtlas.chosenIndex_mem S p
  have hs := contDiffAt_localForm_inChart S hdet J.val J.property a y hy hp
  have he : (SmoothAtlas.presentation S hdet).manifold.formInChart a (omega S hdet) =ᶠ[𝓝 y]
      (SmoothAtlas.presentation S hdet).manifold.formInChart a (localForm S J.val hdet J.property) := by
    have hn := (c.continuousAt_symm hy).preimage_mem_nhds
      ((isOpen_candidateChartLocus S J.val).mem_nhds hp)
    filter_upwards [hn] with z hz
    exact congrArg (fun f => f.compContinuousLinearMap
      ((SmoothAtlas.presentation S hdet).manifold.inverseChartTangentMap a z))
        (omega_eq_localForm S hdet J.val J.property _ hz)
  exact (hs.congr_of_eventuallyEq he).contDiffWithinAt

/-- Exact imaginary-part normalization on the entire initial torus. -/
theorem omega_torus (p : S.Point) (hp : p ∈ initialTorus S)
    (v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (omega S hdet) p v w =
      (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p v w :=
  localForm_torus S (SmoothAtlas.chosenIndex S p).val hdet
    (SmoothAtlas.chosenIndex S p).property p hp v w

/-- The actual derivative is smooth; density arguments for closedness may use this theorem. -/
theorem isSmoothForm_exteriorDerivative_omega :
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (omega S hdet)) :=
  SmoothManifold.isSmoothForm_exteriorDerivative _ _ (isSmoothForm_omega S hdet)

/-- The constant real alternating form whose pullback by local logarithms has
exactly the prescribed factor one half and imaginary part. Its coefficient is
the weighted form matrix `K = E * D`, matching
`SmoothPresentation.logarithmicImaginaryValue`. -/
def matrixForm : (Fin d → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.imCLM.compContinuousAlternatingMap
    (((1 / 2 : ℂ) • ∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℂ) •
      wedge (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj j)).restrictScalars ℝ)

theorem matrixForm_apply (v : Fin 2 → (Fin d → ℂ)) :
    matrixForm S v = ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
      (S.K i j : ℂ) * (v 0 i * v 1 j - v 1 i * v 0 j)).im := by
  simp [matrixForm, wedge_apply, smul_eq_mul]

/-- Normalize each coordinate at a nonzero center before using the principal
logarithm. The resulting germ is defined around every torus point. -/
def normalizedLog (b x : Fin d → ℂ) : Fin d → ℂ :=
  fun i => Complex.log (x i / b i)

theorem contDiffAt_normalizedLog (b x : Fin d → ℂ) (hb : ∀ i, b i ≠ 0)
    (hx : ∀ i, x i / b i ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (normalizedLog b) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact ((Complex.contDiffAt_log (hx i)).restrict_scalars ℝ).comp x
    ((contDiff_apply ℝ ℂ i).contDiffAt.div_const (b i))

theorem fderiv_normalizedLog (b x : Fin d → ℂ) (hb : ∀ i, b i ≠ 0)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, x i / b i ∈ Complex.slitPlane)
    (v : Fin d → ℂ) (i : Fin d) :
    fderiv ℝ (normalizedLog b) x v i = v i / x i := by
  have hdiv (j : Fin d) : HasFDerivAt (fun z : Fin d → ℂ => z j / b j)
      ((b j)⁻¹ • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ)) x := by
    convert (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ).hasFDerivAt.const_smul (b j)⁻¹ using 1
    ext z
    simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  have hi (j : Fin d) := ((Complex.hasDerivAt_log (hx j)).hasFDerivAt.restrictScalars ℝ).comp x
    (hdiv j)
  have hd := (hasFDerivAt_pi.mpr hi).fderiv
  rw [show fderiv ℝ (normalizedLog b) x = _ from hd]
  change ((b i)⁻¹ * v i) * (x i / b i)⁻¹ = v i / x i
  field_simp [hb i, hx0 i]

/-- At every torus point the actual form is locally the pullback of the
constant normalized matrix form by logarithms of the original coordinates. -/
theorem exteriorDerivative_omega_torus (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (omega S hdet) p = 0 := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  let P := SmoothAtlas.presentation S hdet
  let M := P.manifold
  let c := chartAt (Model (2*d)) p
  let y := c p
  have hps : p ∈ c.source := mem_chart_source _ _
  have hy : y ∈ c.target := c.map_source hps
  let q : Model (2*d) → (Fin d → ℂ) := (fun r : S.Point => r.a) ∘ c.symm
  have hq : ContDiffOn ℝ ∞ q c.target :=
    M.contDiffOn_comp_inverseChart (TorusNondegeneracy.original_smooth S P) p
  have hqy : q y = p.a := by
    change (c.symm (c p)).a = p.a
    rw [c.left_inv hps]
  have hlogy : ∀ i, q y i / p.a i ∈ Complex.slitPlane := by
    intro i
    rw [hqy, div_self (hp i)]
    exact Complex.one_mem_slitPlane
  let g := normalizedLog p.a ∘ q
  have hg : ContDiffAt ℝ ∞ g y :=
    (contDiffAt_normalizedLog p.a (q y) hp hlogy).comp y
      (hq.contDiffAt (c.open_target.mem_nhds hy))
  have hnlog : ∀ᶠ z in 𝓝 y, ∀ i, q z i / p.a i ∈ Complex.slitPlane := by
    apply Filter.eventually_all.mpr
    intro i
    exact (((continuous_apply i).continuousAt.comp
      (hq.contDiffAt (c.open_target.mem_nhds hy)).continuousAt).div_const (p.a i)).preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds (hlogy i))
  have hntor : ∀ᶠ z in 𝓝 y, c.symm z ∈ initialTorus S :=
    (c.continuousAt_symm hy).preimage_mem_nhds
      ((isOpen_initialTorus S).mem_nhds (by simpa only [y, c.left_inv hps] using hp))
  have he : M.formInChart p (omega S hdet) =ᶠ[𝓝 y]
      (fun z => (matrixForm S).compContinuousLinearMap (fderiv ℝ g z)) := by
    filter_upwards [c.open_target.mem_nhds hy, hnlog, hntor] with z hz hzlog hztor
    have hdq : (TorusNondegeneracy.originalDifferential S P (c.symm z)).comp
        (M.inverseChartTangentMap p z) = fderiv ℝ q z :=
      M.mfderiv_comp_inverseChart ((TorusNondegeneracy.original_smooth S P).mdifferentiable
        (by simp)) p hz
    have hdg : fderiv ℝ g z = (fderiv ℝ (normalizedLog p.a) (q z)).comp (fderiv ℝ q z) :=
      fderiv_comp z ((contDiffAt_normalizedLog p.a (q z) hp hzlog).differentiableAt (by simp))
        ((hq.contDiffAt (c.open_target.mem_nhds hz)).differentiableAt (by simp))
    have hd (v : Model (2*d)) (i : Fin d) : fderiv ℝ g z v i =
        P.coordinateDifferential i (c.symm z) (M.inverseChartTangentMap p z v) / (c.symm z).a i := by
      rw [hdg, ContinuousLinearMap.comp_apply,
        fderiv_normalizedLog p.a (q z) hp hztor hzlog, ← hdq]
      exact congrArg (fun t => t / (c.symm z).a i)
        (TorusNondegeneracy.originalDifferential_apply S P _ _ i)
    apply ContinuousAlternatingMap.ext
    intro v
    have hv : (fun i => M.inverseChartTangentMap p z (v i)) =
        ![M.inverseChartTangentMap p z (v 0), M.inverseChartTangentMap p z (v 1)] := by
      funext i; fin_cases i <;> rfl
    change omega S hdet (c.symm z) (fun i => M.inverseChartTangentMap p z (v i)) = _
    rw [hv]
    change SmoothManifold.evalTwo (omega S hdet) (c.symm z) _ _ = _
    rw [omega_torus S hdet _ hztor]
    change P.logarithmicImaginaryValue (c.symm z) _ _ =
      matrixForm S (fun i => fderiv ℝ g z (v i))
    rw [matrixForm_apply]
    simp only [hd, SmoothPresentation.logarithmicImaginaryValue]
  change (extDeriv (M.formInChart p (omega S hdet)) y).compContinuousLinearMap
    (M.chartTangentMap p p) = 0
  rw [he.extDeriv_eq]
  have hext := extDeriv_pullback
    (show DifferentiableAt ℝ (fun _ : Fin d → ℂ => matrixForm S) (g y) from differentiableAt_const _)
    hg (by simp)
  rw [hext]
  simp only [extDeriv, fderiv_const]
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- Closedness on the dense torus extends using proved native smoothness of
the actual exterior derivative, in every degree-three tangent fiber. -/
theorem exteriorDerivative_omega (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (omega S hdet) p = 0 := by
  have he := FormExtensionUniqueness.form_eq_of_dense
    (SmoothAtlas.presentation S hdet).manifold (dense_initialTorus S hdet)
    (isSmoothForm_exteriorDerivative_omega S hdet)
    ((SmoothAtlas.presentation S hdet).manifold.isSmoothForm_zero (k := 3))
    (fun p hp => exteriorDerivative_omega_torus S hdet p hp)
  exact congrFun he p

/-- The unchanged accepted global extension proposition, with no compatibility,
closedness, nondegeneracy, or extension premise. -/
theorem globalClosedExtension : NodeTwoForm.GlobalClosedExtension S hdet :=
  ⟨omega S hdet, isSmoothForm_omega S hdet, exteriorDerivative_omega S hdet,
    fun J hJ p hp => omega_eq_localForm S hdet J hJ p hp⟩

end ClusterSkeleton.GlobalTwoForm


