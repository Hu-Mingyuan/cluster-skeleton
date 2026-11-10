import ClusterSkeleton.GlobalTwoForm
import FsFltz.Geometry.ToricForms

/-! The native Liouville primitive on the initial torus. No extension across
zero coordinates, or construction of the manuscript correction H, is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.TorusPrimitive

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The actual angular covector Im(aⱼ⁻¹ daⱼ). -/
def angleCovector (j : Fin d) (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p →L[ℝ] ℝ :=
  Complex.imCLM.comp ((p.a j)⁻¹ •
    (SmoothAtlas.presentation S hdet).coordinateDifferential j p)

theorem angleCovector_apply (j : Fin d) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    angleCovector S hdet j p v =
      ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im := by
  simp [angleCovector, div_eq_mul_inv, mul_comm]

/-- Totalized expression; smoothness is claimed only on the initial torus. -/
def beta : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  covectorForm _ (fun p => ∑ i : Fin d, ∑ j : Fin d,
    ((S.K i j : ℝ) * Real.log ‖p.a i‖) • angleCovector S hdet j p)

/-- There is no factor one half, minus sign, or inverse matrix in beta. -/
theorem evalOne_beta (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalOne (beta S hdet) p v =
      ∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * Real.log ‖p.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im := by
  simp [beta, angleCovector_apply]

/-- Add the actual manifold differential of an ordinary real function.

**Sign convention (stage B2).** The reference primitive is
`λ_ac = λ_tor + dH` with `H = ∑_{i∈M} d_i h(u_i) χ_i ρ(v_i) β(η_i)`
(`proof-blueprint.tex`, section "Skeleton in the acyclic case"). With the literal
column exponents of the weighted seed the Lean character is the reference
character, `exchangeCharacter p i = t_i`, hence
`TorusCorrection.rowLog p i = v_i` and
`arg (-exchangeCharacter p i) = η_i - π`, so the Lean `H` is the reference `H`
itself, not its negative. The correction is therefore **added**: the two sign
flips that cancelled the subtraction in the skew-symmetric baseline
(`rowLog = -v_i`, `arg(-exchangeCharacter) = -(η_i-π)`) are both absent here. -/
def alpha (H : S.Point → ℝ) : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  beta S hdet + covectorForm _ (differentialCovector _ H)

theorem evalOne_alpha (H : S.Point → ℝ) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalOne (alpha S hdet H) p v =
      SmoothManifold.evalOne (beta S hdet) p v +
        differentialCovector (SmoothAtlas.presentation S hdet).manifold H p v := by
  simp [alpha, SmoothManifold.evalOne, covectorForm]

theorem alpha_zero : alpha S hdet (fun _ => 0) = beta S hdet := by
  funext p
  ext v
  simp [alpha, covectorForm, differentialCovector, mfderiv_const]

/-- The affine model in a logarithmic coordinate germ centered at b. -/
def logarithmicPrimitive (b z : Fin d → ℂ) : (Fin d → ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
    (∑ i : Fin d, ∑ j : Fin d,
      ((S.K i j : ℝ) * (Real.log ‖b i‖ + (z i).re)) •
        (Complex.imCLM.comp (ContinuousLinearMap.proj j)))

theorem logarithmicPrimitive_apply (b z : Fin d → ℂ)
    (v : Fin 1 → (Fin d → ℂ)) :
    logarithmicPrimitive S b z v = ∑ i : Fin d, ∑ j : Fin d,
      (S.K i j : ℝ) * (Real.log ‖b i‖ + (z i).re) * (v 0 j).im := by
  simp [logarithmicPrimitive]

theorem contDiff_logarithmicPrimitive (b : Fin d → ℂ) :
    ContDiff ℝ ∞ (logarithmicPrimitive S b) := by
  apply (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Fin d → ℂ) (F := ℝ) (0 : Fin 1)).contDiff.comp
  apply ContDiff.sum; intro i _
  apply ContDiff.sum; intro j _
  exact (show ContDiff ℝ ∞ (fun z : Fin d → ℂ =>
      (S.K i j : ℝ) * (Real.log ‖b i‖ + (z i).re)) from
    contDiff_const.mul (contDiff_const.add
      (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ i)))).smul_const
        (Complex.imCLM.comp (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ))

theorem fderiv_logarithmicPrimitive_eval (b z : Fin d → ℂ)
    (v : Fin 1 → (Fin d → ℂ)) :
    fderiv ℝ (fun x => logarithmicPrimitive S b x v) z =
      ∑ i : Fin d, ∑ j : Fin d,
        ((S.K i j : ℝ) * (v 0 j).im) •
          (Complex.reCLM.comp (ContinuousLinearMap.proj i)) := by
  have he : (fun x => logarithmicPrimitive S b x v) =
      (fun x => ∑ i : Fin d, ∑ j : Fin d,
        ((S.K i j : ℝ) * (v 0 j).im) * (Real.log ‖b i‖ + (x i).re)) := by
    funext x
    simp only [logarithmicPrimitive_apply]
    congr 1; funext i; congr 1; funext j; ring
  rw [he]
  apply HasFDerivAt.fderiv
  apply HasFDerivAt.fun_sum; intro i _
  apply HasFDerivAt.fun_sum; intro j _
  convert ((Complex.reCLM.comp (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℝ] ℂ)).hasFDerivAt.const_add
    (Real.log ‖b i‖)).const_mul ((S.K i j : ℝ) * (v 0 j).im) using 1
  rfl

/-- Real-coordinate expression of the accepted normalized matrix form. -/
theorem matrixForm_real (v w : Fin d → ℂ) :
    GlobalTwoForm.matrixForm S ![v, w] =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (v i).re * (w j).im) -
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (w i).re * (v j).im) := by
  rw [GlobalTwoForm.matrixForm_apply, TorusNondegeneracy.normalized_pairing]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Finset.sum_mul, Complex.im_sum, Complex.mul_im, Complex.mul_re,
    Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero, zero_add, add_zero,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hs : (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (v i).im * (w j).re) =
      -(∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * (w i).re * (v j).im) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [S.K_skew j i, Rat.cast_neg]
    ring
  rw [Finset.sum_comm (f := fun j i => (S.K i j : ℝ) * (v i).im * (w j).re), hs]
  rfl

theorem extDeriv_logarithmicPrimitive (b z : Fin d → ℂ) :
    extDeriv (logarithmicPrimitive S b) z = GlobalTwoForm.matrixForm S := by
  ext v
  rw [extDeriv_apply ((contDiff_logarithmicPrimitive S b).differentiable (by simp) z)]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val •
    fderiv ℝ (fun x => logarithmicPrimitive S b x (i.removeNth v)) z (v i)) = _
  rw [Fin.sum_univ_two]
  simp only [fderiv_logarithmicPrimitive_eval, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.reCLM_apply]
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, matrixForm_real]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul, Fin.removeNth, smul_eq_mul]
  change (∑ i, ∑ j, ((S.K i j : ℝ) * (v 1 j).im) * (v 0 i).re) -
    (∑ i, ∑ j, ((S.K i j : ℝ) * (v 0 j).im) * (v 1 i).re) = _
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem log_norm_normalized (b x : ℂ) (hb : b ≠ 0) (hx : x ≠ 0) :
    Real.log ‖x‖ = Real.log ‖b‖ + (Complex.log (x / b)).re := by
  rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hx)
    (norm_ne_zero_iff.mpr hb)]
  ring

/-- Smoothness of the pullback of a one-form, stated for a single germ. -/
theorem contDiffAt_oneForm_comp
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x : X} {η : X → F [⋀^Fin 1]→L[ℝ] ℝ} {B : X → E →L[ℝ] F}
    (hη : ContDiffAt ℝ ∞ η x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (fun p => (η p).compContinuousLinearMap (B p)) x := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.contDiffAt.comp x
    ((eF.symm.contDiff.contDiffAt.comp x hη).clm_comp hB)
  convert hs using 1
  funext p
  ext v
  change η p (fun i => B p (v i)) = η p (fun _ => B p (v 0))
  congr 1
  ext i
  fin_cases i
  rfl

/-- In every native chart at a torus point, beta and omega have a common
normalized-log germ. Both coefficient equalities are local. -/
theorem logarithmic_germ :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ initialTorus S),
      ∃ g : Model (2*d) → (Fin d → ℂ),
        ContDiffAt ℝ ∞ g y ∧
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (beta S hdet) =ᶠ[𝓝 y]
          fun z => (logarithmicPrimitive S ((chartAt (Model (2*d)) a).symm y).a
            (g z)).compContinuousLinearMap (fderiv ℝ g z)) ∧
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a
          (GlobalTwoForm.omega S hdet) =ᶠ[𝓝 y]
          fun z => (GlobalTwoForm.matrixForm S).compContinuousLinearMap (fderiv ℝ g z)) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro a y hy hp
  let P := SmoothAtlas.presentation S hdet
  let M := P.manifold
  let c := chartAt (Model (2*d)) a
  let b := (c.symm y).a
  let q : Model (2*d) → (Fin d → ℂ) := (fun r : S.Point => r.a) ∘ c.symm
  have hq : ContDiffOn ℝ ∞ q c.target :=
    M.contDiffOn_comp_inverseChart (TorusNondegeneracy.original_smooth S P) a
  have hlogy : ∀ i, q y i / b i ∈ Complex.slitPlane := by
    intro i
    change b i / b i ∈ Complex.slitPlane
    rw [div_self (hp i)]
    exact Complex.one_mem_slitPlane
  let g := GlobalTwoForm.normalizedLog b ∘ q
  have hg : ContDiffAt ℝ ∞ g y :=
    (GlobalTwoForm.contDiffAt_normalizedLog b (q y) hp hlogy).comp y
      (hq.contDiffAt (c.open_target.mem_nhds hy))
  refine ⟨g, hg, ?_, ?_⟩
  all_goals
    have hnlog : ∀ᶠ z in 𝓝 y, ∀ i, q z i / b i ∈ Complex.slitPlane := by
      apply Filter.eventually_all.mpr
      intro i
      exact (((continuous_apply i).continuousAt.comp
        (hq.contDiffAt (c.open_target.mem_nhds hy)).continuousAt).div_const (b i)).preimage_mem_nhds
          (Complex.isOpen_slitPlane.mem_nhds (hlogy i))
    have hntor : ∀ᶠ z in 𝓝 y, c.symm z ∈ initialTorus S :=
      (c.continuousAt_symm hy).preimage_mem_nhds ((isOpen_initialTorus S).mem_nhds hp)
    filter_upwards [c.open_target.mem_nhds hy, hnlog, hntor] with z hz hzlog hztor
    have hdq : (TorusNondegeneracy.originalDifferential S P (c.symm z)).comp
        (M.inverseChartTangentMap a z) = fderiv ℝ q z :=
      M.mfderiv_comp_inverseChart ((TorusNondegeneracy.original_smooth S P).mdifferentiable
        (by simp)) a hz
    have hdg : fderiv ℝ g z = (fderiv ℝ (GlobalTwoForm.normalizedLog b) (q z)).comp
        (fderiv ℝ q z) :=
      fderiv_comp z ((GlobalTwoForm.contDiffAt_normalizedLog b (q z) hp hzlog).differentiableAt
        (by simp)) ((hq.contDiffAt (c.open_target.mem_nhds hz)).differentiableAt (by simp))
    have hd (v : Model (2*d)) (i : Fin d) : fderiv ℝ g z v i =
        P.coordinateDifferential i (c.symm z) (M.inverseChartTangentMap a z v) / (c.symm z).a i := by
      rw [hdg, ContinuousLinearMap.comp_apply,
        GlobalTwoForm.fderiv_normalizedLog b (q z) hp hztor hzlog, ← hdq]
      exact congrArg (fun t => t / (c.symm z).a i)
        (TorusNondegeneracy.originalDifferential_apply S P _ _ i)
  · ext v
    change beta S hdet (c.symm z) (fun i => M.inverseChartTangentMap a z (v i)) = _
    have hv : (fun i => M.inverseChartTangentMap a z (v i)) =
        ![M.inverseChartTangentMap a z (v 0)] := by ext i; fin_cases i; rfl
    rw [hv]
    change SmoothManifold.evalOne (beta S hdet) (c.symm z) _ =
      logarithmicPrimitive S b (g z) (fun i => fderiv ℝ g z (v i))
    rw [evalOne_beta, logarithmicPrimitive_apply]
    simp only [hd]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [log_norm_normalized (b i) ((c.symm z).a i) (hp i) (hztor i)]
    rfl
  · ext v
    have hv : (fun i => M.inverseChartTangentMap a z (v i)) =
        ![M.inverseChartTangentMap a z (v 0), M.inverseChartTangentMap a z (v 1)] := by
      ext i; fin_cases i <;> rfl
    change GlobalTwoForm.omega S hdet (c.symm z)
      (fun i => M.inverseChartTangentMap a z (v i)) = _
    rw [hv]
    change SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) (c.symm z) _ _ = _
    rw [GlobalTwoForm.omega_torus S hdet _ hztor]
    change P.logarithmicImaginaryValue (c.symm z) _ _ =
      GlobalTwoForm.matrixForm S (fun i => fderiv ℝ g z (v i))
    rw [GlobalTwoForm.matrixForm_apply]
    simp only [hd, SmoothPresentation.logarithmicImaginaryValue]

/-- Smooth coefficients at every torus point, in every native chart. -/
theorem contDiffAt_beta_inChart :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ initialTorus S),
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (beta S hdet)) y := by
  letI := SmoothAtlas.charts S hdet
  intro a y hy hp
  obtain ⟨g, hg, hb, _⟩ := logarithmic_germ S hdet a y hy hp
  exact (contDiffAt_oneForm_comp
    ((contDiff_logarithmicPrimitive S _).contDiffAt.comp y hg)
    (hg.fderiv_right (by simp))).congr_of_eventuallyEq hb

/-- The exact accepted omega is the native derivative of beta on the torus. -/
theorem exteriorDerivative_beta (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (beta S hdet) p =
      GlobalTwoForm.omega S hdet p := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  let M := (SmoothAtlas.presentation S hdet).manifold
  let c := chartAt (Model (2*d)) p
  have hps : p ∈ c.source := mem_chart_source _ _
  have hp' : c.symm (c p) ∈ initialTorus S := by rwa [c.left_inv hps]
  obtain ⟨g, hg, hb, hw⟩ := logarithmic_germ S hdet p (c p) (c.map_source hps) hp'
  change (extDeriv (M.formInChart p (beta S hdet)) (c p)).compContinuousLinearMap
    (M.chartTangentMap p p) = _
  rw [hb.extDeriv_eq, extDeriv_pullback
    ((contDiff_logarithmicPrimitive S _).differentiable (by simp) _) hg (by simp),
    extDeriv_logarithmicPrimitive]
  have hw0 : M.formInChart p (GlobalTwoForm.omega S hdet) (c p) =
      (GlobalTwoForm.matrixForm S).compContinuousLinearMap (fderiv ℝ g (c p)) :=
    hw.self_of_nhds
  exact (congrArg (fun f : Model (2*d) [⋀^Fin 2]→L[ℝ] ℝ =>
    f.compContinuousLinearMap (M.chartTangentMap p p)) hw0.symm).trans
      (M.formInChart_comp_chartTangentMap _ p p hps)

/-- Local calculus for dH needs smoothness only on the open initial torus. -/
theorem differential_germ (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ initialTorus S),
      ContDiffAt ℝ ∞ (H ∘ (chartAt (Model (2*d)) a).symm) y ∧
      ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (covectorForm _ (differentialCovector _ H)) =ᶠ[𝓝 y]
        fun z => ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
          (fderiv ℝ (H ∘ (chartAt (Model (2*d)) a).symm) z)) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro hH a y hy hp
  let M := (SmoothAtlas.presentation S hdet).manifold
  let c := chartAt (Model (2*d)) a
  have hHa (p : S.Point) (hp : p ∈ initialTorus S) :
      ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H p :=
    hH.contMDiffAt ((isOpen_initialTorus S).mem_nhds hp)
  have hc : ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Model (2*d)) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2*d))) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  refine ⟨((hHa _ hp).comp y hc).contDiffAt, ?_⟩
  have hn := (c.continuousAt_symm hy).preimage_mem_nhds ((isOpen_initialTorus S).mem_nhds hp)
  filter_upwards [c.open_target.mem_nhds hy, hn] with z hz hztor
  have hd := mfderiv_comp z ((hHa _ hztor).mdifferentiableAt (by simp))
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2*d))) a).mdifferentiableAt_symm hz)
  rw [mfderiv_eq_fderiv] at hd
  ext v
  exact congrArg (fun f => f (v 0)) hd.symm

theorem contDiffAt_differential_inChart (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ initialTorus S),
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (covectorForm _ (differentialCovector _ H))) y := by
  letI := SmoothAtlas.charts S hdet
  intro hH a y hy hp
  obtain ⟨hf, he⟩ := differential_germ S hdet H hH a y hy hp
  exact (((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model (2*d)) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt).comp y
      (hf.fderiv_right (by simp))).congr_of_eventuallyEq he

theorem exteriorDerivative_differential (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ (p : S.Point), p ∈ initialTorus S →
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (covectorForm _ (differentialCovector _ H)) p = 0 := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro hH p hp
  let M := (SmoothAtlas.presentation S hdet).manifold
  let c := chartAt (Model (2*d)) p
  have hps : p ∈ c.source := mem_chart_source _ _
  have hp' : c.symm (c p) ∈ initialTorus S := by rwa [c.left_inv hps]
  obtain ⟨hf, he⟩ := differential_germ S hdet H hH p (c p) (c.map_source hps) hp'
  let f := H ∘ c.symm
  have hz : ContDiffAt ℝ ∞
      (fun z => ContinuousAlternatingMap.constOfIsEmpty ℝ (Model (2*d)) (Fin 0) (f z)) (c p) :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Model (2*d)) ℝ (Fin 0)).contDiff.contDiffAt.comp
      (c p) hf
  change (extDeriv (M.formInChart p (covectorForm _ (differentialCovector _ H))) (c p)).compContinuousLinearMap
    (M.chartTangentMap p p) = 0
  rw [he.extDeriv_eq]
  simp_rw [← extDeriv_constOfIsEmpty]
  rw [extDeriv_extDeriv_apply hz (by simp)]
  ext v
  rfl

theorem contDiffAt_alpha_inChart (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ initialTorus S),
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (alpha S hdet H)) y := by
  letI := SmoothAtlas.charts S hdet
  intro hH a y hy hp
  convert (contDiffAt_beta_inChart S hdet a y hy hp).add
    (contDiffAt_differential_inChart S hdet H hH a y hy hp) using 1
  funext z
  ext v
  rfl

/-- Exact corrections preserve the SAME omega at every torus point. The only
smoothness assumption on H is native ContMDiffOn on that torus. -/
theorem exteriorDerivative_alpha (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ (p : S.Point), p ∈ initialTorus S →
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (alpha S hdet H) p =
        GlobalTwoForm.omega S hdet p := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro hH p hp
  let M := (SmoothAtlas.presentation S hdet).manifold
  let c := chartAt (Model (2*d)) p
  have hps : p ∈ c.source := mem_chart_source _ _
  have hp' : c.symm (c p) ∈ initialTorus S := by rwa [c.left_inv hps]
  have hb := (contDiffAt_beta_inChart S hdet p (c p) (c.map_source hps) hp').differentiableAt (by simp)
  have hD := (contDiffAt_differential_inChart S hdet H hH p (c p)
    (c.map_source hps) hp').differentiableAt (by simp)
  have he : M.exteriorDerivative (alpha S hdet H) p =
      M.exteriorDerivative (beta S hdet) p +
      M.exteriorDerivative (covectorForm _ (differentialCovector _ H)) p := by
    change (extDeriv (fun z => M.formInChart p (beta S hdet) z +
      M.formInChart p (covectorForm _ (differentialCovector _ H)) z) (c p)).compContinuousLinearMap _ = _
    rw [extDeriv_fun_add hb hD]
    ext v
    rfl
  rw [he, exteriorDerivative_beta S hdet p hp,
    exteriorDerivative_differential S hdet H hH p hp, add_zero]

end ClusterSkeleton.TorusPrimitive
