import ClusterSkeleton.TorusCorrection
import ClusterSkeleton.SeedAlgebra
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Native torus Liouville calculations. All assertions about the totalized
primitive and its intrinsic vector are restricted to the initial torus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.TorusLiouvilleDynamics

/-- Finite-dimensional solvability of the pinned native contraction equation.
This uses the same Euclidean duality as `SmoothLiouville`, without importing
its unrelated global regularity dependencies. -/
theorem native_equation_exists {n : ℕ} (M : SmoothManifold n)
    (α : M.Form 1) (p : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative α) p) :
    ∃ v, M.LiouvilleEquation α p v := by
  let e : Model n ≃L[ℝ] Model n [⋀^Fin 1]→L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (Model n)).toContinuousLinearEquiv.trans
      (ContinuousAlternatingMap.ofSubsingletonLIE
        (𝕜 := ℝ) (E := Model n) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let L : Model n →L[ℝ] Model n :=
    e.symm.toContinuousLinearMap.comp (M.exteriorDerivative α p).curryLeft
  have hinj : Function.Injective L := by
    intro v w h
    apply sub_eq_zero.mp
    apply hnd
    intro u
    have hz : L (v - w) = 0 := by rw [map_sub, h, sub_self]
    have hc : (M.exteriorDerivative α p).curryLeft (v - w) = 0 := by
      apply e.symm.injective
      simpa [L] using hz
    exact congrArg (fun β => β ![u]) hc
  obtain ⟨v, hv⟩ := LinearMap.surjective_of_injective (f := L.toLinearMap) hinj
    (e.symm (α p))
  refine ⟨v, ?_⟩
  have hc : (M.exteriorDerivative α p).curryLeft v = α p := e.symm.injective hv
  intro w
  have hw := congrArg (fun β => β (fun _ : Fin 1 => w)) hc
  convert hw using 1
  · apply congrArg (M.exteriorDerivative α p)
    funext i
    fin_cases i <;> rfl
  · rfl

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The form-determined native vector, without a global smoothness assertion. -/
def Z (ε κ δ : ℝ) (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p :=
  (SmoothAtlas.presentation S hdet).manifold.liouvilleVector
    (TorusCorrection.alpha S hdet ε κ δ) p

/-- Actual logarithmic tangent components, including all frozen coordinates. -/
def logarithmicComponents (ε κ δ : ℝ) (p : S.Point) (j : Fin d) : ℂ :=
  (SmoothAtlas.presentation S hdet).coordinateDifferential j p
    (Z S hdet ε κ δ p) / p.a j

theorem contraction (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p (Z S hdet ε κ δ p) v =
      SmoothManifold.evalOne (TorusCorrection.alpha S hdet ε κ δ) p v := by
  let M := (SmoothAtlas.presentation S hdet).manifold
  let α := TorusCorrection.alpha S hdet ε κ δ
  have hnd : M.Nondegenerate (M.exteriorDerivative α) p := by
    intro u hu
    apply TorusNondegeneracy.logarithmicImaginaryValue_nondegenerate S
      (SmoothAtlas.presentation S hdet) hdet p hp u
    intro w
    have hw := hu w
    change (M.exteriorDerivative α p) ![u, w] = 0 at hw
    rw [TorusCorrection.exteriorDerivative_alpha S hdet ε κ hδ p hp] at hw
    exact (GlobalTwoForm.omega_torus S hdet p hp u w).symm.trans hw
  have h := M.liouvilleVector_contraction α p (native_equation_exists M α p hnd) v
  change (M.exteriorDerivative α p) ![Z S hdet ε κ δ p, v] = _ at h
  rw [TorusCorrection.exteriorDerivative_alpha S hdet ε κ hδ p hp] at h
  exact h

/-- The real coordinate basis transported into the actual tangent fiber. -/
def radialTangent (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p :=
  (TorusNondegeneracy.logarithmicTangentEquiv S
    (SmoothAtlas.presentation S hdet) p hp).symm (Pi.single i 1)

/-- The imaginary coordinate basis transported into the actual tangent fiber. -/
def angularTangent (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p :=
  (TorusNondegeneracy.logarithmicTangentEquiv S
    (SmoothAtlas.presentation S hdet) p hp).symm (Pi.single i Complex.I)

theorem logarithmic_radialTangent (p : S.Point) (hp : p ∈ initialTorus S)
    (i j : Fin d) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential j p
      (radialTangent S hdet p hp i) / p.a j = (Pi.single i 1 : Fin d → ℂ) j := by
  rw [← TorusNondegeneracy.logarithmicTangentEquiv_apply S
    (SmoothAtlas.presentation S hdet) p hp]
  exact congrFun ((TorusNondegeneracy.logarithmicTangentEquiv S
    (SmoothAtlas.presentation S hdet) p hp).apply_symm_apply _) j

theorem logarithmic_angularTangent (p : S.Point) (hp : p ∈ initialTorus S)
    (i j : Fin d) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential j p
      (angularTangent S hdet p hp i) / p.a j = (Pi.single i Complex.I : Fin d → ℂ) j := by
  rw [← TorusNondegeneracy.logarithmicTangentEquiv_apply S
    (SmoothAtlas.presentation S hdet) p hp]
  exact congrFun ((TorusNondegeneracy.logarithmicTangentEquiv S
    (SmoothAtlas.presentation S hdet) p hp).apply_symm_apply _) j

/-- The full matrix pairing in real logarithmic tangent coordinates. -/
theorem omega_real (p : S.Point) (hp : p ∈ initialTorus S)
    (v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p v w =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential i p v / p.a i).re *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p w / p.a j).im) -
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential i p w / p.a i).re *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im) := by
  rw [GlobalTwoForm.omega_torus S hdet p hp]
  have h := TorusPrimitive.matrixForm_real S
    (fun i => (SmoothAtlas.presentation S hdet).coordinateDifferential i p v / p.a i)
    (fun i => (SmoothAtlas.presentation S hdet).coordinateDifferential i p w / p.a i)
  rw [GlobalTwoForm.matrixForm_apply] at h
  exact h

/-- The angular equation of (2.9), with the actual differential and tangent. -/
theorem angular_equation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (∑ j : Fin d, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      -differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i) := by
  classical
  have h := contraction S hdet ε κ hδ p hp (radialTangent S hdet p hp i)
  rw [omega_real S hdet p hp, TorusCorrection.evalOne_alpha] at h
  simp [logarithmic_radialTangent, Pi.single_apply, logarithmicComponents, apply_ite] at h ⊢
  linarith

/-- The angular equation in the exponent (character) orientation. The weight
`d_i` appears **here**, not in the radial equation: this is the blueprint's
`eq:acyclic-angle-flow`, `η̇_i = (1/d_i) ∂_{u_i} H`, obtained from the form
equation by `SeedAlgebra.sum_K_row` (`∑_j K_{ij} x_j = -d_i ∑_j B_{ij} x_j`). -/
theorem angular_equation_row (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (S.D i : ℝ) *
      (∑ j : Fin d, (S.B i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp i) := by
  have h := angular_equation S hdet ε κ hδ p hp i
  rw [SeedAlgebra.sum_K_row S _ i] at h
  linarith

/-- Normalization puts every nonzero base point at 1 in the logarithm's slit
plane. This is a derivative of a genuine smooth local logarithm. -/
theorem hasFDerivAt_normalized_log {b : ℂ} (hb : b ≠ 0) :
    HasFDerivAt (fun z : ℂ => Complex.log (z / b))
      (b⁻¹ • (1 : ℂ →L[ℝ] ℂ)) b := by
  have hd : HasDerivAt (fun z : ℂ => z / b) b⁻¹ b := by
    convert! (hasDerivAt_id b).div_const b using 1
    simp
  have hl := (Complex.hasDerivAt_log
    (z := b / b) (by simpa [div_self hb] using Complex.one_mem_slitPlane)).comp b
      (h := fun z : ℂ => z / b) hd
  apply (hl.hasFDerivAt.restrictScalars ℝ).congr_fderiv
  ext z
  simp [div_self hb, smul_eq_mul, mul_comm]

theorem hasFDerivAt_localAngle {b : ℂ} (hb : b ≠ 0) :
    HasFDerivAt (TorusCorrection.localAngle b)
      (Complex.imCLM.comp (b⁻¹ • (1 : ℂ →L[ℝ] ℂ))) b := by
  exact (Complex.imCLM.hasFDerivAt.comp b (hasFDerivAt_normalized_log hb)).add_const _

/-- The derivative of the literal periodic cutoff of principal argument,
including at the principal argument cut. -/
theorem hasFDerivAt_vartheta_arg {δ : ℝ} (hδ : 0 < δ) {b : ℂ} (hb : b ≠ 0) :
    HasFDerivAt (fun z : ℂ => PrimitiveCutoffs.vartheta δ (Complex.arg z))
      (deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg b) •
        Complex.imCLM.comp (b⁻¹ • (1 : ℂ →L[ℝ] ℂ))) b := by
  have ht := ((PrimitiveCutoffs.vartheta_smooth hδ).differentiable (by simp)
    (TorusCorrection.localAngle b b)).hasDerivAt
  have hc := ht.comp_hasFDerivAt b (hasFDerivAt_localAngle hb)
  rw [TorusCorrection.localAngle_self hb] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hb] with z hz
  exact (TorusCorrection.vartheta_localAngle hb hz).symm

theorem hasFDerivAt_log_norm {b : ℂ} (hb : b ≠ 0) :
    HasFDerivAt (fun z : ℂ => Real.log ‖z‖)
      (Complex.reCLM.comp (b⁻¹ • (1 : ℂ →L[ℝ] ℂ))) b := by
  apply ((Complex.reCLM.hasFDerivAt.comp b (hasFDerivAt_normalized_log hb)).const_add
    (Real.log ‖b‖)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hb] with z hz
  exact TorusPrimitive.log_norm_normalized b z hb hz

/-- Native radial differentiation for an arbitrary tangent, rather than a
supplied logarithmic derivative. -/
theorem differential_A (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) (i : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun q => TorusCorrection.A S q i) p v =
      ((SmoothAtlas.presentation S hdet).coordinateDifferential i p v / p.a i).re := by
  letI := SmoothAtlas.charts S hdet
  have hc := (((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))) p).mdifferentiableAt
      (by simp)
  have h := (hasFDerivAt_log_norm (hp i)).hasMFDerivAt.comp p hc.hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
    (fun q : S.Point => Real.log ‖q.a i‖) p v = _
  erw [h.mfderiv]
  change ((p.a i)⁻¹ * (SmoothAtlas.presentation S hdet).coordinateDifferential i p v).re = _
  simp only [div_eq_mul_inv, mul_comm]

/-- The ambient Laurent character derivative, retaining the full integer row. -/
theorem hasFDerivAt_character (x : Fin d → ℂ) (hx : ∀ j, x j ≠ 0) (i : Fin d) :
    HasFDerivAt (fun y : Fin d → ℂ => ∏ j, y j ^ S.B i j)
      ((∏ j, x j ^ S.B i j) •
        ∑ j : Fin d, (S.B i j : ℂ) • ((x j)⁻¹ •
          (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))) x := by
  apply NodeTwoForm.hasFDerivAt_product_log (E := Fin d → ℂ) Finset.univ
  intro j _
  refine NodeTwoForm.hasFDerivAt_zpow_log (E := Fin d → ℂ)
    (f := fun y => y j) (l := (x j)⁻¹ • (ContinuousLinearMap.proj j)) ?_ (hx j) (S.B i j)
  convert! (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := x) using 1
  simp [smul_smul, hx j]

theorem differential_character (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) (i : Fin d) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun q => exchangeCharacter q i) p v =
      exchangeCharacter p i * ∑ j : Fin d, (S.B i j : ℂ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j) := by
  letI := SmoothAtlas.charts S hdet
  have hc := ((TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))
    p).mdifferentiableAt (by simp)
  have h := ((hasFDerivAt_character S p.a hp i).restrictScalars ℝ).hasMFDerivAt.comp p
    hc.hasMFDerivAt
  have he : (fun q : S.Point => exchangeCharacter q i) =
      (fun y : Fin d → ℂ => ∏ j, y j ^ S.B i j) ∘ (fun q : S.Point => q.a) := by
    funext q
    exact exchangeCharacter_eq_zpow_product q i
  unfold complexDifferential
  rw [he]
  erw [h.mfderiv]
  change (∏ j, p.a j ^ S.B i j) *
    (∑ j : Fin d, (S.B i j : ℂ) • ((p.a j)⁻¹ •
      (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ)))
        (TorusNondegeneracy.originalDifferential S (SmoothAtlas.presentation S hdet) p v) = _
  simp [exchangeCharacter_eq_zpow_product, TorusNondegeneracy.originalDifferential_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Native differentiation of the angular cutoff retains every full-matrix
column. The principal argument itself is never differentiated at its cut. -/
theorem differential_angular {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) (i : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun q => TorusCorrection.angular S δ q i) p v =
      deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
        ∑ j : Fin d, (S.B i j : ℝ) *
          ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im := by
  letI := SmoothAtlas.charts S hdet
  have hn := TorusCorrection.exchangeCharacter_ne_zero S p hp i
  have hc := (TorusCorrection.contMDiffAt_exchangeCharacter S hdet p hp i).mdifferentiableAt
    (by simp)
  have h := (hasFDerivAt_vartheta_arg hδ (neg_ne_zero.mpr hn)).hasMFDerivAt.comp p
    hc.hasMFDerivAt.neg
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
    ((fun z : ℂ => PrimitiveCutoffs.vartheta δ (Complex.arg z)) ∘
      (fun q : S.Point => -exchangeCharacter q i)) p v = _
  erw [h.mfderiv]
  change deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
    ((-exchangeCharacter p i)⁻¹ *
      (-complexDifferential (SmoothAtlas.presentation S hdet).manifold
        (fun q => exchangeCharacter q i) p v)).im = _
  rw [differential_character S hdet p hp v i]
  simp [hn, mul_assoc, Complex.im_sum, Complex.mul_im]

/-- The real radial amplitude of a single mutable summand. -/
def amplitude (ε κ : ℝ) (i : Fin d) (a : Fin d → ℝ) : ℝ :=
  PrimitiveCutoffs.radial ε κ (a i) * DominanceCutoff.dominance S ε i a *
    PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * a j)

theorem amplitude_smooth (ε κ : ℝ) (i : Fin d) :
    ContDiff ℝ ∞ (amplitude S ε κ i) := by
  have hr : ContDiff ℝ ∞ (fun a : Fin d → ℝ => ∑ j, (S.B i j : ℝ) * a j) := by
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul (contDiff_apply ℝ ℝ j)
  exact (((PrimitiveCutoffs.radial_smooth ε κ).comp (contDiff_apply ℝ ℝ i)).mul
    (DominanceCutoff.contDiff_dominance S ε i)).mul (PrimitiveCutoffs.rho_smooth.comp hr)

theorem mfderiv_A_apply (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Fin d → ℝ) (TorusCorrection.A S) p v =
      fun j => ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).re := by
  letI := SmoothAtlas.charts S hdet
  funext j
  let ev : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hc := mfderiv_comp p (ev.mdifferentiableAt)
    ((TorusCorrection.contMDiffAt_A S hdet p hp).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, ev.hasFDerivAt.fderiv] at hc
  have he := congrArg (fun L => L v) hc
  change differentialCovector (SmoothAtlas.presentation S hdet).manifold
    (fun q => TorusCorrection.A S q j) p v = _ at he
  exact he.symm.trans (differential_A S hdet p hp v j)

theorem differential_radial_function (f : (Fin d → ℝ) → ℝ)
    (p : S.Point) (hp : p ∈ initialTorus S) (hf : DifferentiableAt ℝ f (TorusCorrection.A S p))
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun q => f (TorusCorrection.A S q)) p v =
      fderiv ℝ f (TorusCorrection.A S p)
        (fun j => ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).re) := by
  letI := SmoothAtlas.charts S hdet
  have h := hf.hasFDerivAt.hasMFDerivAt.comp p
    ((TorusCorrection.contMDiffAt_A S hdet p hp).mdifferentiableAt (by simp)).hasMFDerivAt
  unfold differentialCovector
  erw [h.mfderiv]
  change fderiv ℝ f (TorusCorrection.A S p)
    (mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Fin d → ℝ) (TorusCorrection.A S) p v) = _
  rw [mfderiv_A_apply S hdet p hp v]

/-- The actual differential of the literal Hamiltonian on every native tangent.
All derivatives of the dominance factors occur only in the real direction
supplied to `fderiv amplitude`. -/
theorem differential_H (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) p v =
      ∑ i ∈ S.mutable, (S.D i : ℝ) * (
        amplitude S ε κ i (TorusCorrection.A S p) *
          (deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
            ∑ j : Fin d, (S.B i j : ℝ) *
              ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im) +
        TorusCorrection.angular S δ p i *
          fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S p)
            (fun j => ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).re)) := by
  letI := SmoothAtlas.charts S hdet
  have hF (i : Fin d) := ((amplitude_smooth S ε κ i).comp_contMDiffAt
    (TorusCorrection.contMDiffAt_A S hdet p hp)).mdifferentiableAt (by simp)
  have hG (i : Fin d) := (TorusCorrection.contMDiffAt_angular S hdet hδ p hp i).mdifferentiableAt
    (by simp)
  have hsum := HasMFDerivAt.sum (t := S.mutable)
    (fun i _ => ((hF i).hasMFDerivAt.mul (hG i).hasMFDerivAt).const_smul ((S.D i : ℝ)))
  have hfun : (∑ i ∈ S.mutable, (S.D i : ℝ) •
      ((amplitude S ε κ i ∘ TorusCorrection.A S) *
        (fun q => TorusCorrection.angular S δ q i))) = TorusCorrection.H S ε κ δ := by
    funext q
    simp [TorusCorrection.H, amplitude, TorusCorrection.rowLog, mul_assoc]
  rw [hfun] at hsum
  have he := congrArg (fun L => L v) hsum.mfderiv
  change differentialCovector (SmoothAtlas.presentation S hdet).manifold
    (TorusCorrection.H S ε κ δ) p v = _ at he
  rw [he]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change amplitude S ε κ i (TorusCorrection.A S p) *
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun q => TorusCorrection.angular S δ q i) p v +
    TorusCorrection.angular S δ p i *
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (fun q => amplitude S ε κ i (TorusCorrection.A S q)) p v = _
  rw [differential_angular S hdet hδ p hp v i,
    differential_radial_function S hdet (amplitude S ε κ i) p hp
      ((amplitude_smooth S ε κ i).differentiable (by simp) _) v]

/-- Dominance derivatives vanish on actual pure angular tangents. -/
theorem dominance_angular_derivative_zero (ε : ℝ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i j : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun q => DominanceCutoff.dominance S ε i (TorusCorrection.A S q)) p
        (angularTangent S hdet p hp j) = 0 := by
  rw [differential_radial_function S hdet _ p hp
    ((DominanceCutoff.contDiff_dominance S ε i).differentiable (by simp) _)]
  simp [logarithmic_angularTangent, Pi.single_apply, apply_ite]
  change fderiv ℝ (DominanceCutoff.dominance S ε i) (TorusCorrection.A S p) 0 = 0
  exact map_zero _

theorem differential_H_angular (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (j : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) p (angularTangent S hdet p hp j) =
      ∑ i ∈ S.mutable, (S.D i : ℝ) * (amplitude S ε κ i (TorusCorrection.A S p) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
          (S.B i j : ℝ)) := by
  rw [differential_H S hdet ε κ hδ p hp]
  simp [logarithmic_angularTangent, Pi.single_apply, apply_ite, mul_assoc]
  simp only [← Pi.zero_def, map_zero, mul_zero, add_zero]

/-- The weighted angular derivative of `H` in the form coefficient `K`. The
weight `d_i` of each `H` summand is absorbed by `K_{ij} = -d_i B_{ij}`
(`SeedAlgebra.K_eq_neg_D_mul_B`), at the price of an overall minus sign. -/
theorem differential_H_angular_K (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (j : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) p (angularTangent S hdet p hp j) =
      -∑ i ∈ S.mutable, amplitude S ε κ i (TorusCorrection.A S p) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
          (S.K i j : ℝ) := by
  rw [differential_H_angular S hdet ε κ hδ p hp j, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SeedAlgebra.K_eq_neg_D_mul_B S i j]
  ring

theorem differential_H_radial (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (j : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp j) =
      ∑ i ∈ S.mutable, (S.D i : ℝ) * (TorusCorrection.angular S δ p i *
        fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S p) (Pi.single j 1)) := by
  rw [differential_H S hdet ε κ hδ p hp]
  simp [logarithmic_radialTangent, Pi.single_apply, apply_ite]
  apply Finset.sum_congr rfl
  intro i _
  congr 3
  ext k
  simp [Pi.single_apply]

/-- Correction coefficient extended by zero at frozen indices. -/
def radialCorrection (ε κ δ : ℝ) (p : S.Point) (i : Fin d) : ℝ :=
  if i ∈ S.mutable then amplitude S ε κ i (TorusCorrection.A S p) *
    deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) else 0

theorem radial_matrix_equation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (j : Fin d) :
    (∑ i : Fin d, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p i).re) =
      (∑ i : Fin d, (S.K i j : ℝ) * TorusCorrection.A S p i) -
      ∑ i ∈ S.mutable, amplitude S ε κ i (TorusCorrection.A S p) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
          (S.K i j : ℝ) := by
  classical
  have h := contraction S hdet ε κ hδ p hp (angularTangent S hdet p hp j)
  rw [omega_real S hdet p hp, TorusCorrection.evalOne_alpha,
    differential_H_angular_K S hdet ε κ hδ p hp j] at h
  simpa [logarithmic_angularTangent, Pi.single_apply, apply_ite,
    logarithmicComponents, TorusCorrection.A, sub_eq_add_neg] using h

/-- Cancelling the full weighted form matrix computes every radial component
of the native Liouville vector. -/
theorem real_logarithmicComponents (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (logarithmicComponents S hdet ε κ δ p i).re =
      TorusCorrection.A S p i - radialCorrection S ε κ δ p i := by
  classical
  have he : Matrix.vecMul (fun i => (logarithmicComponents S hdet ε κ δ p i).re)
        (SeedAlgebra.Kreal S) =
      Matrix.vecMul (fun i => TorusCorrection.A S p i - radialCorrection S ε κ δ p i)
        (SeedAlgebra.Kreal S) := by
    funext j
    have h := radial_matrix_equation S hdet ε κ hδ p hp j
    simpa [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib,
      radialCorrection, ite_mul, Finset.sum_ite_mem, mul_comm] using h
  exact congrFun (SeedAlgebra.Kreal_vecMul_injective S hdet he) i

theorem mutable_radial_equation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) (hi : i ∈ S.mutable) :
    (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i -
      PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) *
        DominanceCutoff.dominance S ε i (TorusCorrection.A S p) *
        PrimitiveCutoffs.rho (TorusCorrection.rowLog S p i) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) := by
  rw [real_logarithmicComponents S hdet ε κ hδ p hp i]
  simp [radialCorrection, hi, amplitude, TorusCorrection.rowLog]

theorem frozen_radial_equation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) (hi : i ∉ S.mutable) :
    (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i := by
  rw [real_logarithmicComponents S hdet ε κ hδ p hp i]
  simp [radialCorrection, hi]

theorem radial_eq_of_nonneg {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d)
    (ha : 0 ≤ TorusCorrection.A S p i) :
    (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i := by
  rw [real_logarithmicComponents S hdet ε κ hδ p hp i]
  have hr := PrimitiveCutoffs.radial_eq_zero hκ (show -2 * ε ≤ TorusCorrection.A S p i by linarith)
  simp [radialCorrection, amplitude, hr]

theorem radial_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d)
    (ha : TorusCorrection.A S p i = 0) :
    (logarithmicComponents S hdet ε κ δ p i).re = 0 := by
  rw [radial_eq_of_nonneg S hdet hε hκ hδ p hp i (by rw [ha]), ha]

theorem radial_negative_bound {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d)
    (ha : TorusCorrection.A S p i < 0) :
    (logarithmicComponents S hdet ε κ δ p i).re ≤
      TorusCorrection.A S p i - PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) ∧
    TorusCorrection.A S p i - PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) < 0 := by
  have hr := PrimitiveCutoffs.radial_nonpos hκ (TorusCorrection.A S p i)
  refine ⟨?_, sub_neg.mpr (PrimitiveCutoffs.radial_gt hε hκ ha)⟩
  by_cases hi : i ∈ S.mutable
  · rw [mutable_radial_equation S hdet ε κ hδ p hp i hi]
    let c := DominanceCutoff.dominance S ε i (TorusCorrection.A S p) *
      PrimitiveCutoffs.rho (TorusCorrection.rowLog S p i)
    have hc0 : 0 ≤ c := mul_nonneg (DominanceCutoff.dominance_nonneg S ε i _)
      (PrimitiveCutoffs.rho_nonneg _)
    have hc1 : c ≤ 1 := by
      exact (mul_le_mul_of_nonneg_left (PrimitiveCutoffs.rho_le_one _)
        (DominanceCutoff.dominance_nonneg S ε i _)).trans
          (by simpa using DominanceCutoff.dominance_le_one S ε i (TorusCorrection.A S p))
    have hct : c * deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (PrimitiveCutoffs.vartheta_deriv_le_one hδ _) hc0).trans
        (by simpa using hc1)
    have hh := mul_le_mul_of_nonpos_left hct hr
    dsimp [c] at hh
    nlinarith only [hh]
  · rw [frozen_radial_equation S hdet ε κ hδ p hp i hi]
    linarith

theorem arg_product_angle {ι : Type*} (s : Finset ι) (x : ι → ℂ)
    (hx : ∀ j ∈ s, x j ≠ 0) :
    (Complex.arg (∏ j ∈ s, x j) : Real.Angle) =
      ∑ j ∈ s, (Complex.arg (x j) : Real.Angle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Complex.arg_mul_coe_angle (hx i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hx j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]

/-- A literal Hamiltonian in logarithmic coordinates centered at an actual
torus point. The second argument is a real vector space of complex logarithms. -/
def logarithmicHamiltonian (ε κ δ : ℝ) (p : S.Point) (z : Fin d → ℂ) : ℝ :=
  ∑ i ∈ S.mutable, (S.D i : ℝ) *
    (amplitude S ε κ i (fun j => TorusCorrection.A S p j + (z j).re) *
      PrimitiveCutoffs.vartheta δ
        (Complex.arg (-exchangeCharacter p i) + ∑ j : Fin d, (S.B i j : ℝ) * (z j).im))

theorem angular_logarithmic_identity (δ : ℝ) (p q : S.Point)
    (hp : p ∈ initialTorus S) (hq : q ∈ initialTorus S) (i : Fin d) :
    TorusCorrection.angular S δ q i = PrimitiveCutoffs.vartheta δ
      (Complex.arg (-exchangeCharacter p i) +
        ∑ j : Fin d, (S.B i j : ℝ) * (Complex.log (q.a j / p.a j)).im) := by
  have hnp := neg_ne_zero.mpr (TorusCorrection.exchangeCharacter_ne_zero S p hp i)
  have hnq := neg_ne_zero.mpr (TorusCorrection.exchangeCharacter_ne_zero S q hq i)
  have he : (-exchangeCharacter q i) / (-exchangeCharacter p i) =
      ∏ j : Fin d, (q.a j / p.a j) ^ S.B i j := by
    simp [exchangeCharacter_eq_zpow_product, div_zpow, Finset.prod_div_distrib]
  have ha := arg_product_angle Finset.univ (fun j : Fin d => (q.a j / p.a j) ^ S.B i j)
    (fun j _ => zpow_ne_zero _ (div_ne_zero (hq j) (hp j)))
  rw [← he, Complex.arg_div_coe_angle hnq hnp] at ha
  have hs : ((∑ j : Fin d, (S.B i j : ℝ) * (Complex.log (q.a j / p.a j)).im : ℝ) : Real.Angle) =
      ∑ j : Fin d, S.B i j • (Complex.arg (q.a j / p.a j) : Real.Angle) := by
    change Real.Angle.coeHom (∑ j : Fin d, _) = _
    rw [map_sum]
    simp only [Real.Angle.coe_coeHom, Complex.log_im, Real.Angle.intCast_mul_eq_zsmul]
  apply TorusCorrection.vartheta_eq_of_angle_eq
  rw [Real.Angle.coe_add, hs]
  simp only [Complex.arg_zpow_coe_angle] at ha
  exact (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)

/-- The literal accepted H agrees with the logarithmic expression, with no
restriction on the principal arguments at the base point. -/
theorem H_logarithmic_identity (ε κ δ : ℝ) (p q : S.Point)
    (hp : p ∈ initialTorus S) (hq : q ∈ initialTorus S) :
    TorusCorrection.H S ε κ δ q =
      logarithmicHamiltonian S ε κ δ p (GlobalTwoForm.normalizedLog p.a q.a) := by
  have hA : TorusCorrection.A S q = fun j => TorusCorrection.A S p j +
      (GlobalTwoForm.normalizedLog p.a q.a j).re := by
    funext j
    exact TorusPrimitive.log_norm_normalized (p.a j) (q.a j) (hp j) (hq j)
  change (∑ i ∈ S.mutable, (S.D i : ℝ) * (amplitude S ε κ i (TorusCorrection.A S q) *
    TorusCorrection.angular S δ q i)) = _
  unfold logarithmicHamiltonian
  apply Finset.sum_congr rfl
  intro i _
  rw [hA, angular_logarithmic_identity S δ p q hp hq i]
  rfl

/-- Smooth local logarithmic coordinates at every actual torus point. -/
theorem localLog_contMDiffAt (p : S.Point) (hp : p ∈ initialTorus S) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Fin d → ℂ) ∞
      (fun q : S.Point => GlobalTwoForm.normalizedLog p.a q.a) p := by
  letI := SmoothAtlas.charts S hdet
  exact (GlobalTwoForm.contDiffAt_normalizedLog p.a p.a hp
    (fun j => by simpa [div_self (hp j)] using Complex.one_mem_slitPlane)).comp_contMDiffAt
      (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet) p)

theorem H_logarithmic_germ (ε κ δ : ℝ) (p : S.Point) (hp : p ∈ initialTorus S) :
    TorusCorrection.H S ε κ δ =ᶠ[𝓝 p]
      fun q => logarithmicHamiltonian S ε κ δ p (GlobalTwoForm.normalizedLog p.a q.a) := by
  filter_upwards [(isOpen_initialTorus S).mem_nhds hp] with q hq
  exact H_logarithmic_identity S ε κ δ p q hp hq

/-- Periodic derivative independence, as well as value independence. -/
theorem vartheta_deriv_representative (δ t : ℝ) (k : ℤ) :
    deriv (PrimitiveCutoffs.vartheta δ) (t + k * (2 * Real.pi)) =
      deriv (PrimitiveCutoffs.vartheta δ) t := by
  have h := PrimitiveCutoffs.periodic_iteratedDeriv (PrimitiveCutoffs.vartheta_periodic δ) 1
  rw [iteratedDeriv_one] at h
  simpa [zsmul_eq_mul] using h.zsmul k t

theorem logarithmicHamiltonian_smooth (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) :
    ContDiff ℝ ∞ (logarithmicHamiltonian S ε κ δ p) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul contDiff_const
  apply ContDiff.mul
  · apply (amplitude_smooth S ε κ i).comp
    apply contDiff_pi.mpr
    intro j
    exact contDiff_const.add (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ j))
  · apply (PrimitiveCutoffs.vartheta_smooth hδ).comp
    apply ContDiff.add contDiff_const
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ j))

theorem mfderiv_localLog (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Fin d → ℂ)
      (fun q : S.Point => GlobalTwoForm.normalizedLog p.a q.a) p v =
      fun j => (SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j := by
  letI := SmoothAtlas.charts S hdet
  have hn := (GlobalTwoForm.contDiffAt_normalizedLog p.a p.a hp
    (fun j => by simpa [div_self (hp j)] using Complex.one_mem_slitPlane)).differentiableAt (by simp)
  have h := hn.hasFDerivAt.hasMFDerivAt.comp p
    ((TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet) p).mdifferentiableAt
      (by simp)).hasMFDerivAt
  erw [h.mfderiv]
  funext j
  change fderiv ℝ (GlobalTwoForm.normalizedLog p.a) p.a
    (TorusNondegeneracy.originalDifferential S (SmoothAtlas.presentation S hdet) p v) j = _
  rw [GlobalTwoForm.fderiv_normalizedLog p.a p.a hp hp
      (fun j => by simpa [div_self (hp j)] using Complex.one_mem_slitPlane)]
  exact congrArg (fun z => z / p.a j)
    (TorusNondegeneracy.originalDifferential_apply S (SmoothAtlas.presentation S hdet) p v j)

/-- Ordinary derivative of the literal lifted Hamiltonian. -/
theorem fderiv_logarithmicHamiltonian (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (u : Fin d → ℂ) :
    fderiv ℝ (logarithmicHamiltonian S ε κ δ p) 0 u =
      ∑ i ∈ S.mutable, (S.D i : ℝ) * (
        amplitude S ε κ i (TorusCorrection.A S p) *
          (deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) *
            ∑ j : Fin d, (S.B i j : ℝ) * (u j).im) +
        TorusCorrection.angular S δ p i *
          fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S p) (fun j => (u j).re)) := by
  let re : (Fin d → ℂ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi
    (fun j => Complex.reCLM.comp (ContinuousLinearMap.proj j))
  let row (i : Fin d) : (Fin d → ℂ) →L[ℝ] ℝ :=
    ∑ j : Fin d, (S.B i j : ℝ) •
      Complex.imCLM.comp (ContinuousLinearMap.proj j)
  have hr : HasFDerivAt (fun z : Fin d → ℂ => TorusCorrection.A S p + re z) re 0 :=
    re.hasFDerivAt.const_add _
  have ha (i : Fin d) := ((amplitude_smooth S ε κ i).differentiable (by simp)
    (TorusCorrection.A S p + re 0)).hasFDerivAt.comp 0 hr
  have ht (i : Fin d) := (((PrimitiveCutoffs.vartheta_smooth hδ).differentiable
    (by simp) (Complex.arg (-exchangeCharacter p i) + row i 0)).hasDerivAt).comp_hasFDerivAt
      0 (f := fun z : Fin d → ℂ => Complex.arg (-exchangeCharacter p i) + row i z)
      ((row i).hasFDerivAt.const_add _)
  have h := HasFDerivAt.sum (u := S.mutable)
    (fun i _ => ((ha i).mul (ht i)).const_smul ((S.D i : ℝ)))
  have hf : (∑ i ∈ S.mutable, (S.D i : ℝ) •
      ((amplitude S ε κ i ∘ (fun z : Fin d → ℂ => TorusCorrection.A S p + re z)) *
        (PrimitiveCutoffs.vartheta δ ∘ (fun z : Fin d → ℂ =>
          Complex.arg (-exchangeCharacter p i) + row i z)))) =
      logarithmicHamiltonian S ε κ δ p := by
    funext z
    simp [logarithmicHamiltonian, re, row]
    rfl
  rw [hf] at h
  rw [h.fderiv]
  simp [re, row, smul_eq_mul, TorusCorrection.angular]
  simp only [← Pi.zero_def, add_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The native differential equals the ordinary lifted derivative. The
smooth logarithmic germ and its native derivative are proved above; both sides
here are computed by their native product and chain rules. -/
theorem differential_H_logarithmic (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) p v =
      fderiv ℝ (logarithmicHamiltonian S ε κ δ p) 0
        (fun j => (SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j) := by
  rw [differential_H S hdet ε κ hδ p hp v, fderiv_logarithmicHamiltonian S ε κ hδ p]

/-- The angular equation is the ordinary partial radial derivative of the
literal Hamiltonian in smooth local logarithmic coordinates. -/
theorem angular_equation_logarithmic (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (∑ j : Fin d, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      -fderiv ℝ (logarithmicHamiltonian S ε κ δ p) 0 (Pi.single i 1) := by
  rw [angular_equation S hdet ε κ hδ p hp i,
    differential_H_logarithmic S hdet ε κ hδ p hp]
  congr 2
  funext j
  exact logarithmic_radialTangent S hdet p hp i j

theorem angular_equation_partial_deriv (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (∑ j : Fin d, (S.K i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      -deriv (fun t : ℝ => logarithmicHamiltonian S ε κ δ p
        (t • (Pi.single i 1 : Fin d → ℂ))) 0 := by
  rw [angular_equation_logarithmic S hdet ε κ hδ p hp i]
  have hd : HasDerivAt (fun t : ℝ => t • (Pi.single i 1 : Fin d → ℂ))
      (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin d → ℂ)
  have h := ((logarithmicHamiltonian_smooth S ε κ hδ p).differentiable
    (by simp) (0 • (Pi.single i 1 : Fin d → ℂ))).hasFDerivAt.comp_hasDerivAt 0 hd
  congr 1
  simpa only [Function.comp_def, zero_smul] using h.deriv.symm

theorem amplitude_abs_le {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ)
    (a : Fin d → ℝ) (i : Fin d) : |amplitude S ε κ i a| ≤ |a i| := by
  have hd0 := DominanceCutoff.dominance_nonneg S ε i a
  have hd1 := DominanceCutoff.dominance_le_one S ε i a
  have hr0 := PrimitiveCutoffs.rho_nonneg (∑ j : Fin d, (S.B i j : ℝ) * a j)
  have hr1 := PrimitiveCutoffs.rho_le_one (∑ j : Fin d, (S.B i j : ℝ) * a j)
  have h3 : |amplitude S ε κ i a| ≤ |PrimitiveCutoffs.radial ε κ (a i)| := by
    unfold amplitude
    rw [abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg hr0]
    have h1 : |PrimitiveCutoffs.radial ε κ (a i)| * DominanceCutoff.dominance S ε i a ≤
        |PrimitiveCutoffs.radial ε κ (a i)| := by
      simpa using mul_le_mul_of_nonneg_left hd1
        (abs_nonneg (PrimitiveCutoffs.radial ε κ (a i)))
    have h2 : (0 : ℝ) ≤ |PrimitiveCutoffs.radial ε κ (a i)| *
        DominanceCutoff.dominance S ε i a := mul_nonneg (abs_nonneg _) hd0
    have h3 := mul_le_mul_of_nonneg_left hr1 h2
    linarith
  exact h3.trans (PrimitiveCutoffs.radial_abs_le hε hκ (a i))

theorem real_components_growth {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : S.Point), p ∈ initialTorus S →
      ∑ j : Fin d, |(logarithmicComponents S hdet ε κ δ p j).re| ≤
        C * ∑ j : Fin d, |TorusCorrection.A S p j| := by
  obtain ⟨C, hC, hb⟩ := PrimitiveCutoffs.vartheta_iteratedDeriv_bound hδ 1
  simp only [iteratedDeriv_one] at hb
  refine ⟨1 + C, by linarith, fun p hp => ?_⟩
  have hc (i : Fin d) : |radialCorrection S ε κ δ p i| ≤ |TorusCorrection.A S p i| * C := by
    unfold radialCorrection
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (amplitude_abs_le S hε hκ _ i) (hb _)
        (abs_nonneg _) (abs_nonneg _)
    · simp only [abs_zero]
      positivity
  calc
    _ ≤ ∑ j : Fin d, (1 + C) * |TorusCorrection.A S p j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [real_logarithmicComponents S hdet ε κ hδ p hp j]
      calc
        _ ≤ |TorusCorrection.A S p j| + |radialCorrection S ε κ δ p j| := abs_sub _ _
        _ ≤ |TorusCorrection.A S p j| + |TorusCorrection.A S p j| * C := add_le_add_right (hc j) _
        _ = _ := by ring
    _ = _ := (Finset.mul_sum ..).symm

include hdet in
/-- A fixed inverse of the entire weighted form matrix gives a uniform one-norm
bound. In particular this does not discard frozen columns or require d>0. The
weighted matrix is `K = E · diag D`, whose determinant is `∏ d_i` rather than
`1`; only `IsUnit` is needed, and that is `SeedAlgebra.isUnit_det_Kreal`. -/
theorem full_matrix_inverse_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y b : Fin d → ℝ),
      (∀ i, ∑ j : Fin d, (S.K i j : ℝ) * y j = b i) →
      (∑ j : Fin d, |y j|) ≤ C * ∑ j : Fin d, |b j| :=
  SeedAlgebra.exists_inverse_bound_Kreal S hdet

theorem chi_deriv_compactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (deriv (DominanceCutoff.chi ε)) := by
  apply HasCompactSupport.intro (K := Icc (-ε) (-ε / 2)) isCompact_Icc
  intro x hx
  have hh : x < -ε ∨ -ε / 2 < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  rcases hh with hx | hx
  · have he : DominanceCutoff.chi ε =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [eventually_lt_nhds hx] with t ht
      exact (DominanceCutoff.chi_eq_one_iff hε).2 ht.le
    rw [he.deriv_eq]
    simp
  · have he : DominanceCutoff.chi ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact (DominanceCutoff.chi_eq_zero_iff hε).2 ht.le
    rw [he.deriv_eq]
    simp

theorem chi_deriv_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv (DominanceCutoff.chi ε) x| ≤ C := by
  simpa only [iteratedDeriv_zero] using
    PrimitiveCutoffs.bounded_iteratedDeriv_of_compactSupport
      (contDiff_infty_iff_deriv.mp (DominanceCutoff.contDiff_chi ε)).2
      (chi_deriv_compactSupport hε) 0

theorem fderiv_dominance_apply (ε : ℝ) (i : Fin d) (a u : Fin d → ℝ) :
    fderiv ℝ (DominanceCutoff.dominance S ε i) a u =
      ∑ k ∈ DominanceCutoff.mutableNeighbors S i,
        (∏ l ∈ (DominanceCutoff.mutableNeighbors S i).erase k,
          DominanceCutoff.chi ε (a i - a l)) *
        (deriv (DominanceCutoff.chi ε) (a i - a k) * (u i - u k)) := by
  classical
  let ev (k : Fin d) : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hf (k : Fin d) :
      HasFDerivAt (fun x : Fin d → ℝ => DominanceCutoff.chi ε (x i - x k))
        (deriv (DominanceCutoff.chi ε) (a i - a k) • (ev i - ev k)) a :=
    (((DominanceCutoff.contDiff_chi ε).differentiable (by simp)
      (a i - a k)).hasDerivAt).comp_hasFDerivAt a (f := fun x : Fin d → ℝ => x i - x k)
      ((ev i).hasFDerivAt.sub (ev k).hasFDerivAt)
  have hd := (HasFDerivAt.finsetProd
    (u := DominanceCutoff.mutableNeighbors S i) (fun k _ => hf k)).fderiv
  change fderiv ℝ (fun x : Fin d → ℝ =>
    ∏ k ∈ DominanceCutoff.mutableNeighbors S i,
      DominanceCutoff.chi ε (x i - x k)) a u = _
  rw [hd]
  simp [ev, smul_eq_mul]

theorem dominance_partial_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : Fin d → ℝ) (i j : Fin d),
      |fderiv ℝ (DominanceCutoff.dominance S ε i) a (Pi.single j 1)| ≤ D := by
  obtain ⟨C, hC, hb⟩ := chi_deriv_bound hε
  refine ⟨∑ _k : Fin d, 2 * C, Finset.sum_nonneg (fun _ _ => by positivity), ?_⟩
  intro a i j
  have hv (k : Fin d) : |(Pi.single j 1 : Fin d → ℝ) k| ≤ 1 := by
    classical
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [fderiv_dominance_apply S ε i a (Pi.single j 1)]
  calc
    _ ≤ ∑ k ∈ DominanceCutoff.mutableNeighbors S i,
        |(∏ l ∈ (DominanceCutoff.mutableNeighbors S i).erase k,
          DominanceCutoff.chi ε (a i - a l)) *
        (deriv (DominanceCutoff.chi ε) (a i - a k) *
          ((Pi.single j 1 : Fin d → ℝ) i - (Pi.single j 1 : Fin d → ℝ) k))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ DominanceCutoff.mutableNeighbors S i, 2 * C := by
      apply Finset.sum_le_sum
      intro k _
      have hp0 : 0 ≤ ∏ l ∈ (DominanceCutoff.mutableNeighbors S i).erase k,
          DominanceCutoff.chi ε (a i - a l) :=
        Finset.prod_nonneg fun _ _ => DominanceCutoff.chi_nonneg _ _
      have hp1 : (∏ l ∈ (DominanceCutoff.mutableNeighbors S i).erase k,
          DominanceCutoff.chi ε (a i - a l)) ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => DominanceCutoff.chi_nonneg _ _)
          (fun _ _ => DominanceCutoff.chi_le_one _ _)
      have hv2 : |(Pi.single j 1 : Fin d → ℝ) i - (Pi.single j 1 : Fin d → ℝ) k| ≤ 2 :=
        (abs_sub _ _).trans (by linarith [hv i, hv k])
      rw [abs_mul, abs_mul, abs_of_nonneg hp0]
      calc
        _ ≤ 1 * (C * 2) := mul_le_mul hp1
          (mul_le_mul (hb _) hv2 (abs_nonneg _) hC)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
        _ = _ := by ring
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)

theorem fderiv_amplitude_apply (ε κ : ℝ) (i : Fin d) (a u : Fin d → ℝ) :
    fderiv ℝ (amplitude S ε κ i) a u =
      (deriv (PrimitiveCutoffs.radial ε κ) (a i) * u i *
          DominanceCutoff.dominance S ε i a +
        PrimitiveCutoffs.radial ε κ (a i) *
          fderiv ℝ (DominanceCutoff.dominance S ε i) a u) *
        PrimitiveCutoffs.rho (∑ k : Fin d, (S.B i k : ℝ) * a k) +
      (PrimitiveCutoffs.radial ε κ (a i) * DominanceCutoff.dominance S ε i a) *
        (deriv PrimitiveCutoffs.rho (∑ k : Fin d, (S.B i k : ℝ) * a k) *
          (∑ k : Fin d, (S.B i k : ℝ) * u k)) := by
  let ev (k : Fin d) : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  let row : (Fin d → ℝ) →L[ℝ] ℝ := ∑ k : Fin d, (S.B i k : ℝ) • ev k
  have hr := (((PrimitiveCutoffs.radial_smooth ε κ).differentiable (by simp)
    (a i)).hasDerivAt).comp_hasFDerivAt a (f := fun x : Fin d → ℝ => x i)
      (ev i).hasFDerivAt
  have hd := ((DominanceCutoff.contDiff_dominance S ε i).differentiable (by simp) a).hasFDerivAt
  have hρ := ((PrimitiveCutoffs.rho_smooth.differentiable (by simp)
    (row a)).hasDerivAt).comp_hasFDerivAt a (f := row) row.hasFDerivAt
  have h := (hr.mul hd).mul hρ
  have he : (fun x : Fin d → ℝ =>
      PrimitiveCutoffs.radial ε κ (x i) * DominanceCutoff.dominance S ε i x *
        PrimitiveCutoffs.rho (row x)) = amplitude S ε κ i := by
    funext x
    simp [amplitude, row, ev]
  change HasFDerivAt (fun x : Fin d → ℝ =>
    PrimitiveCutoffs.radial ε κ (x i) * DominanceCutoff.dominance S ε i x *
      PrimitiveCutoffs.rho (row x)) _ a at h
  rw [he] at h
  rw [h.fderiv]
  simp [row, ev, smul_eq_mul]
  ring

theorem amplitude_partial_bound {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : Fin d → ℝ) (i j : Fin d),
      |fderiv ℝ (amplitude S ε κ i) a (Pi.single j 1)| ≤
        K * (1 + ∑ k : Fin d, |a k|) := by
  obtain ⟨D, hD, hdom⟩ := dominance_partial_bound S hε
  obtain ⟨R, hR, hρ⟩ := PrimitiveCutoffs.rho_iteratedDeriv_bound 1
  simp only [iteratedDeriv_one] at hρ
  let B : ℝ := ∑ i : Fin d, ∑ j : Fin d, |(S.B i j : ℝ)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hentry (i j : Fin d) : |(S.B i j : ℝ)| ≤ B :=
    (Finset.single_le_sum (fun k _ => abs_nonneg (S.B i k : ℝ)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        abs_nonneg (S.B k l : ℝ)) (Finset.mem_univ i))
  refine ⟨1 + D + R * B, by positivity, ?_⟩
  intro a i j
  let U : ℝ := ∑ k : Fin d, |a k|
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha : |a i| ≤ U := Finset.single_le_sum (fun k _ => abs_nonneg (a k)) (Finset.mem_univ i)
  have hv : |(Pi.single j 1 : Fin d → ℝ) i| ≤ 1 := by
    classical
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hd0 := DominanceCutoff.dominance_nonneg S ε i a
  have hd1 := DominanceCutoff.dominance_le_one S ε i a
  have hp0 := PrimitiveCutoffs.rho_nonneg (∑ k : Fin d, (S.B i k : ℝ) * a k)
  have hp1 := PrimitiveCutoffs.rho_le_one (∑ k : Fin d, (S.B i k : ℝ) * a k)
  have hr : |PrimitiveCutoffs.radial ε κ (a i)| ≤ U :=
    (PrimitiveCutoffs.radial_abs_le hε hκ _).trans ha
  have hr' : |deriv (PrimitiveCutoffs.radial ε κ) (a i)| ≤ 1 := by
    rw [abs_of_nonneg (PrimitiveCutoffs.radial_deriv_nonneg hκ _)]
    exact PrimitiveCutoffs.radial_deriv_le_one hκ _
  have ht1 : |deriv (PrimitiveCutoffs.radial ε κ) (a i) *
      (Pi.single j 1 : Fin d → ℝ) i * DominanceCutoff.dominance S ε i a| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hd0]
    simpa using mul_le_mul (mul_le_mul hr' hv (abs_nonneg _) (by norm_num)) hd1 hd0
      (by norm_num : (0 : ℝ) ≤ 1 * 1)
  have ht2 : |PrimitiveCutoffs.radial ε κ (a i) *
      fderiv ℝ (DominanceCutoff.dominance S ε i) a (Pi.single j 1)| ≤ U * D := by
    rw [abs_mul]
    exact mul_le_mul hr (hdom a i j) (abs_nonneg _) hU
  have ht3 : |(PrimitiveCutoffs.radial ε κ (a i) * DominanceCutoff.dominance S ε i a) *
      (deriv PrimitiveCutoffs.rho (∑ k : Fin d, (S.B i k : ℝ) * a k) *
        (S.B i j : ℝ))| ≤ U * (R * B) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hd0]
    have ht : |PrimitiveCutoffs.radial ε κ (a i)| * DominanceCutoff.dominance S ε i a ≤ U := by
      simpa using mul_le_mul hr hd1 hd0 hU
    exact mul_le_mul ht (mul_le_mul (hρ _) (hentry i j) (abs_nonneg _) hR)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hU
  rw [fderiv_amplitude_apply S ε κ i a (Pi.single j 1)]
  have hs : (∑ k : Fin d, (S.B i k : ℝ) * (Pi.single j 1 : Fin d → ℝ) k) =
      (S.B i j : ℝ) := by
    classical
    simp [Pi.single_apply]
  rw [hs]
  calc
    _ ≤ (1 + U * D) * 1 + U * (R * B) := by
      apply (abs_add_le _ _).trans
      apply add_le_add _ ht3
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_mul ((abs_add_le _ _).trans (add_le_add ht1 ht2)) hp1 hp0
        (by positivity)
    _ ≤ (1 + D + R * B) * (1 + U) := by nlinarith [mul_nonneg hR hB]

theorem imaginary_components_growth {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : S.Point), p ∈ initialTorus S →
      ∑ j : Fin d, |(logarithmicComponents S hdet ε κ δ p j).im| ≤
        C * (1 + ∑ j : Fin d, |TorusCorrection.A S p j|) := by
  obtain ⟨K, hK, hKbound⟩ := amplitude_partial_bound S hε hκ
  obtain ⟨V, hV, hVbound⟩ := PrimitiveCutoffs.vartheta_iteratedDeriv_bound hδ 0
  simp only [iteratedDeriv_zero] at hVbound
  obtain ⟨N, hN, hNbound⟩ := full_matrix_inverse_bound S hdet
  let W : ℝ := ∑ i : Fin d, (S.D i : ℝ) * (V * K)
  have hW : 0 ≤ W :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (le_of_lt (by exact_mod_cast S.D_pos i)) (mul_nonneg hV hK)
  refine ⟨N * (∑ _j : Fin d, W), mul_nonneg hN (Finset.sum_nonneg fun _ _ => hW),
    fun p hp => ?_⟩
  let U : ℝ := 1 + ∑ j : Fin d, |TorusCorrection.A S p j|
  have hU : 0 ≤ U := by dsimp [U]; positivity
  let b (j : Fin d) := -differentialCovector (SmoothAtlas.presentation S hdet).manifold
    (TorusCorrection.H S ε κ δ) p (radialTangent S hdet p hp j)
  have hb (j : Fin d) : |b j| ≤ W * U := by
    dsimp [b]
    rw [abs_neg, differential_H_radial S hdet ε κ hδ p hp j]
    calc
      _ ≤ ∑ i ∈ S.mutable, |(S.D i : ℝ) * (TorusCorrection.angular S δ p i *
          fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S p) (Pi.single j 1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S.mutable, (S.D i : ℝ) * ((V * K) * U) := by
        apply Finset.sum_le_sum
        intro i _
        have hDi : (0 : ℝ) ≤ (S.D i : ℝ) := le_of_lt (by exact_mod_cast S.D_pos i)
        rw [abs_mul, abs_of_nonneg hDi, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hVbound _) (hKbound _ i j) (abs_nonneg _) hV) hDi
      _ ≤ ∑ i : Fin d, (S.D i : ℝ) * ((V * K) * U) :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => by
          have hDi : (0 : ℝ) ≤ (S.D i : ℝ) := le_of_lt (by exact_mod_cast S.D_pos i)
          have : (0 : ℝ) ≤ U := hU
          positivity)
      _ = W * U := by simp only [W, Finset.sum_mul, mul_assoc]
  calc
    _ ≤ N * ∑ j : Fin d, |b j| := hNbound _ b
      (fun j => angular_equation S hdet ε κ hδ p hp j)
    _ ≤ N * ∑ _j : Fin d, W * U :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hb j) hN
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]; rfl

/-- A point-independent linear growth bound for this actual native torus field.
No extension or complete flow is assumed. -/
theorem logarithmic_linear_growth {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : S.Point), p ∈ initialTorus S →
      (∑ j : Fin d, (|(logarithmicComponents S hdet ε κ δ p j).re| +
        |(logarithmicComponents S hdet ε κ δ p j).im|)) ≤
        C * (1 + ∑ j : Fin d, |TorusCorrection.A S p j|) := by
  have hk : 2 * ε < κ := by linarith
  obtain ⟨R, hR, hr⟩ := real_components_growth S hdet hε hk hδ
  obtain ⟨I, hI, hi⟩ := imaginary_components_growth S hdet hε hk hδ
  refine ⟨1 + R + I, by positivity, fun p hp => ?_⟩
  rw [Finset.sum_add_distrib]
  have hU : 0 ≤ ∑ j : Fin d, |TorusCorrection.A S p j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hh := add_le_add (hr p hp) (hi p hp)
  nlinarith

end ClusterSkeleton.TorusLiouvilleDynamics
