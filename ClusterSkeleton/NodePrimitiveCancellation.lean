import ClusterSkeleton.NodeLogExtension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The regular node primitive summand

On the explicit principal-log domain, the raw node coordinates are `(u,v)`.
This is a single regularized summand, not a global primitive or a claim about
residual cross terms. Every differential below is the native real derivative.
-/
noncomputable section
open scoped ContDiff Topology
open Set

namespace ClusterSkeleton.NodePrimitiveCancellation

abbrev E := ℂ × ℂ
abbrev Covector := E →L[ℝ] ℝ
abbrev OneForm := E [⋀^Fin 1]→L[ℝ] ℝ

def L (p : E) : ℂ := Complex.log (1 - p.1 * p.2)
def A (p : E) : ℝ := Real.log ‖p.1‖
def S (p : E) : ℝ := (L p).re
def T (p : E) : ℝ := (L p).im

def du : E →L[ℝ] ℂ := ContinuousLinearMap.fst ℝ ℂ ℂ
def dL (p : E) : E →L[ℝ] ℂ := fderiv ℝ L p
def dtheta (p : E) : Covector := Complex.imCLM.comp (p.1⁻¹ • du)

/-- The real parameter is inside the negative imaginary part. -/
def lambda (k : ℝ) (p : E) : Covector :=
  -(Complex.imCLM.comp (nodeLogQuotient p • du + (k : ℂ) • dL p))

def oneForm (k : ℝ) (p : E) : OneForm :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1) (lambda k p)

@[simp] theorem lambda_apply (k : ℝ) (p t : E) :
    lambda k p t = -(nodeLogQuotient p * t.1 + (k : ℂ) * fderiv ℝ L p t).im := rfl

@[simp] theorem oneForm_apply (k : ℝ) (p : E) (t : Fin 1 → E) :
    oneForm k p t = lambda k p (t 0) := rfl

theorem contDiffAt_L {p : E} (hp : p ∈ nodeLogDomain) : ContDiffAt ℝ ∞ L p :=
  ((Complex.contDiffAt_log hp).restrict_scalars ℝ).comp p
    (contDiffAt_const.sub (contDiffAt_fst.mul contDiffAt_snd))

/-- Actual real Fréchet derivative, with the denominator `uv-1`. -/
theorem fderiv_L {p : E} (hp : p ∈ nodeLogDomain) (t : E) :
    fderiv ℝ L p t = (p.2 * t.1 + p.1 * t.2) / (p.1 * p.2 - 1) := by
  have hd := (((hasFDerivAt_fst (𝕜 := ℂ) (p := p)).mul
    (hasFDerivAt_snd (𝕜 := ℂ))).const_sub (1 : ℂ)).clog hp
  change HasFDerivAt L _ p at hd
  rw [(hd.restrictScalars ℝ).fderiv]
  change (1 - p.1 * p.2)⁻¹ * -(p.1 * t.2 + p.2 * t.1) = _
  rw [show p.1 * p.2 - 1 = -(1 - p.1 * p.2) by ring]
  simp only [div_eq_mul_inv, inv_neg]
  ring

theorem contDiffAt_lambda (k : ℝ) {p : E} (hp : p ∈ nodeLogDomain) :
    ContDiffAt ℝ ∞ (lambda k) p := by
  have hQ := contDiffOn_nodeLogQuotient.contDiffAt (isOpen_nodeLogDomain.mem_nhds hp)
  have hd := (contDiffAt_L hp).fderiv_right (m := ∞) (by simp)
  exact ((contDiffAt_const.clm_comp
    ((hQ.smul contDiffAt_const).add (hd.const_smul (k : ℂ))))).neg

theorem contDiffOn_lambda (k : ℝ) : ContDiffOn ℝ ∞ (lambda k) nodeLogDomain :=
  fun _ hp => (contDiffAt_lambda k hp).contDiffWithinAt

theorem contDiffOn_oneForm (k : ℝ) : ContDiffOn ℝ ∞ (oneForm k) nodeLogDomain :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp_contDiffOn (contDiffOn_lambda k)

/-- A normalized logarithm germ proves the radial derivative at every nonzero
complex number, with no principal-argument restriction on that number. -/
theorem hasFDerivAt_A {p : E} (hu : p.1 ≠ 0) :
    HasFDerivAt A (Complex.reCLM.comp (p.1⁻¹ • du)) p := by
  have hdiv : HasFDerivAt (fun q : E => q.1 / p.1) (p.1⁻¹ • du) p := by
    convert du.hasFDerivAt.const_smul p.1⁻¹ using 1
    ext q
    simp [du, div_eq_mul_inv, smul_eq_mul, mul_comm]
  have hlog := (Complex.hasStrictFDerivAt_log_real
    (show p.1 / p.1 ∈ Complex.slitPlane by simp [hu])).hasFDerivAt.comp p hdiv
  have hg := (Complex.reCLM.hasFDerivAt.comp p hlog).const_add (Real.log ‖p.1‖)
  have he : (fun q : E => Real.log ‖p.1‖ + (Complex.log (q.1 / p.1)).re)
      =ᶠ[nhds p] A := by
    filter_upwards [(isOpen_ne.preimage continuous_fst).mem_nhds hu] with q hq
    change Real.log ‖p.1‖ + (Complex.log (q.1 / p.1)).re = Real.log ‖q.1‖
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hq)
      (norm_ne_zero_iff.mpr hu)]
    ring
  apply (hg.congr_of_eventuallyEq he.symm).congr_fderiv
  apply ContinuousLinearMap.ext
  intro t
  simp [hu]

theorem fderiv_A {p : E} (hu : p.1 ≠ 0) (t : E) :
    fderiv ℝ A p t = (t.1 / p.1).re := by
  rw [(hasFDerivAt_A hu).fderiv]
  simp [du, div_eq_mul_inv, mul_comm]

theorem fderiv_T {p : E} (hp : p ∈ nodeLogDomain) (t : E) :
    fderiv ℝ T p t = (fderiv ℝ L p t).im := by
  exact congrArg (fun f : E →L[ℝ] ℝ => f t)
    (Complex.imCLM.hasFDerivAt.comp p ((contDiffAt_L hp).differentiableAt (by simp)).hasFDerivAt).fderiv

/-- Product differentiation of the literal correction function. -/
theorem fderiv_correction (k : ℝ) {p : E} (hp : p ∈ nodeLogDomain)
    (hu : p.1 ≠ 0) (t : E) :
    fderiv ℝ (fun q => (A q + k) * T q) p t =
      (A p + k) * fderiv ℝ T p t + T p * (t.1 / p.1).re := by
  have hT : HasFDerivAt T (Complex.imCLM.comp (fderiv ℝ L p)) p :=
    Complex.imCLM.hasFDerivAt.comp p
      ((contDiffAt_L hp).differentiableAt (by simp)).hasFDerivAt
  have hprod := ((hasFDerivAt_A hu).add_const k).mul hT
  change HasFDerivAt (fun q => (A q + k) * T q) _ p at hprod
  rw [hprod.fderiv]
  rw [← hT.fderiv]
  simp [du, div_eq_mul_inv, mul_comm]

/-- Equality of native covectors, retaining both explicit domain hypotheses. -/
theorem cancellation (k : ℝ) {p : E} (hp : p ∈ nodeLogDomain) (hu : p.1 ≠ 0) :
    A p • fderiv ℝ T p - S p • dtheta p -
      fderiv ℝ (fun q => (A q + k) * T q) p = lambda k p := by
  apply ContinuousLinearMap.ext
  intro t
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [lambda_apply, fderiv_correction k hp hu t, fderiv_T hp t,
    nodeLogQuotient_eq_div hu]
  have he : Complex.log (1 - p.1 * p.2) / p.1 * t.1 = L p * (t.1 / p.1) := by
    unfold L
    ring
  rw [he]
  simp [dtheta, du, S, T, Complex.mul_im, div_eq_mul_inv, mul_comm]
  ring

/-- The same equality in the native alternating `Fin 1` representation. -/
theorem cancellation_oneForm (k : ℝ) {p : E} (hp : p ∈ nodeLogDomain) (hu : p.1 ≠ 0) :
    ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
      (A p • fderiv ℝ T p - S p • dtheta p -
        fderiv ℝ (fun q => (A q + k) * T q) p) = oneForm k p := by
  rw [cancellation k hp hu]
  rfl

/-- Every tangent direction at every point on the full zero divisor. -/
theorem lambda_zero (k : ℝ) (v : ℂ) (t : E) :
    lambda k (0, v) t = (1 + k) * (v * t.1).im := by
  rw [lambda_apply, nodeLogQuotient_zero, fderiv_L (zero_mem_nodeLogDomain v)]
  change -((-v) * t.1 + (k : ℂ) * ((v * t.1 + 0 * t.2) / (0 * v - 1))).im = _
  simp only [zero_mul, add_zero, zero_sub, div_neg, div_one,
    mul_neg, neg_mul, Complex.neg_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem oneForm_zero (k : ℝ) (v : ℂ) (t : Fin 1 → E) :
    oneForm k (0, v) t = (1 + k) * (v * (t 0).1).im := lambda_zero k v _

/-- A nonzero sign check: the coefficient is positive at k=1. -/
theorem numerical_sign : lambda 1 (0, Complex.I) (1, 0) = 2 := by
  rw [lambda_zero]
  norm_num

end ClusterSkeleton.NodePrimitiveCancellation
