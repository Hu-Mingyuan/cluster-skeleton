import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Scalar functions used in (2.5)--(2.7) of acyclic_cluster_HMS.pdf, p. 10.
All derivatives and smoothness assertions use native Mathlib calculus.
-/
noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace ClusterSkeleton.PrimitiveCutoffs

/-- A fixed smooth real cutoff with values in `[0,1]`. -/
def rho (x : ℝ) : ℝ := Real.smoothTransition (2 - x ^ 2)

theorem rho_smooth : ContDiff ℝ ∞ rho := by
  unfold rho
  fun_prop

theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _
theorem rho_le_one (x : ℝ) : rho x ≤ 1 := Real.smoothTransition.le_one _

theorem rho_eq_one {x : ℝ} (hx : |x| ≤ 1) : rho x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mpr hx
  nlinarith [sq_abs x]

theorem rho_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : rho x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg x)).mpr hx
  nlinarith [sq_abs x]

theorem rho_compactSupport : HasCompactSupport rho := by
  apply HasCompactSupport.intro (K := Icc (-2 : ℝ) 2) isCompact_Icc
  intro x hx
  apply rho_eq_zero
  by_contra h
  have habs : |x| < 2 := lt_of_not_ge h
  exact hx ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2.le⟩

/-- Compact support gives uniform bounds for every native iterated derivative. -/
theorem bounded_iteratedDeriv_of_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n f x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := hs.exists_bound_iteratedFDeriv hf n
  refine ⟨C, hC, fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb n le_rfl x

theorem rho_iteratedDeriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n rho x| ≤ C :=
  bounded_iteratedDeriv_of_compactSupport rho_smooth rho_compactSupport n

/-- The primitive vanishing on the negative half-line. -/
def transitionPrimitive (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.smoothTransition t

theorem transitionPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt transitionPrimitive (Real.smoothTransition x) x :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem transitionPrimitive_deriv : deriv transitionPrimitive = Real.smoothTransition :=
  funext fun x => (transitionPrimitive_hasDerivAt x).deriv

theorem transitionPrimitive_smooth : ContDiff ℝ ∞ transitionPrimitive := by
  rw [contDiff_infty_iff_deriv, transitionPrimitive_deriv]
  exact ⟨fun x => (transitionPrimitive_hasDerivAt x).differentiableAt,
    Real.smoothTransition.contDiff⟩

theorem transitionPrimitive_zero {x : ℝ} (hx : x ≤ 0) : transitionPrimitive x = 0 := by
  unfold transitionPrimitive
  calc
    _ = ∫ _ in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hx] at ht
      exact Real.smoothTransition.zero_of_nonpos ht.2
    _ = 0 := by simp

theorem transitionPrimitive_nonneg (x : ℝ) : 0 ≤ transitionPrimitive x := by
  by_cases hx : x ≤ 0
  · rw [transitionPrimitive_zero hx]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge hx)
      Real.smoothTransition.nonneg

theorem transitionPrimitive_le {x : ℝ} (hx : 0 ≤ x) : transitionPrimitive x ≤ x := by
  have := intervalIntegral.integral_mono_on (μ := volume) hx
    (Real.smoothTransition.continuous.intervalIntegrable 0 x)
    (continuous_const.intervalIntegrable 0 x)
    (fun t (_ : t ∈ Icc 0 x) => Real.smoothTransition.le_one t)
  simpa [transitionPrimitive] using this

theorem smoothTransition_reflect (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  have hd := (Real.smoothTransition.pos_denom x).ne'
  have he : 1 - (1 - x) = x := by ring
  rw [he, add_comm (expNegInvGlue (1 - x))]
  field_simp [hd]
  ring

theorem transitionPrimitive_one : transitionPrimitive 1 = 1 / 2 := by
  have he := intervalIntegral.integral_comp_sub_left Real.smoothTransition
    (a := (0 : ℝ)) (b := 1) 1
  simp only [sub_self, sub_zero] at he
  have hi : (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x)) =
      1 - transitionPrimitive 1 := by
    simp_rw [smoothTransition_reflect]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 1)
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)]
    simp [transitionPrimitive]
  change _ = transitionPrimitive 1 at he
  linarith

theorem transitionPrimitive_tail {x : ℝ} (hx : 1 ≤ x) :
    transitionPrimitive x = x - 1 / 2 := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.smoothTransition.continuous.intervalIntegrable 0 1)
    (Real.smoothTransition.continuous.intervalIntegrable 1 x)
  have hi : (∫ t in (1 : ℝ)..x, Real.smoothTransition t) = x - 1 := by
    calc
      _ = ∫ _ in (1 : ℝ)..x, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hx] at ht
        exact Real.smoothTransition.one_of_one_le ht.1
      _ = x - 1 := by simp
  change transitionPrimitive 1 + _ = transitionPrimitive x at he
  rw [transitionPrimitive_one, hi] at he
  linarith

/-- Transition length, chosen to give the prescribed intercept exactly. -/
def radialLength (ε κ : ℝ) : ℝ := 2 * (κ - 2 * ε)

/-- Concrete radial cutoff from (2.6). -/
def radial (ε κ A : ℝ) : ℝ :=
  -radialLength ε κ * transitionPrimitive ((-A - 2 * ε) / radialLength ε κ)

theorem radial_smooth (ε κ : ℝ) : ContDiff ℝ ∞ (radial ε κ) := by
  unfold radial
  exact contDiff_const.mul (transitionPrimitive_smooth.comp (by fun_prop))

theorem radial_length_pos {ε κ : ℝ} (hκ : 2 * ε < κ) : 0 < radialLength ε κ := by
  unfold radialLength
  linarith

theorem radial_hasDerivAt {ε κ : ℝ} (hκ : 2 * ε < κ) (A : ℝ) :
    HasDerivAt (radial ε κ)
      (Real.smoothTransition ((-A - 2 * ε) / radialLength ε κ)) A := by
  have hL := (radial_length_pos hκ).ne'
  convert ((transitionPrimitive_hasDerivAt ((-A - 2 * ε) / radialLength ε κ)).comp A
    (((hasDerivAt_id A).neg.sub_const (2 * ε)).div_const (radialLength ε κ))).const_mul
    (-radialLength ε κ) using 1
  · rfl
  · field_simp


theorem radial_deriv {ε κ : ℝ} (hκ : 2 * ε < κ) (A : ℝ) :
    deriv (radial ε κ) A =
      Real.smoothTransition ((-A - 2 * ε) / radialLength ε κ) :=
  (radial_hasDerivAt hκ A).deriv

theorem radial_deriv_nonneg {ε κ : ℝ} (hκ : 2 * ε < κ) (A : ℝ) :
    0 ≤ deriv (radial ε κ) A := by
  rw [radial_deriv hκ]
  exact Real.smoothTransition.nonneg _

theorem radial_deriv_le_one {ε κ : ℝ} (hκ : 2 * ε < κ) (A : ℝ) :
    deriv (radial ε κ) A ≤ 1 := by
  rw [radial_deriv hκ]
  exact Real.smoothTransition.le_one _

theorem radial_nonpos {ε κ : ℝ} (hκ : 2 * ε < κ) (A : ℝ) : radial ε κ A ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (radial_length_pos hκ).le)
    (transitionPrimitive_nonneg _)

theorem radial_eq_zero {ε κ A : ℝ} (hκ : 2 * ε < κ) (hA : -2 * ε ≤ A) :
    radial ε κ A = 0 := by
  unfold radial
  rw [transitionPrimitive_zero (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (radial_length_pos hκ).le), mul_zero]

theorem radial_tail {ε κ A : ℝ} (hκ : 2 * ε < κ)
    (hA : A ≤ -radialLength ε κ - 2 * ε) : radial ε κ A = A + κ := by
  have hL := radial_length_pos hκ
  have hx : 1 ≤ (-A - 2 * ε) / radialLength ε κ :=
    (le_div_iff₀ hL).mpr (by linarith)
  rw [radial, transitionPrimitive_tail hx]
  field_simp
  simp only [radialLength]
  ring

theorem radial_gt {ε κ A : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) (hA : A < 0) :
    A < radial ε κ A := by
  by_cases h : -2 * ε ≤ A
  · rw [radial_eq_zero hκ h]
    exact hA
  · have hL := radial_length_pos hκ
    have hx : 0 ≤ (-A - 2 * ε) / radialLength ε κ :=
      div_nonneg (by linarith) hL.le
    have hb := mul_le_mul_of_nonneg_left (transitionPrimitive_le hx) hL.le
    have he : radialLength ε κ * ((-A - 2 * ε) / radialLength ε κ) = -A - 2 * ε :=
      mul_div_cancel₀ _ hL.ne'
    rw [he] at hb
    unfold radial
    nlinarith

/-- A support radius strictly smaller than the requested principal arc. -/
def angularRadius (δ : ℝ) : ℝ := min (δ / 2) (Real.pi / 4)

theorem angularRadius_pos {δ : ℝ} (hδ : 0 < δ) : 0 < angularRadius δ := by
  exact lt_min (by linarith) (by positivity)

theorem angularRadius_le_quarter (δ : ℝ) : angularRadius δ ≤ Real.pi / 4 :=
  min_le_right _ _

theorem angularRadius_lt {δ : ℝ} (hδ : 0 < δ) : angularRadius δ < δ := by
  have := min_le_left (δ / 2) (Real.pi / 4)
  unfold angularRadius
  linarith

/-- A periodic smooth cutoff selected using cosine, with its singular angles excluded. -/
def angularWindow (δ T : ℝ) : ℝ :=
  Real.smoothTransition ((Real.cos T - Real.cos (angularRadius δ)) /
    (Real.cos (angularRadius δ / 2) - Real.cos (angularRadius δ)))

/-- A concrete periodic angular function; no choice of an angle representative occurs. -/
def vartheta (δ T : ℝ) : ℝ := Real.arcsin (Real.sin T) * angularWindow δ T

theorem angular_den_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < Real.cos (angularRadius δ / 2) - Real.cos (angularRadius δ) := by
  have hr := angularRadius_pos hδ
  have hb := angularRadius_le_quarter δ
  exact sub_pos.mpr (Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith)
    (by linarith [Real.pi_pos]) (by linarith))

theorem angular_cos_pos {δ : ℝ} (hδ : 0 < δ) : 0 < Real.cos (angularRadius δ) := by
  apply Real.cos_pos_of_mem_Ioo
  have := angularRadius_pos hδ
  have := angularRadius_le_quarter δ
  constructor <;> linarith [Real.pi_pos]

theorem angularWindow_smooth (δ : ℝ) : ContDiff ℝ ∞ (angularWindow δ) := by
  unfold angularWindow
  fun_prop

theorem angularWindow_nonneg (δ T : ℝ) : 0 ≤ angularWindow δ T :=
  Real.smoothTransition.nonneg _

theorem angularWindow_le_one (δ T : ℝ) : angularWindow δ T ≤ 1 :=
  Real.smoothTransition.le_one _

theorem angularWindow_zero {δ T : ℝ} (hδ : 0 < δ)
    (hT : Real.cos T ≤ Real.cos (angularRadius δ)) : angularWindow δ T = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hT) (angular_den_pos hδ).le

theorem angularWindow_one {δ T : ℝ} (hδ : 0 < δ)
    (hT : |T| ≤ angularRadius δ / 2) : angularWindow δ T = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (angular_den_pos hδ)).mpr
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg T)
    (show angularRadius δ / 2 ≤ Real.pi by
      have := angularRadius_le_quarter δ
      linarith [Real.pi_pos]) hT
  rw [Real.cos_abs] at hc
  linarith

theorem vartheta_periodic (δ : ℝ) : Function.Periodic (vartheta δ) (2 * Real.pi) := by
  intro T
  simp [vartheta, angularWindow, Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem vartheta_representative_independent (δ T : ℝ) (k : ℤ) :
    vartheta δ (T + k * (2 * Real.pi)) = vartheta δ T := by
  simpa only [zsmul_eq_mul] using (vartheta_periodic δ).zsmul k T

theorem vartheta_eq_self {δ T : ℝ} (hδ : 0 < δ)
    (hT : |T| ≤ angularRadius δ / 2) : vartheta δ T = T := by
  rw [vartheta, angularWindow_one hδ hT, mul_one]
  apply Real.arcsin_sin
  all_goals
    have := angularRadius_le_quarter δ
    have hTa := abs_le.mp hT
    linarith [Real.pi_pos]

theorem vartheta_zero_of_radius_le {δ T : ℝ} (hδ : 0 < δ)
    (hT : |T| ≤ Real.pi) (hr : angularRadius δ ≤ |T|) : vartheta δ T = 0 := by
  rw [vartheta, angularWindow_zero hδ, mul_zero]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (angularRadius_pos hδ).le hT hr
  simpa only [Real.cos_abs] using hc

theorem vartheta_support_principal {δ T : ℝ} (hδ : 0 < δ)
    (hT : |T| ≤ Real.pi) (hn : vartheta δ T ≠ 0) : |T| < δ := by
  have hr : |T| < angularRadius δ := by
    by_contra h
    exact hn (vartheta_zero_of_radius_le hδ hT (le_of_not_gt h))
  exact hr.trans (angularRadius_lt hδ)

theorem vartheta_local_sign {δ T : ℝ} (hδ : 0 < δ) (hT : |T| ≤ Real.pi) :
    0 ≤ T * vartheta δ T := by
  by_cases hr : angularRadius δ ≤ |T|
  · rw [vartheta_zero_of_radius_le hδ hT hr, mul_zero]
  · have ha : Real.arcsin (Real.sin T) = T := by
      apply Real.arcsin_sin
      all_goals
        have ht := abs_lt.mp (lt_of_not_ge hr)
        have := angularRadius_le_quarter δ
        linarith [Real.pi_pos]
    rw [vartheta, ha, ← mul_assoc]
    exact mul_nonneg (mul_self_nonneg T) (angularWindow_nonneg δ T)

/-- The angular function is locally zero wherever cosine is below the support threshold. -/
theorem vartheta_eventually_zero {δ T : ℝ} (hδ : 0 < δ)
    (hT : Real.cos T < Real.cos (angularRadius δ)) :
    vartheta δ =ᶠ[𝓝 T] fun _ => 0 := by
  filter_upwards [Real.continuous_cos.continuousAt.eventually_lt_const hT] with t ht
  simp [vartheta, angularWindow_zero hδ ht.le]

/-- Even the closed topological support lies in the requested principal arc. -/
theorem vartheta_tsupport_principal {δ T : ℝ} (hδ : 0 < δ)
    (hT : |T| ≤ Real.pi) (hs : T ∈ tsupport (vartheta δ)) : |T| < δ := by
  by_contra h
  have hr : angularRadius δ < |T| := (angularRadius_lt hδ).trans_le (le_of_not_gt h)
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (angularRadius_pos hδ).le hT hr
  rw [Real.cos_abs] at hc
  exact (notMem_tsupport_iff_eventuallyEq.mpr (vartheta_eventually_zero hδ hc)) hs

theorem vartheta_smooth {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (vartheta δ) := by
  rw [contDiff_iff_contDiffAt]
  intro T
  by_cases hT : Real.cos T < Real.cos (angularRadius δ)
  · exact contDiffAt_const.congr_of_eventuallyEq (vartheta_eventually_zero hδ hT)
  · have hc : 0 < Real.cos T := (angular_cos_pos hδ).trans_le (le_of_not_gt hT)
    have hs : Real.sin T ≠ -1 ∧ Real.sin T ≠ 1 := by
      have he := Real.sin_sq_add_cos_sq T
      constructor <;> intro h <;> rw [h] at he <;> nlinarith
    exact ((Real.contDiffAt_arcsin hs.1 hs.2).comp T Real.contDiff_sin.contDiffAt).mul
      (angularWindow_smooth δ).contDiffAt

theorem vartheta_deriv_le_one {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    deriv (vartheta δ) T ≤ 1 := by
  by_cases hc : 0 < Real.cos T
  · have hs : Real.sin T ≠ -1 ∧ Real.sin T ≠ 1 := by
      have he := Real.sin_sq_add_cos_sq T
      constructor <;> intro h <;> rw [h] at he <;> nlinarith
    have hsqrt : Real.sqrt (1 - Real.sin T ^ 2) = Real.cos T := by
      rw [show 1 - Real.sin T ^ 2 = Real.cos T ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq T], Real.sqrt_sq hc.le]
    have ha : HasDerivAt (fun t => Real.arcsin (Real.sin t)) 1 T := by
      convert (Real.hasDerivAt_arcsin hs.1 hs.2).comp T (Real.hasDerivAt_sin T) using 1
      · rfl
      rw [hsqrt]
      field_simp
    let d := Real.cos (angularRadius δ / 2) - Real.cos (angularRadius δ)
    let u := (Real.cos T - Real.cos (angularRadius δ)) / d
    have hw : HasDerivAt (angularWindow δ)
        (deriv Real.smoothTransition u * (-Real.sin T / d)) T := by
      exact (((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)) u).hasDerivAt.comp T
        (((Real.hasDerivAt_cos T).sub_const _).div_const d)
    have hd : deriv (vartheta δ) T =
        angularWindow δ T + Real.arcsin (Real.sin T) *
          (deriv Real.smoothTransition u * (-Real.sin T / d)) := by
      have hv : HasDerivAt (vartheta δ)
          (1 * angularWindow δ T + Real.arcsin (Real.sin T) *
            (deriv Real.smoothTransition u * (-Real.sin T / d))) T := ha.mul hw
      simpa only [one_mul] using hv.deriv
    have hsign : 0 ≤ Real.arcsin (Real.sin T) * Real.sin T := by
      rcases le_total 0 (Real.sin T) with h | h
      · exact mul_nonneg (Real.arcsin_nonneg.mpr h) h
      · exact mul_nonneg_of_nonpos_of_nonpos (Real.arcsin_nonpos.mpr h) h
    have hb : 0 ≤ (Real.arcsin (Real.sin T) * Real.sin T) *
        deriv Real.smoothTransition u / d :=
      div_nonneg (mul_nonneg hsign Real.smoothTransition.monotone.deriv_nonneg)
        (angular_den_pos hδ).le
    rw [hd]
    calc
      _ = angularWindow δ T - (Real.arcsin (Real.sin T) * Real.sin T) *
          deriv Real.smoothTransition u / d := by ring
      _ ≤ 1 := by linarith [angularWindow_le_one δ T]
  · have he := vartheta_eventually_zero hδ
      ((le_of_not_gt hc).trans_lt (angular_cos_pos hδ))
    rw [he.deriv_eq]
    simp

theorem periodic_iteratedDeriv {f : ℝ → ℝ} {p : ℝ} (hf : Function.Periodic f p)
    (n : ℕ) : Function.Periodic (iteratedDeriv n f) p := by
  intro x
  have he : (fun t => f (t + p)) = f := funext hf
  have hi := congr_fun (iteratedDeriv_comp_add_const n f p) x
  rw [he] at hi
  exact hi.symm

theorem bounded_iteratedDeriv_of_periodic {f : ℝ → ℝ} {p : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f p) (hp0 : p ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n f x| ≤ C := by
  have hper : Function.Periodic (fun x => |iteratedDeriv n f x|) p :=
    (periodic_iteratedDeriv hp n).comp abs
  have hcon : Continuous (fun x => |iteratedDeriv n f x|) :=
    (hf.continuous_iteratedDeriv n (by simp)).abs
  obtain ⟨C, hC⟩ := (hper.compact_of_continuous hp0 hcon).bddAbove
  exact ⟨max 0 C, le_max_left _ _, fun x => (hC (mem_range_self x)).trans (le_max_right _ _)⟩

theorem vartheta_iteratedDeriv_bound {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T, |iteratedDeriv n (vartheta δ) T| ≤ C :=
  bounded_iteratedDeriv_of_periodic (vartheta_smooth hδ) (vartheta_periodic δ)
    (by positivity) n

theorem radial_abs_le {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) (A : ℝ) :
    |radial ε κ A| ≤ |A| := by
  rw [abs_of_nonpos (radial_nonpos hκ A)]
  by_cases hA : A < 0
  · rw [abs_of_neg hA]
    linarith [radial_gt hε hκ hA]
  · rw [radial_eq_zero hκ (by linarith)]
    simp

theorem radial_linear_growth {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A, |radial ε κ A| ≤ C * (1 + |A|) := by
  refine ⟨1, one_pos, fun A => ?_⟩
  have := radial_abs_le hε hκ A
  linarith

theorem radial_secondDeriv_compactSupport {ε κ : ℝ} (hκ : 2 * ε < κ) :
    HasCompactSupport (deriv (deriv (radial ε κ))) := by
  apply HasCompactSupport.intro
    (K := Icc (-radialLength ε κ - 2 * ε) (-2 * ε)) isCompact_Icc
  intro A hA
  have hh : A < -radialLength ε κ - 2 * ε ∨ -2 * ε < A := by
    simpa only [mem_Icc, not_and_or, not_le] using hA
  rcases hh with hA | hA
  · have he : radial ε κ =ᶠ[𝓝 A] fun t => t + κ := by
      filter_upwards [eventually_lt_nhds hA] with t ht
      exact radial_tail hκ ht.le
    rw [he.deriv.deriv_eq]
    simp
  · have he : radial ε κ =ᶠ[𝓝 A] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds hA] with t ht
      exact radial_eq_zero hκ ht.le
    rw [he.deriv.deriv_eq]
    simp

theorem radial_iteratedDeriv_bound {ε κ : ℝ} (hκ : 2 * ε < κ)
    (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A, |iteratedDeriv n (radial ε κ) A| ≤ C := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, fun A => ?_⟩
      simpa only [Nat.zero_add, iteratedDeriv_one, abs_of_nonneg (radial_deriv_nonneg hκ A)] using
        radial_deriv_le_one hκ A
    | succ n =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      apply bounded_iteratedDeriv_of_compactSupport
      · exact (contDiff_infty_iff_deriv.mp
          (contDiff_infty_iff_deriv.mp (radial_smooth ε κ)).2).2
      · exact radial_secondDeriv_compactSupport hκ

end ClusterSkeleton.PrimitiveCutoffs
