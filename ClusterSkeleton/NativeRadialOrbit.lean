import ClusterSkeleton.ZeroStratumInvariance
import ClusterSkeleton.NormalizedPartnerNormDrift
import ClusterSkeleton.ScalarOrbitDynamics
import Mathlib.Topology.Order.Compact

/-! Radial consequences of the exact global native Liouville field. The time
domain is open, so the shifted equation has an ordinary derivative even at zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.NativeRadialOrbit

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

open GlobalLiouvilleField

/-- The two cutoff factors multiplying the radial cutoff have absolute value at most one. -/
theorem amplitude_abs_le_radial (ε κ : ℝ) (a : Fin d → ℝ) (j : Fin d) :
    |TorusLiouvilleDynamics.amplitude S ε κ j a| ≤
      |PrimitiveCutoffs.radial ε κ (a j)| := by
  have hd0 := DominanceCutoff.dominance_nonneg S ε j a
  have hd1 := DominanceCutoff.dominance_le_one S ε j a
  have hr0 := PrimitiveCutoffs.rho_nonneg (∑ k : Fin d, (S.B j k : ℝ) * a k)
  have hr1 := PrimitiveCutoffs.rho_le_one (∑ k : Fin d, (S.B j k : ℝ) * a k)
  have h1 := mul_le_mul_of_nonneg_left hd1
    (abs_nonneg (PrimitiveCutoffs.radial ε κ (a j)))
  have h2 := mul_le_mul_of_nonneg_left hr1
    (mul_nonneg (abs_nonneg (PrimitiveCutoffs.radial ε κ (a j))) hd0)
  simpa [TorusLiouvilleDynamics.amplitude, abs_mul,
    abs_of_nonneg hd0, abs_of_nonneg hr0] using
      h2.trans (by simpa using h1)

/-- A single constant controls the correction on every selected-coordinate nonzero locus.
Other coordinates may vanish. -/
theorem uniform_radial_error_bound {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : S.Point) (j : Fin d), p.a j ≠ 0 →
      |L S hdet ε κ hδ p j - A S p j| ≤
        C * |PrimitiveCutoffs.radial ε κ (A S p j)| := by
  obtain ⟨C, hC, hb⟩ := PrimitiveCutoffs.vartheta_iteratedDeriv_bound hδ 1
  simp only [iteratedDeriv_one] at hb
  have hc (q : S.Point) (j : Fin d) :
      |TorusLiouvilleDynamics.radialCorrection S ε κ δ q j| ≤
        C * |PrimitiveCutoffs.radial ε κ (TorusCorrection.A S q j)| := by
    unfold TorusLiouvilleDynamics.radialCorrection
    split_ifs
    · rw [abs_mul]
      calc
        _ ≤ |PrimitiveCutoffs.radial ε κ (TorusCorrection.A S q j)| * C :=
          mul_le_mul (amplitude_abs_le_radial S ε κ (TorusCorrection.A S q) j)
            (hb _) (abs_nonneg _) (abs_nonneg _)
        _ = _ := mul_comm _ _
    · simp only [abs_zero]
      exact mul_nonneg hC (abs_nonneg _)
  have ht (q : S.Point) (hq : q ∈ initialTorus S) (j : Fin d) :
      |L S hdet ε κ hδ q j - A S q j| ≤
        C * |PrimitiveCutoffs.radial ε κ (A S q j)| := by
    rw [L_eq_logarithmicComponents S hdet ε κ hδ q j (hq j),
      logarithmicComponents_eq_torus S hdet hε hκ hδ q hq,
      TorusLiouvilleDynamics.real_logarithmicComponents S hdet ε κ hδ q hq j]
    change |TorusCorrection.A S q j -
      TorusLiouvilleDynamics.radialCorrection S ε κ δ q j - TorusCorrection.A S q j| ≤ _
    rw [show TorusCorrection.A S q j -
      TorusLiouvilleDynamics.radialCorrection S ε κ δ q j - TorusCorrection.A S q j =
        -TorusLiouvilleDynamics.radialCorrection S ε κ δ q j by ring, abs_neg]
    exact hc q j
  refine ⟨C, hC, ?_⟩
  intro p j hj
  have hA := continuousAt_A S hdet p j hj
  apply le_of_dense_open (dense_initialTorus S hdet) (isOpen_nonzeroLocus S j) hj
    ((continuousAt_L S hdet hε hκ hδ p j hj).sub hA).abs
    (continuousAt_const.mul
      (((PrimitiveCutoffs.radial_smooth ε κ).continuous.continuousAt.comp hA).abs))
  intro q hq
  exact ht q hq.2 j

/-- Vanishing of the radial cutoff forces exact native radial drift. -/
theorem L_eq_A_of_radial_eq_zero {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) (hr : PrimitiveCutoffs.radial ε κ (A S p j) = 0) :
    L S hdet ε κ hδ p j = A S p j := by
  obtain ⟨C, _, hb⟩ := uniform_radial_error_bound S hdet hε hκ hδ
  have h := hb p j hj
  rw [hr, abs_zero, mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- The closed cutoff collar, including A = -2ε. -/
theorem L_eq_A_of_ge_cutoff {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) (ha : -2 * ε ≤ A S p j) :
    L S hdet ε κ hδ p j = A S p j :=
  L_eq_A_of_radial_eq_zero S hdet hε hκ hδ p j hj
    (PrimitiveCutoffs.radial_eq_zero (by linarith : 2 * ε < κ) ha)

/-- The scalar coefficient is derived from the actual native field. -/
def c (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) (j : Fin d) : ℝ :=
  (A S p j - L S hdet ε κ hδ p j) /
    PrimitiveCutoffs.radial ε κ (A S p j)

/-- The totalized quotient still gives the radial equation where the selected coordinate is nonzero. -/
theorem L_eq_A_sub_radial_mul_c {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) :
    L S hdet ε κ hδ p j = A S p j -
      PrimitiveCutoffs.radial ε κ (A S p j) * c S hdet ε κ hδ p j := by
  by_cases hr : PrimitiveCutoffs.radial ε κ (A S p j) = 0
  · rw [hr, zero_mul, sub_zero]
    exact L_eq_A_of_radial_eq_zero S hdet hε hκ hδ p j hj hr
  · dsimp only [c]
    rw [mul_div_cancel₀ _ hr]
    ring

/-- The scalar coefficient bound comes from the proved native negative drift estimate. -/
theorem c_le_one {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) : c S hdet ε κ hδ p j ≤ 1 := by
  have hk : 2 * ε < κ := by linarith
  unfold c
  by_cases hr : PrimitiveCutoffs.radial ε κ (A S p j) = 0
  · simp [hr]
  · have hrneg : PrimitiveCutoffs.radial ε κ (A S p j) < 0 :=
      lt_of_le_of_ne (PrimitiveCutoffs.radial_nonpos hk _) hr
    have ha : A S p j < 0 := by
      by_contra hn
      have hnonneg : 0 ≤ A S p j := not_lt.mp hn
      exact hr (PrimitiveCutoffs.radial_eq_zero hk (by linarith))
    apply (div_le_iff_of_neg hrneg).2
    have h := (L_negative_bound S hdet hε hκ hδ p j hj ha).1
    linarith


/-- The scalar chain rule at a point of an open time domain. -/
theorem hasDerivAt_A (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {t : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsOpen J) (ht : t ∈ J) (j : Fin d) (hj : (γ t).a j ≠ 0) :
    HasDerivAt (fun u => GlobalLiouvilleField.A S (γ u) j)
      (GlobalLiouvilleField.L S hdet ε κ hδ (γ t) j) t := by
  letI := SmoothAtlas.charts S hdet
  exact (NormalizedPartnerNormDrift.hasDerivWithinAt_scalar_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht
    ((GlobalLiouvilleField.contMDiffAt_A S hdet (γ t) j hj).mdifferentiableAt
      (by simp))).hasDerivAt (hJ.mem_nhds ht)

/-- One initial nonzero coordinate suffices on the entire open time interval. -/
theorem coordinate_ne_zero {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) {t : ℝ} (ht : t₀-η < t) :
    (γ t).a j ≠ 0 :=
  (ZeroStratumInvariance.coordinate_ne_zero_iff S hdet hε hκ hδ hγ
    isPreconnected_Ioi (show t₀ ∈ Ioi (t₀-η) by change t₀-η < t₀; linarith)
      ht j).mp hj

/-- Translation retains a genuine derivative at every forward time, including zero. -/
theorem shifted_hasDerivAt_A {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => GlobalLiouvilleField.A S (γ (t₀+u)) j)
      (GlobalLiouvilleField.L S hdet ε κ hδ (γ (t₀+t)) j) t := by
  have htime : t₀-η < t₀+t := by linarith
  have hd := hasDerivAt_A S hdet ε κ hδ hγ isOpen_Ioi htime j
    (coordinate_ne_zero S hdet hε hκ hδ hη hγ j hj htime)
  convert! hd.comp t ((hasDerivAt_id t).const_add t₀) using 1 <;> simp


/-- The accepted scalar equation is derived from the exact field and its derived coefficient. -/
theorem radialEquation {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) :
    ScalarOrbitDynamics.RadialEquation ε κ
      (fun t => A S (γ (t₀+t)) j) (fun t => c S hdet ε κ hδ (γ (t₀+t)) j) := by
  intro t ht
  exact (shifted_hasDerivAt_A S hdet hε hκ hδ hη hγ j hj ht).congr_deriv
    (L_eq_A_sub_radial_mul_c S hdet hε hκ hδ _ j
      (coordinate_ne_zero S hdet hε hκ hδ hη hγ j hj (by linarith)))

/-- All negative scalar consequences use the accepted scalar proofs unchanged. -/
theorem negative_log_laws {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) (hneg : A S (γ t₀) j < 0) :
    (∀ t ≥ 0, A S (γ (t₀+t)) j ≤ A S (γ t₀) j) ∧
    (∀ t ≥ 0, A S (γ (t₀+t)) j < 0) ∧
    AntitoneOn (fun t => A S (γ (t₀+t)) j) (Ici 0) ∧
    (∀ t ≥ 0, A S (γ (t₀+t)) j ≤ A S (γ t₀) j +
      (A S (γ t₀) j - PrimitiveCutoffs.radial ε κ (A S (γ t₀) j)) * t) ∧
    Tendsto (fun t => A S (γ (t₀+t)) j) atTop atBot ∧
    Tendsto (fun t => ‖(γ (t₀+t)).a j‖) atTop (𝓝 0) := by
  have hA := radialEquation S hdet hε hκ hδ hη hγ j hj
  have hc : ∀ t, 0 ≤ t → c S hdet ε κ hδ (γ (t₀+t)) j ≤ 1 := by
    intro t ht
    exact c_le_one S hdet hε hκ hδ _ j
      (coordinate_ne_zero S hdet hε hκ hδ hη hγ j hj (by linarith))
  have h0 : A S (γ (t₀+0)) j < 0 := by simpa using hneg
  refine ⟨?_, ?_, ScalarOrbitDynamics.radial_antitone hε hκ hA hc h0, ?_,
    ScalarOrbitDynamics.radial_tendsto_atBot hε hκ hA hc h0, ?_⟩
  · intro t ht
    simpa only [add_zero] using ScalarOrbitDynamics.radial_le_initial hε hκ hA hc h0 ht
  · intro t ht
    exact ScalarOrbitDynamics.radial_negative hε hκ hA hc h0 ht
  · intro t ht
    simpa only [add_zero] using ScalarOrbitDynamics.radial_affine_bound hε hκ hA hc h0 ht
  · apply (ScalarOrbitDynamics.radial_exp_tendsto_zero hε hκ hA hc h0).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Real.exp_log (norm_pos_iff.mpr
      (coordinate_ne_zero S hdet hε hκ hδ hη hγ j hj (by linarith)))

/-- Nonnegative log radii obey the exact positive exponential law. -/
theorem nonnegative_log_law {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) (hpos : 0 ≤ A S (γ t₀) j)
    {t : ℝ} (ht : 0 ≤ t) : A S (γ (t₀+t)) j = A S (γ t₀) j * Real.exp t := by
  simpa only [add_zero] using ScalarOrbitDynamics.radial_eq_exp_of_nonneg hε hκ
    (radialEquation S hdet hε hκ hδ hη hγ j hj) (by simpa using hpos) ht

/-- Positive case of the accepted scalar theorem on the actual native curve. -/
theorem positive_log_law {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) (hpos : 0 < A S (γ t₀) j)
    {t : ℝ} (ht : 0 ≤ t) : A S (γ (t₀+t)) j = A S (γ t₀) j * Real.exp t := by
  simpa only [add_zero] using ScalarOrbitDynamics.radial_positive hε hκ
    (radialEquation S hdet hε hκ hδ hη hγ j hj) (by simpa using hpos) ht

/-- Zero initial logarithm is rigid, with no caller-supplied sign law. -/
theorem zero_log_law {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (Z S hdet ε κ hδ) (Ioi (t₀-η)))
    (j : Fin d) (hj : (γ t₀).a j ≠ 0) (hzero : A S (γ t₀) j = 0)
    {t : ℝ} (ht : 0 ≤ t) : A S (γ (t₀+t)) j = 0 :=
  ScalarOrbitDynamics.radial_zero hε hκ
    (radialEquation S hdet hε hκ hδ hη hγ j hj) (by simpa using hzero) ht

/-- Escape follows from bounded actual coordinate norms on any compact set;
no continuity of a mutable logarithm on that compact set is used. -/
theorem eventually_not_mem_compact {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (j : Fin d) (hnorm : 1 < ‖(γ t₀).a j‖)
    {K : Set S.Point} (hK : IsCompact K) :
    ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image
    (continuous_originalCoordinate S j).norm.continuousOn
  let a₀ := GlobalLiouvilleField.A S (γ t₀) j
  have ha₀ : 0 < a₀ := Real.log_pos hnorm
  have hnonzero : (γ t₀).a j ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨max t₀ (t₀ + (M / a₀ + 1)), le_max_left _ _, ?_⟩
  intro t ht hmem
  have ht₀ : 0 ≤ t - t₀ := by linarith [(le_max_left _ _).trans ht]
  have he := positive_log_law S hdet hε hκ hδ hη hγ j hnonzero ha₀ ht₀
  have hshift : t₀ + (t - t₀) = t := by ring
  rw [hshift] at he
  have hbound : a₀ * Real.exp (t - t₀) ≤ M := by
    rw [← he]
    exact (Real.log_le_self (norm_nonneg _)).trans (hM ⟨γ t, hmem, rfl⟩)
  have hlow : M / a₀ + 1 ≤ t - t₀ := by
    linarith [(le_max_right t₀ (t₀ + (M / a₀ + 1))).trans ht]
  have hlowmul := mul_le_mul_of_nonneg_left hlow ha₀.le
  have hexp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t - t₀)) ha₀.le
  have hcancel := div_mul_cancel₀ M (ne_of_gt ha₀)
  nlinarith

theorem not_isCompact_closure_forward_image {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (j : Fin d) (hnorm : 1 < ‖(γ t₀).a j‖) :
    ¬ IsCompact (closure (γ '' Ici t₀)) := by
  intro hK
  obtain ⟨T, hT, hescape⟩ :=
    eventually_not_mem_compact S hdet hε hκ hδ hη hγ j hnorm hK
  exact hescape T le_rfl (subset_closure ⟨T, hT, rfl⟩)

/-- A supplied native flow for the precise global field has no trapped point
with any original coordinate outside the unit disk. -/
theorem original_norm_le_one_of_mem_trappedSet {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) univ)
    {p : S.Point} (hp : p ∈ trappedSet flow) (j : Fin d) : ‖p.a j‖ ≤ 1 := by
  letI := SmoothAtlas.charts S hdet
  by_contra hnot
  have hnorm : 1 < ‖p.a j‖ := lt_of_not_ge hnot
  have hγ : IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi ((0 : ℝ) - 1)) :=
    (hflow p).mono (subset_univ _)
  have horbit : (fun t => flow t p) '' Ici 0 = flow.forwardOrbit p := by
    rw [flow.forwardOrbit_eq_range_nonneg]
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, rfl⟩
  have hcompact : IsCompact (closure ((fun t => flow t p) '' Ici 0)) := by
    rw [horbit]
    exact hp
  exact not_isCompact_closure_forward_image S hdet hε hκ hδ
    (show (0 : ℝ) < 1 by norm_num) hγ j
    (by simpa only [Flow.map_zero_apply] using hnorm) hcompact

/-- The frozen ODE required by ScalarOrbitDynamics is derived by the native
manifold chain rule and the exact global field's frozen radial equation. -/
theorem frozen_log_hasDerivAt {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) univ)
    (f : Fin d) (hf : f ∉ S.mutable) (p : S.Point) (t : ℝ) :
    HasDerivAt (fun s => Real.log ‖(flow s p).a f‖)
      (Real.log ‖(flow t p).a f‖) t := by
  letI := SmoothAtlas.charts S hdet
  have hd := hasDerivAt_A S hdet ε κ hδ (hflow p) isOpen_univ (mem_univ t) f
    ((flow t p).frozen_ne_zero f hf)
  exact hd.congr_deriv
    (GlobalLiouvilleField.frozen_radial_equation S hdet hε hκ hδ (flow t p) f hf)

theorem frozen_norm_eq_one_of_mem_trappedSet {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) univ)
    {p : S.Point} (hp : p ∈ trappedSet flow) (f : Fin d) (hf : f ∉ S.mutable) :
    ‖p.a f‖ = 1 :=
  ScalarOrbitDynamics.trapped_frozen_norm_eq_one flow f hf
    (frozen_log_hasDerivAt S hdet hε hκ hδ flow hflow f hf) hp

/-- Necessary radial restrictions for the supplied flow's independently defined
trapped set; this does not assert the full coordinate-cap identification. -/
theorem trapped_radial_restrictions {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) univ)
    {p : S.Point} (hp : p ∈ trappedSet flow) :
    (∀ j : Fin d, ‖p.a j‖ ≤ 1) ∧ (∀ f : Fin d, f ∉ S.mutable → ‖p.a f‖ = 1) :=
  ⟨fun j => original_norm_le_one_of_mem_trappedSet S hdet hε hκ hδ flow hflow hp j,
    fun f hf => frozen_norm_eq_one_of_mem_trappedSet S hdet hε hκ hδ flow hflow hp f hf⟩


end ClusterSkeleton.NativeRadialOrbit
