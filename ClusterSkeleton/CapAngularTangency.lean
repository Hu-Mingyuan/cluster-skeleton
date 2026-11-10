import ClusterSkeleton.AllStrataGrowth
import ClusterSkeleton.CapIndependence

/-! Pointwise angular tangency of the independently defined coordinate cap.
The statements concern the exact native Liouville field on the literal exchange
points. They do not assert forward invariance or propagation of partner constraints.
-/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.CapAngularTangency

variable {d : ℕ} (S : Seed d)
open LocalAngularDynamics TorusLiouvilleDynamics

/-- Outside the strict disk directions every original coordinate has modulus one,
including the independently variable frozen coordinates. The proof now lives in
`CapIndependence`, so that the stratified cap description does not import the
flow modules; this is the same statement under its original name. -/
theorem norm_eq_one_of_not_strict {p : S.Point} (hp : p ∈ coordinateCap S)
    (j : Fin d) (hj : j ∉ p.strictCapIndices) : ‖p.a j‖ = 1 :=
  ClusterSkeleton.norm_eq_one_of_not_strict S hp j hj

/-- The independent locus selected by the cap contains its actual point. -/
theorem mem_strict_locus {p : S.Point} (hp : p ∈ coordinateCap S) :
    p ∈ candidateChartLocus S p.strictCapIndices := by
  intro j hj hz
  have h := norm_eq_one_of_not_strict S hp j hj
  simp [hz] at h

/-- The partner vanishes by the cap equation; no division by the original
coordinate occurs, so zero and nonzero strict-interior coordinates are included. -/
theorem normalizedPartner_eq_zero_of_interior {p : S.Point}
    (hp : p ∈ coordinateCap S) (i : S.Mutable) (hi : ‖p.a i‖ < 1) :
    normalizedPartner p i = 0 := by
  simp [normalizedPartner, coordinateCap_b_eq_zero hp i hi]

/-- Strict-interior independence makes the normalized node equation valid,
even on simultaneous zero strata. -/
theorem exchangeCharacter_eq_neg_one_of_interior {p : S.Point}
    (hp : p ∈ coordinateCap S) (i : S.Mutable) (hi : ‖p.a i‖ < 1) :
    exchangeCharacter p i = -1 := by
  have he := normalized_node_equation (coordinateCap_strictCapIndices_independent hp)
    (mem_strict_locus S hp) i ((p.mem_strictCapIndices i).mpr ⟨i.property, hi⟩)
  rw [normalizedPartner_eq_zero_of_interior S hp i hi, mul_zero] at he
  exact eq_neg_of_add_eq_zero_right he.symm

theorem angular_eq_zero_of_interior (δ : ℝ) {p : S.Point}
    (hp : p ∈ coordinateCap S) (i : S.Mutable) (hi : ‖p.a i‖ < 1) :
    TorusCorrection.angular S δ p i = 0 := by
  simp [TorusCorrection.angular, exchangeCharacter_eq_neg_one_of_interior S hp i hi,
    PrimitiveCutoffs.vartheta]

/-- A unit coordinate is outside the zero mask and its genuine log norm is zero. -/
theorem maskedLogs_eq_zero_of_unit (p : S.Point) (i : Fin d) (hi : ‖p.a i‖ = 1) :
    maskedLogs S p.zeroSet p i = 0 := by
  have hn : i ∉ p.zeroSet := by
    intro hz
    have ha := ((p.mem_zeroSet i).mp hz).2
    simp [ha] at hi
  simp [maskedLogs, hn, hi]

/-- Both the cutoff and its actual derivative vanish at log radius zero. -/
theorem radial_and_deriv_zero {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ) :
    PrimitiveCutoffs.radial ε κ 0 = 0 ∧ deriv (PrimitiveCutoffs.radial ε κ) 0 = 0 := by
  refine ⟨PrimitiveCutoffs.radial_eq_zero hκ (by linarith), ?_⟩
  rw [PrimitiveCutoffs.radial_deriv hκ]
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (PrimitiveCutoffs.radial_length_pos hκ).le

/-- The full derivative formula retains the derivatives of dominance and rho.
Each term vanishes because it contains the radial cutoff or its derivative. -/
theorem amplitude_fderiv_zero_of_unit {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ)
    (p : S.Point) (i : Fin d) (hi : ‖p.a i‖ = 1) (u : Fin d → ℝ) :
    fderiv ℝ (amplitude S ε κ i) (maskedLogs S p.zeroSet p) u = 0 := by
  obtain ⟨hr, hd⟩ := radial_and_deriv_zero hε hκ
  rw [fderiv_amplitude_apply, maskedLogs_eq_zero_of_unit S p i hi, hr, hd]
  simp

/-- Every summand vanishes at every cap point, on all zero strata. -/
theorem angularRhs_eq_zero {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ)
    (δ : ℝ) {p : S.Point} (hp : p ∈ coordinateCap S) (j : Fin d) :
    angularRhs S ε κ δ p p j = 0 := by
  classical
  rw [AllStrataGrowth.angularRhs_center S ε κ δ p j]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_eq_zero]
  refine Or.inr ?_
  split_ifs with hs
  · by_cases hi : ‖p.a i‖ < 1
    · rw [angular_eq_zero_of_interior S δ hp i hi, zero_mul]
    · have hu : ‖p.a i‖ = 1 :=
        le_antisymm (coordinateCap_norm_a_le hp i) (le_of_not_gt hi)
      rw [amplitude_fderiv_zero_of_unit S hε hκ p i hu, mul_zero]
  · rfl

/-- The inverse of the full matrix sends the zero angular right-hand side to zero. -/
theorem nu_eq_zero {ε κ : ℝ} (hε : 0 < ε) (hκ : 2 * ε < κ)
    (δ : ℝ) {p : S.Point} (hp : p ∈ coordinateCap S) :
    nu S ε κ δ p p = 0 := by
  have he : angularRhs S ε κ δ p p = 0 :=
    funext (angularRhs_eq_zero S hε hκ δ hp)
  simp [nu, he, Matrix.mulVec_zero, show (fun _ : Fin d => (0 : ℝ)) = 0 from rfl]

variable (hdet : S.Unimodular)

/-- The actual native logarithmic component is real at each selected nonzero
original coordinate; other original coordinates may vanish simultaneously. -/
theorem logarithmicComponents_im_eq_zero {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p : S.Point}
    (hp : p ∈ coordinateCap S) (j : Fin d) (hj : p.a j ≠ 0) :
    (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im = 0 := by
  rw [← nu_eq_logarithmicComponents S hdet hε hκ hδ p p
    (LocalPrimitive.mem_neighborhood S ε κ hδ p) j hj,
    nu_eq_zero S hε (by linarith : 2 * ε < κ) δ hp]
  rfl

/-- At a unit coordinate the real component also vanishes, by the accepted
all-strata radial equation for the same field. -/
theorem logarithmicComponents_eq_zero_of_unit {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p : S.Point}
    (hp : p ∈ coordinateCap S) (j : Fin d) (hj : ‖p.a j‖ = 1) :
    GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j = 0 := by
  have hn : p.a j ≠ 0 := by intro h; simp [h] at hj
  have ha : GlobalLiouvilleField.A S p j = 0 := by
    simp [GlobalLiouvilleField.A, hj]
  apply Complex.ext
  · rw [← GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ p j hn,
      GlobalLiouvilleField.L_eq_A_of_nonneg S hdet hε hκ hδ p j hn (by rw [ha]), ha]
    rfl
  · exact logarithmicComponents_im_eq_zero S hdet hε hκ hδ hp j hn

/-- Pointwise native coordinate drift is zero at every unit coordinate of a cap
point. Mutable boundary coordinates need no hypothesis on their partners. -/
theorem coordinate_drift_eq_zero_of_unit {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p : S.Point}
    (hp : p ∈ coordinateCap S) (j : Fin d) (hj : ‖p.a j‖ = 1) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential j p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 := by
  have hn : p.a j ≠ 0 := by intro h; simp [h] at hj
  have he := logarithmicComponents_eq_zero_of_unit S hdet hε hκ hδ hp j hj
  change _ / p.a j = 0 at he
  exact (div_eq_zero_iff.mp he).resolve_right hn

/-- Native within-time derivative on any genuine same-field curve. Only its
value at the selected time lies in the cap; no whole-curve chart is required. -/
theorem coordinate_hasDerivWithinAt_zero {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {t : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (ht : t ∈ J) (hp : γ t ∈ coordinateCap S) (j : Fin d) (hj : ‖(γ t).a j‖ = 1) :
    HasDerivWithinAt (fun u => (γ u).a j) 0 J t := by
  have hd := ZeroStratumInvariance.coordinate_hasDerivWithinAt S hdet hδ hγ ht j
  rwa [coordinate_drift_eq_zero_of_unit S hdet hε hκ hδ hp j hj] at hd

end ClusterSkeleton.CapAngularTangency
