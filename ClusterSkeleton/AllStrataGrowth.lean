import ClusterSkeleton.LocalAngularDynamics
import ClusterSkeleton.SeedAlgebra
import ClusterSkeleton.NativeRadialOrbit

/-! Uniform pointwise growth of the actual native Liouville field on every
zero stratum. The mask is fixed when differentiating along a curve. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.AllStrataGrowth

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
open LocalAngularDynamics TorusLiouvilleDynamics

/-- The size used in the estimates; no regularity across strata is asserted. -/
def R (p : S.Point) : ℝ := ∑ j : Fin d, |maskedLogs S p.zeroSet p j|

theorem R_nonneg (p : S.Point) : 0 ≤ R S p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem R_eq_sum (p : S.Point) :
    R S p = ∑ j ∈ p.zeroSetᶜ, |GlobalLiouvilleField.A S p j| := by
  classical
  have he : p.zeroSetᶜ = Finset.univ.filter (fun j => j ∉ p.zeroSet) := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, Finset.sum_filter]
  unfold R
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ p.zeroSet <;> simp [maskedLogs, hj, GlobalLiouvilleField.A]

theorem coordinate_ne_zero_of_mem_compl (p : S.Point) (j : Fin d)
    (hj : j ∈ p.zeroSetᶜ) : p.a j ≠ 0 := by
  by_cases hm : j ∈ S.mutable
  · exact fun hz => (Finset.mem_compl.mp hj) ((p.mem_zeroSet j).mpr ⟨hm, hz⟩)
  · exact p.frozen_ne_zero j hm

/-- Every frozen variable is included in the estimated complement. -/
theorem frozen_mem_compl (p : S.Point) (j : Fin d) (hj : j ∉ S.mutable) :
    j ∈ p.zeroSetᶜ := by
  exact Finset.mem_compl.mpr fun h => hj ((p.mem_zeroSet j).mp h).1

/-- The accepted radial defect estimate extends the homogeneous radial bound
to every selected nonzero coordinate, regardless of other zeros. -/
theorem radial_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : S.Point,
      (∑ j ∈ p.zeroSetᶜ,
        |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re|) ≤
          C * R S p := by
  classical
  obtain ⟨C, hC, hb⟩ := NativeRadialOrbit.uniform_radial_error_bound S hdet hε hκ hδ
  refine ⟨1+C, by positivity, fun p => ?_⟩
  rw [R_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hn := coordinate_ne_zero_of_mem_compl S p j hj
  rw [← GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ p j hn]
  have he := (hb p j hn).trans (mul_le_mul_of_nonneg_left
    (PrimitiveCutoffs.radial_abs_le hε (by linarith : 2*ε<κ) _) hC)
  calc
    _ = |(GlobalLiouvilleField.L S hdet ε κ hδ p j - GlobalLiouvilleField.A S p j) +
        GlobalLiouvilleField.A S p j| := by congr 1; ring
    _ ≤ |GlobalLiouvilleField.L S hdet ε κ hδ p j - GlobalLiouvilleField.A S p j| +
        |GlobalLiouvilleField.A S p j| := abs_add_le _ _
    _ ≤ C * |GlobalLiouvilleField.A S p j| + |GlobalLiouvilleField.A S p j| :=
      add_le_add he le_rfl
    _ = _ := by ring

/-- A local complex logarithm of one nonzero coordinate has its genuine
within-time derivative. The center is the current point, not one chart for the curve. -/
theorem normalizedLog_hasDerivWithinAt (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {t : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (ht : t ∈ J) (j : Fin d) (hj : (γ t).a j ≠ 0) :
    HasDerivWithinAt (fun u => Complex.log ((γ u).a j / (γ t).a j))
      (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j) J t := by
  have hd := (ZeroStratumInvariance.coordinate_hasDerivWithinAt S hdet hδ hγ ht j).div_const
    ((γ t).a j)
  have hs : (γ t).a j / (γ t).a j ∈ Complex.slitPlane := by
    simpa [div_self hj] using Complex.one_mem_slitPlane
  simpa only [div_self hj, div_one, GlobalLiouvilleField.logarithmicComponents] using
    hd.clog_real hs

/-- Singular summands vanish at the actual center, without restricting the zero set. -/
theorem angularRhs_center (ε κ δ : ℝ) (p : S.Point) (j : Fin d) :
    angularRhs S ε κ δ p p j =
      ∑ i : S.Mutable, (S.D (i : Fin d) : ℝ) *
        (if i ∈ RegularCorrection.surviving S p.zeroSet then
          TorusCorrection.angular S δ p i *
            fderiv ℝ (amplitude S ε κ i) (maskedLogs S p.zeroSet p) (Pi.single j 1)
        else 0) := by
  classical
  unfold angularRhs
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  by_cases hi : (i : Fin d) ∈ p.zeroSet
  · have ha : p.a i = 0 := ((p.mem_zeroSet i).mp hi).2
    have hs : i ∉ RegularCorrection.surviving S p.zeroSet :=
      fun h => ((RegularCorrection.mem_surviving S p.zeroSet i).mp h).1 hi
    simp [hi, hs, PrimitiveLocalization.nodeLog, ha]
  · simp only [hi, ite_false]

include hdet in
/-- Multiplication by the full weighted form matrix undoes the full inverse in
`nu`. The minus sign is the one carried by `nu`'s definition, i.e. by the
angular equation `∑_k K_{jk} θ̇_k = -∂_{u_j} H`. -/
theorem full_matrix_nu_equation (ε κ δ : ℝ) (p q : S.Point) (j : Fin d) :
    (∑ k : Fin d, (S.K j k : ℝ) * nu S ε κ δ p q k) =
      -angularRhs S ε κ δ p q j := by
  have he : (SeedAlgebra.Kreal S).mulVec (nu S ε κ δ p q) =
      fun i => -angularRhs S ε κ δ p q i := by
    change (SeedAlgebra.Kreal S).mulVec
      ((SeedAlgebra.Kreal S)⁻¹.mulVec (fun i => -angularRhs S ε κ δ p q i)) = _
    rw [Matrix.mulVec_mulVec, SeedAlgebra.Kreal_mul_inv S hdet, Matrix.one_mulVec]
  exact (SeedAlgebra.Kreal_mulVec_apply S _ j).symm.trans (congrFun he j)

include hdet in
/-- The row (character) form of the `nu` equation: `d_j · c_j(θ̇) = ∂_{u_j} H`,
i.e. the weight appears in the angular equation, exactly as in
`TorusLiouvilleDynamics.angular_equation_row`. -/
theorem row_nu_equation (ε κ δ : ℝ) (p q : S.Point) (j : Fin d) :
    (S.D j : ℝ) * (∑ k : Fin d, (S.B j k : ℝ) * nu S ε κ δ p q k) =
      angularRhs S ε κ δ p q j := by
  have h := full_matrix_nu_equation S hdet ε κ δ p q j
  rw [SeedAlgebra.sum_K_row S _ j] at h
  linarith

/-- A uniform bound for every radial Hamiltonian derivative at each center. -/
theorem angularRhs_center_bound {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : S.Point) (j : Fin d),
      |angularRhs S ε κ δ p p j| ≤ C * (1 + R S p) := by
  obtain ⟨K, hK, hKb⟩ := amplitude_partial_bound S hε hκ
  obtain ⟨V, hV, hVb⟩ := PrimitiveCutoffs.vartheta_iteratedDeriv_bound hδ 0
  simp only [iteratedDeriv_zero] at hVb
  have hD (i : S.Mutable) : (0 : ℝ) ≤ (S.D (i : Fin d) : ℝ) :=
    le_of_lt (by exact_mod_cast S.D_pos (i : Fin d))
  let C : ℝ := ∑ i : S.Mutable, (S.D (i : Fin d) : ℝ) * (V * K)
  have hC : 0 ≤ C :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hD i) (mul_nonneg hV hK)
  refine ⟨C, hC, fun p j => ?_⟩
  have hU : 0 ≤ 1 + R S p := by have := R_nonneg S p; positivity
  rw [angularRhs_center S ε κ δ p j]
  calc
    _ ≤ ∑ i : S.Mutable, |(S.D (i : Fin d) : ℝ) *
        (if i ∈ RegularCorrection.surviving S p.zeroSet then
          TorusCorrection.angular S δ p i *
            fderiv ℝ (amplitude S ε κ i) (maskedLogs S p.zeroSet p) (Pi.single j 1)
        else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : S.Mutable, (S.D (i : Fin d) : ℝ) * ((V * K) * (1 + R S p)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hD i)]
      refine mul_le_mul_of_nonneg_left ?_ (hD i)
      split_ifs with hs
      · rw [abs_mul, mul_assoc]
        exact mul_le_mul (hVb _) (hKb _ i j) (abs_nonneg _) hV
      · simp only [abs_zero]
        exact mul_nonneg (mul_nonneg hV hK) hU
    _ = C * (1 + R S p) := by simp only [C, Finset.sum_mul, mul_assoc]

include hdet in
/-- All entries of the center angular vector have uniform linear growth. -/
theorem nu_center_growth {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε < κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : S.Point,
      (∑ j : Fin d, |nu S ε κ δ p p j|) ≤ C * (1 + R S p) := by
  obtain ⟨K, hK, hKb⟩ := angularRhs_center_bound S hε hκ hδ
  obtain ⟨N, hN, hNb⟩ := full_matrix_inverse_bound S hdet
  refine ⟨N * (∑ _j : Fin d, K), by positivity, fun p => ?_⟩
  calc
    _ ≤ N * ∑ j : Fin d, |-angularRhs S ε κ δ p p j| :=
      hNb _ _ (fun j => full_matrix_nu_equation S hdet ε κ δ p p j)
    _ ≤ N * ∑ _j : Fin d, K * (1 + R S p) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ => by rw [abs_neg]; exact hKb p j) hN
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The coefficient estimate is purely algebraic and never divides by a partner. -/
theorem partner_coefficient_norm_le (κ ν : ℝ) :
    ‖(1 : ℂ) + (κ : ℂ) - Complex.I * (ν : ℂ)‖ ≤ 1 + |κ| + |ν| := by
  calc
    _ ≤ ‖(1 : ℂ) + (κ : ℂ)‖ + ‖Complex.I * (ν : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ)‖ + ‖(κ : ℂ)‖) + ‖Complex.I * (ν : ℂ)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- A uniform relative norm bound on native normalized-partner drift at every
zero original coordinate; zero partners are included. -/
theorem partner_drift_growth {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : S.Point) (i : S.Mutable), p.a i = 0 →
      ‖BoundaryTangency.drift S hdet ε κ hδ (fun q => normalizedPartner q i) p‖ ≤
        C * (1 + R S p) * ‖normalizedPartner p i‖ := by
  obtain ⟨N, hN, hNb⟩ := nu_center_growth S hdet hε (by linarith : 2*ε<κ) hδ
  refine ⟨1 + |κ| + N, by positivity, fun p i ha => ?_⟩
  have hi : (i : Fin d) ∈ p.zeroSet := (p.mem_zeroSet i).mpr ⟨i.property, ha⟩
  rw [partner_drift_zero S hdet hε hκ hδ p p
    (LocalPrimitive.mem_neighborhood S ε κ hδ p) i hi ha, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hν : |nu S ε κ δ p p i| ≤ N * (1 + R S p) :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (nu S ε κ δ p p j))
      (Finset.mem_univ i.val)).trans (hNb p)
  calc
    _ ≤ 1 + |κ| + |nu S ε κ δ p p i| := partner_coefficient_norm_le κ _
    _ ≤ (1 + |κ| + N) * (1 + R S p) := by
      have hR := R_nonneg S p
      nlinarith [mul_nonneg (by positivity : 0 ≤ 1 + |κ|) hR]


/-- At a zero index the literal node logarithm is log(1), for every partner. -/
theorem nodeLog_center_zero (p : S.Point) (i : S.Mutable)
    (hi : (i : Fin d) ∈ p.zeroSet) : PrimitiveLocalization.nodeLog p i = 0 := by
  simp [PrimitiveLocalization.nodeLog, ((p.mem_zeroSet i).mp hi).2]

theorem complex_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : S.Point,
      (∑ j ∈ p.zeroSetᶜ,
        (|(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re| +
         |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im|)) ≤
          C * (1 + R S p) := by
  classical
  obtain ⟨A, hA, ha⟩ := radial_growth S hdet hε hκ hδ
  obtain ⟨N, hN, hn⟩ := nu_center_growth S hdet hε (by linarith : 2*ε<κ) hδ
  refine ⟨A+N, add_nonneg hA hN, fun p => ?_⟩
  have him : (∑ j ∈ p.zeroSetᶜ,
      |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im|) ≤
        N * (1 + R S p) := by
    calc
      _ = ∑ j ∈ p.zeroSetᶜ, |nu S ε κ δ p p j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [nu_eq_logarithmicComponents S hdet hε hκ hδ p p
          (LocalPrimitive.mem_neighborhood S ε κ hδ p) j
          (coordinate_ne_zero_of_mem_compl S p j hj)]
      _ ≤ ∑ j : Fin d, |nu S ε κ δ p p j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := hn p
  rw [Finset.sum_add_distrib]
  have hr := ha p
  nlinarith

/-- One positive constant, independent of the point, stratum, index and partners,
controls all four actual native quantities. -/
theorem uniform_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : S.Point,
      (∑ j ∈ p.zeroSetᶜ,
        |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re|) ≤ C * R S p ∧
      (∑ j : Fin d, |nu S ε κ δ p p j|) ≤ C * (1 + R S p) ∧
      (∑ j ∈ p.zeroSetᶜ,
        (|(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re| +
         |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im|)) ≤
          C * (1 + R S p) ∧
      ∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet →
        ‖BoundaryTangency.drift S hdet ε κ hδ (fun q => normalizedPartner q i) p‖ ≤
          C * (1 + R S p) * ‖normalizedPartner p i‖ := by
  obtain ⟨A, hA, ha⟩ := radial_growth S hdet hε hκ hδ
  obtain ⟨N, hN, hn⟩ := nu_center_growth S hdet hε (by linarith : 2*ε<κ) hδ
  obtain ⟨G, hG, hg⟩ := complex_growth S hdet hε hκ hδ
  obtain ⟨P, hP, hp⟩ := partner_drift_growth S hdet hε hκ hδ
  let C := 1 + A + N + G + P
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hNC : N ≤ C := by dsimp [C]; linarith
  have hGC : G ≤ C := by dsimp [C]; linarith
  have hPC : P ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, fun p => ?_⟩
  have hR := R_nonneg S p
  have h1R : 0 ≤ 1 + R S p := by positivity
  refine ⟨(ha p).trans (mul_le_mul_of_nonneg_right hAC hR),
    (hn p).trans (mul_le_mul_of_nonneg_right hNC h1R),
    (hg p).trans (mul_le_mul_of_nonneg_right hGC h1R), fun i hi => ?_⟩
  exact (hp p i ((p.mem_zeroSet i).mp hi).2).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPC h1R) (norm_nonneg _))

/-- Differentiate the fixed initial mask, using the accepted zero-stratum
invariance and the native scalar chain rule. -/
theorem fixed_mask_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {t₀ t : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) (ht₀ : t₀ ∈ J) (ht : t ∈ J)
    (j : Fin d) (hj : j ∈ (γ t₀).zeroSetᶜ) :
    HasDerivWithinAt (fun u => maskedLogs S (γ t₀).zeroSet (γ u) j)
      (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j).re J t := by
  letI := SmoothAtlas.charts S hdet
  have hz := ZeroStratumInvariance.zeroSet_eq S hdet hε hκ hδ hγ hJ ht₀ ht
  have hn := coordinate_ne_zero_of_mem_compl S (γ t) j (hz ▸ hj)
  have hd := NormalizedPartnerNormDrift.hasDerivWithinAt_scalar_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht
    ((GlobalLiouvilleField.contMDiffAt_A S hdet (γ t) j hn).mdifferentiableAt (by simp))
  change HasDerivWithinAt (fun u => GlobalLiouvilleField.A S (γ u) j)
    (GlobalLiouvilleField.L S hdet ε κ hδ (γ t) j) J t at hd
  rw [GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ (γ t) j hn] at hd
  simpa only [maskedLogs, Finset.mem_compl.mp hj, ite_false, GlobalLiouvilleField.A] using hd

/-- Native complex partner differentiation needs only the current center. -/
theorem partner_center_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {t : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (ht : t ∈ J) (i : S.Mutable) (hi : (i : Fin d) ∈ (γ t).zeroSet) :
    HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
      (BoundaryTangency.drift S hdet ε κ hδ (fun q => normalizedPartner q i) (γ t)) J t := by
  rw [partner_drift_zero S hdet hε hκ hδ (γ t) (γ t)
    (LocalPrimitive.mem_neighborhood S ε κ hδ (γ t)) i hi
    (((γ t).mem_zeroSet i).mp hi).2]
  exact partner_hasDerivWithinAt_zero S hdet hε hκ hδ (γ t) i hi hγ ht
    (LocalPrimitive.mem_neighborhood S ε κ hδ (γ t)) (((γ t).mem_zeroSet i).mp hi).2

/-- Pointwise growth along any genuine native integral curve on a preconnected
time set. All sums use the fixed initial zero set; derivatives are honest within
derivatives and require no chart containing the whole curve. -/
theorem integralCurve_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
      (letI := SmoothAtlas.charts S hdet;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
          (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
      IsPreconnected J → t₀ ∈ J → ∀ t ∈ J,
      let I := (γ t₀).zeroSet
      let r := ∑ j : Fin d, |maskedLogs S I (γ t) j|
      (γ t).zeroSet = I ∧
      (∀ j ∈ Iᶜ,
        HasDerivWithinAt (fun u => maskedLogs S I (γ u) j)
          (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j).re J t ∧
        HasDerivWithinAt (fun u => Complex.log ((γ u).a j / (γ t).a j))
          (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j) J t) ∧
      (∑ j ∈ Iᶜ, |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j).re|) ≤ C*r ∧
      (∑ j : Fin d, |nu S ε κ δ (γ t) (γ t) j|) ≤ C*(1+r) ∧
      (∑ j ∈ Iᶜ, (|(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j).re| +
        |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ t) j).im|)) ≤ C*(1+r) ∧
      ∀ i : S.Mutable, (i : Fin d) ∈ I →
        HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
          (BoundaryTangency.drift S hdet ε κ hδ (fun q => normalizedPartner q i) (γ t)) J t ∧
        ‖BoundaryTangency.drift S hdet ε κ hδ (fun q => normalizedPartner q i) (γ t)‖ ≤
          C*(1+r)*‖normalizedPartner (γ t) i‖ := by
  obtain ⟨C, hC, hb⟩ := uniform_growth S hdet hε hκ hδ
  refine ⟨C, hC, fun γ J t₀ hγ hJ ht₀ t ht => ?_⟩
  dsimp only
  have hz := ZeroStratumInvariance.zeroSet_eq S hdet hε hκ hδ hγ hJ ht ht₀
  have hR : R S (γ t) = ∑ j : Fin d, |maskedLogs S (γ t₀).zeroSet (γ t) j| := by
    unfold R
    rw [hz]
  obtain ⟨hr, hn, hg, hp⟩ := hb (γ t)
  rw [hR, hz] at hr hg
  rw [hR] at hn hp
  refine ⟨hz, ?_, hr, hn, hg, ?_⟩
  · intro j hj
    exact ⟨fixed_mask_hasDerivWithinAt S hdet hε hκ hδ hγ hJ ht₀ ht j hj,
      normalizedLog_hasDerivWithinAt S hdet ε κ hδ hγ ht j
        (coordinate_ne_zero_of_mem_compl S (γ t) j (hz.symm ▸ hj))⟩
  · intro i hi
    have hit : (i : Fin d) ∈ (γ t).zeroSet := hz.symm ▸ hi
    exact ⟨partner_center_hasDerivWithinAt S hdet hε hκ hδ hγ ht i hit, hp i hit⟩

end ClusterSkeleton.AllStrataGrowth
