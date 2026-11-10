import ClusterSkeleton.CapAngularTangency
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.ODE.Gronwall

/-! Strict-interior partner propagation from one initial cap point, for the
actual global native field. The coordinate cap is not assumed along the curve. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.InteriorPartnerPropagation

variable {d : ℕ} (S : Seed d)

/-- Independence at the single initial cap point gives every full-row neighbor,
including every frozen neighbor, unit norm. -/
theorem initial_neighbor_unit {p : S.Point} (hp : p ∈ coordinateCap S)
    (i : S.Mutable) (hi : ‖p.a i‖ < 1) (j : Fin d) (hij : S.B i j ≠ 0) :
    ‖p.a j‖ = 1 := by
  apply CapAngularTangency.norm_eq_one_of_not_strict S hp j
  intro hj
  exact hij ((S.E_eq_zero_iff (i : Fin d) j).mp
    ((coordinateCap_strictCapIndices_independent hp).2 i
      ((p.mem_strictCapIndices i).mpr ⟨i.property, hi⟩) j hj))

variable (hdet : S.Unimodular)

/-- The accepted native zero-log law propagates a unit coordinate; no cap
membership at later times is a premise. -/
theorem unit_norm_forward {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (j : Fin d) (hj : ‖(γ t₀).a j‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(γ (t₀+t)).a j‖ = 1 := by
  have hn : (γ t₀).a j ≠ 0 := by intro hz; simp [hz] at hj
  have hp := NativeRadialOrbit.coordinate_ne_zero S hdet hε hκ hδ hη hγ j hn
    (show t₀ - η < t₀ + t by linarith)
  have hz := NativeRadialOrbit.zero_log_law S hdet hε hκ hδ hη hγ j hn
    (by simp [GlobalLiouvilleField.A, hj]) ht
  have he := congrArg Real.exp hz
  simpa only [GlobalLiouvilleField.A, Real.exp_log (norm_pos_iff.mpr hp), Real.exp_zero]
    using he

/-- Every neighbor premise of the character equation follows from one initial
cap membership and the genuine native radial laws. -/
theorem neighbors_unit_forward {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable) (hi : ‖(γ t₀).a i‖ < 1)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin d) (hij : S.B i j ≠ 0) :
    ‖(γ (t₀+t)).a j‖ = 1 :=
  unit_norm_forward S hdet hε hκ hδ hη hγ j (initial_neighbor_unit S hp i hi j hij) ht

/-- Only the row support is needed to make the literal denominator nonzero. -/
theorem negativeMonomial_ne_zero (p : S.Point) (i : Fin d)
    (hn : ∀ j, S.B i j ≠ 0 → p.a j ≠ 0) : S.negativeMonomial p.a i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases h : S.B i j = 0
  · simp [show S.E j i = 0 from h]
  · exact pow_ne_zero _ (hn j h)

/-- The actual exchange equation recovers the actual partner; unrelated
original coordinates may vanish. -/
theorem partners_zero_of_character (p : S.Point) (i : S.Mutable)
    (hi : p.a i ≠ 0) (hn : ∀ j, S.B i j ≠ 0 → p.a j ≠ 0)
    (hq : exchangeCharacter p i = -1) :
    normalizedPartner p i = 0 ∧ p.b i = 0 := by
  have hQ := negativeMonomial_ne_zero S p i hn
  have hP : S.positiveMonomial p.a i = -S.negativeMonomial p.a i := by
    have h := (div_eq_iff hQ).mp hq
    simpa only [neg_one_mul] using h
  have hb : p.b i = 0 := by
    have he := p.exchange i
    rw [hP, neg_add_cancel] at he
    exact (mul_eq_zero.mp he).resolve_left hi
  exact ⟨by simp [normalizedPartner, hb], hb⟩

end ClusterSkeleton.InteriorPartnerPropagation

namespace ClusterSkeleton.InteriorPartnerPropagation

variable {d : ℕ} (S : Seed d)
open TorusLiouvilleDynamics LocalAngularDynamics

/-- Laurent factors with exponent zero are constant, even at zero coordinates. -/
theorem hasFDerivAt_character_row (x : Fin d → ℂ) (i : Fin d)
    (hx : ∀ j, S.B i j ≠ 0 → x j ≠ 0) :
    HasFDerivAt (fun y : Fin d → ℂ => ∏ j, y j ^ S.B i j)
      ((∏ j, x j ^ S.B i j) •
        ∑ j : Fin d, (S.B i j : ℂ) • ((x j)⁻¹ •
          (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))) x := by
  apply NodeTwoForm.hasFDerivAt_product_log (E := Fin d → ℂ) Finset.univ
  intro j _
  by_cases hj : S.B i j = 0
  · convert! (hasFDerivAt_const (𝕜 := ℂ) (1 : ℂ) x) using 1
    · funext y
      simp [show S.E j i = 0 from hj]
    · ext y
      simp [show S.E j i = 0 from hj, smul_eq_mul]
  · refine NodeTwoForm.hasFDerivAt_zpow_log (E := Fin d → ℂ)
      (f := fun y => y j) (l := (x j)⁻¹ • (ContinuousLinearMap.proj j)) ?_
      (hx j hj) (S.B i j)
    convert! (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt
      (x := x) using 1
    simp [smul_smul, hx j hj]

variable (hdet : S.Unimodular)

/-- Only the full-row support needs to be nonzero for native differentiability. -/
theorem mdifferentiableAt_character_row (p : S.Point) (i : Fin d)
    (hp : ∀ j, S.B i j ≠ 0 → p.a j ≠ 0) :
    letI := SmoothAtlas.charts S hdet
    MDifferentiableAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ)
      (fun q : S.Point => exchangeCharacter q i) p := by
  letI := SmoothAtlas.charts S hdet
  have hc := ((TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))
    p).mdifferentiableAt (by simp)
  have h := ((hasFDerivAt_character_row S p.a i hp).restrictScalars ℝ).hasMFDerivAt.comp p
    hc.hasMFDerivAt
  have he : (fun q : S.Point => exchangeCharacter q i) =
      (fun y : Fin d → ℂ => ∏ j, y j ^ S.B i j) ∘ (fun q : S.Point => q.a) := by
    funext q
    exact exchangeCharacter_eq_zpow_product q i
  rw [he]
  exact h.mdifferentiableAt

theorem differential_character_row (p : S.Point) (i : Fin d)
    (hp : ∀ j, S.B i j ≠ 0 → p.a j ≠ 0)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun q => exchangeCharacter q i) p v =
      exchangeCharacter p i * ∑ j : Fin d, (S.B i j : ℂ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j) := by
  letI := SmoothAtlas.charts S hdet
  have hc := ((TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))
    p).mdifferentiableAt (by simp)
  have h := ((hasFDerivAt_character_row S p.a i hp).restrictScalars ℝ).hasMFDerivAt.comp p
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
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]

omit hdet in
theorem angularRhs_eq_self_of_unit_neighbors {ε κ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε < κ) (δ : ℝ)
    (p : S.Point) (i : S.Mutable) (hi : p.a i ≠ 0)
    (hrow : ∀ j, S.B i j ≠ 0 → ‖p.a j‖ = 1) :
    angularRhs S ε κ δ p p i = (S.D (i : Fin d) : ℝ) *
      (TorusCorrection.angular S δ p i *
        fderiv ℝ (amplitude S ε κ i) (Pi.single i (GlobalLiouvilleField.A S p i))
          (Pi.single i 1)) := by
  classical
  have hiZ : (i : Fin d) ∉ p.zeroSet := fun h => hi ((p.mem_zeroSet i).mp h).2
  have hs : i ∈ RegularCorrection.surviving S p.zeroSet := by
    apply (RegularCorrection.mem_surviving S p.zeroSet i).mpr
    refine ⟨hiZ, ?_⟩
    intro j hj
    by_contra hB
    have hu := hrow j hB
    simp [((p.mem_zeroSet j).mp hj).2] at hu
  have hdiag : S.B i i = 0 := S.B_diag_zero i
  have hf : fderiv ℝ (amplitude S ε κ i) (maskedLogs S p.zeroSet p) (Pi.single i 1) =
      fderiv ℝ (amplitude S ε κ i) (Pi.single i (GlobalLiouvilleField.A S p i))
        (Pi.single i 1) := by
    apply amplitude_fderiv_congr S ε κ i _ _ _
    · simp [maskedLogs, hiZ, GlobalLiouvilleField.A]
    · intro j hj
      have hji : j ≠ (i : Fin d) := by intro he; subst j; exact hj hdiag
      rw [CapAngularTangency.maskedLogs_eq_zero_of_unit S p j (hrow j hj)]
      simp [hji]
  rw [AllStrataGrowth.angularRhs_center S ε κ δ p i]
  rw [Finset.sum_eq_single i]
  · simp only [hs, ite_true, hf]
  · intro j _ hji
    by_cases hB : S.B j i = 0
    · have hjival : (j : Fin d) ≠ (i : Fin d) := fun he => hji (Subtype.ext he)
      rw [BoundaryTangency.amplitude_partial_nonadjacent S ε κ _ i j hjival hB]
      split_ifs <;> simp
    · have hB' : S.B i j ≠ 0 := by
        intro he
        apply hB
        exact (S.B_eq_zero_iff i j).mp he
      rw [CapAngularTangency.amplitude_fderiv_zero_of_unit S hε hκ p j (hrow j hB')]
      split_ifs <;> simp
  · simp

/-- Exact complex character equation when all full-row neighbors have unit modulus.
The selected coordinate can lie anywhere in the nonzero locus, including the collar. -/
theorem differential_character_of_unit_neighbors {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    (p : S.Point) (i : S.Mutable) (hi : p.a i ≠ 0)
    (hrow : ∀ j, S.B i j ≠ 0 → ‖p.a j‖ = 1) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun q => exchangeCharacter q i) p (GlobalLiouvilleField.Z S hdet ε κ hδ p) =
      Complex.I * exchangeCharacter p i *
        (fderiv ℝ (amplitude S ε κ i) (Pi.single i (GlobalLiouvilleField.A S p i))
          (Pi.single i 1) : ℂ) * (TorusCorrection.angular S δ p i : ℂ) := by
  have hn (j : Fin d) (hj : S.B i j ≠ 0) : p.a j ≠ 0 := by
    intro he
    have hu := hrow j hj
    simp [he] at hu
  have hr (j : Fin d) (hj : S.B i j ≠ 0) :
      (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re = 0 := by
    have ha : GlobalLiouvilleField.A S p j = 0 := by
      simp [GlobalLiouvilleField.A, hrow j hj]
    rw [← GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ p j (hn j hj),
      GlobalLiouvilleField.L_eq_A_of_nonneg S hdet hε hκ hδ p j (hn j hj) (by rw [ha]), ha]
  have hnu (j : Fin d) (hj : S.B i j ≠ 0) :
      GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j =
        Complex.I * (nu S ε κ δ p p j : ℂ) := by
    apply Complex.ext
    · simpa using hr j hj
    · simpa using (nu_eq_logarithmicComponents S hdet hε hκ hδ p p
        (LocalPrimitive.mem_neighborhood S ε κ hδ p) j (hn j hj)).symm
  have hrowsum : (∑ j : Fin d, (S.B i j : ℝ) * nu S ε κ δ p p j) =
      TorusCorrection.angular S δ p i *
        fderiv ℝ (amplitude S ε κ i) (Pi.single i (GlobalLiouvilleField.A S p i))
          (Pi.single i 1) := by
    have h := AllStrataGrowth.row_nu_equation S hdet ε κ δ p p i
    rw [angularRhs_eq_self_of_unit_neighbors S hε (by linarith) δ p i hi hrow] at h
    have hD : ((S.D (i : Fin d) : ℚ) : ℝ) ≠ 0 := by
      have := S.D_pos (i : Fin d)
      exact_mod_cast this.ne'
    exact mul_left_cancel₀ hD h
  have hsum : (∑ j : Fin d, (S.B i j : ℂ) *
      GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j) =
        Complex.I * ((TorusCorrection.angular S δ p i *
          fderiv ℝ (amplitude S ε κ i) (Pi.single i (GlobalLiouvilleField.A S p i))
            (Pi.single i 1) : ℝ) : ℂ) := by
    calc
      _ = ∑ j : Fin d, Complex.I * ((S.B i j : ℝ) * nu S ε κ δ p p j : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : S.B i j = 0
        · simp [show S.E j (i : Fin d) = 0 from hj]
        · rw [hnu j hj]
          push_cast
          ring
      _ = Complex.I * (∑ j : Fin d, (S.B i j : ℝ) * nu S ε κ δ p p j : ℝ) := by
        rw [Complex.ofReal_sum, Finset.mul_sum]
      _ = _ := by rw [hrowsum]
  rw [differential_character_row S hdet p i hn]
  change exchangeCharacter p i * (∑ j : Fin d, (S.B i j : ℂ) *
    GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j) = _
  rw [hsum]
  push_cast
  ring

end ClusterSkeleton.InteriorPartnerPropagation

namespace ClusterSkeleton.InteriorPartnerPropagation

/-- Jordan's inequality controls the principal inverse sine by its sine. -/
theorem abs_arcsin_sin_le (θ : ℝ) :
    |Real.arcsin (Real.sin θ)| ≤ (Real.pi / 2) * |Real.sin θ| := by
  have h := Real.mul_abs_le_abs_sin
    (abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin (Real.sin θ),
      Real.arcsin_le_pi_div_two (Real.sin θ)⟩)
  rw [Real.sin_arcsin (Real.neg_one_le_sin θ) (Real.sin_le_one θ)] at h
  calc
    |Real.arcsin (Real.sin θ)| =
        (Real.pi / 2) * ((2 / Real.pi) * |Real.arcsin (Real.sin θ)|) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi / 2) * |Real.sin θ| :=
      mul_le_mul_of_nonneg_left h Real.pi_div_two_pos.le

/-- This bound uses only the actual cutoff's range, and holds for every parameter. -/
theorem abs_vartheta_le_sin (δ θ : ℝ) :
    |PrimitiveCutoffs.vartheta δ θ| ≤ (Real.pi / 2) * |Real.sin θ| := by
  calc
    |PrimitiveCutoffs.vartheta δ θ| =
        |Real.arcsin (Real.sin θ)| * PrimitiveCutoffs.angularWindow δ θ := by
      rw [PrimitiveCutoffs.vartheta, abs_mul,
        abs_of_nonneg (PrimitiveCutoffs.angularWindow_nonneg δ θ)]
    _ ≤ |Real.arcsin (Real.sin θ)| * 1 :=
      mul_le_mul_of_nonneg_left (PrimitiveCutoffs.angularWindow_le_one δ θ) (abs_nonneg _)
    _ = |Real.arcsin (Real.sin θ)| := mul_one _
    _ ≤ (Real.pi / 2) * |Real.sin θ| := abs_arcsin_sin_le θ

/-- Global estimate for the actual complex angular vector field at its equilibrium `-1`.
No unit-norm or nonvanishing premise is needed: the polar sine identity includes zero. -/
theorem norm_mul_vartheta_arg_le (δ : ℝ) (z : ℂ) :
    ‖z‖ * |PrimitiveCutoffs.vartheta δ (Complex.arg (-z))| ≤
      (Real.pi / 2) * ‖z + 1‖ := by
  have hsin : ‖z‖ * |Real.sin (Complex.arg (-z))| = |z.im| := by
    simpa only [abs_mul, abs_norm, norm_neg, Complex.neg_im, abs_neg] using
      congrArg abs (Complex.norm_mul_sin_arg (-z))
  calc
    ‖z‖ * |PrimitiveCutoffs.vartheta δ (Complex.arg (-z))| ≤
        ‖z‖ * ((Real.pi / 2) * |Real.sin (Complex.arg (-z))|) :=
      mul_le_mul_of_nonneg_left (abs_vartheta_le_sin δ (Complex.arg (-z))) (norm_nonneg _)
    _ = (Real.pi / 2) * (‖z‖ * |Real.sin (Complex.arg (-z))|) := by ring
    _ = (Real.pi / 2) * |z.im| := by rw [hsin]
    _ ≤ (Real.pi / 2) * ‖z + 1‖ :=
      mul_le_mul_of_nonneg_left
        (by simpa using Complex.abs_im_le_norm (z + 1)) Real.pi_div_two_pos.le

/-- Scalar uniqueness on a closed finite segment, with the native derivative taken
within that segment. A bound on the coefficient is the only coefficient regularity used. -/
theorem angular_scalar_eq_neg_one_of_bounded
    {q c : ℝ → ℂ} {δ a b C : ℝ}
    (hq : ContinuousOn q (Icc a b))
    (hderiv : ∀ t ∈ Ico a b,
      HasDerivWithinAt q
        (Complex.I * q t * c t *
          (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)) (Icc a b) t)
    (hinit : q a = -1)
    (hc : ∀ t ∈ Ico a b, ‖c t‖ ≤ C) :
    ∀ t ∈ Icc a b, q t = -1 := by
  have hzero : ∀ t ∈ Icc a b, q t + 1 = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f' := fun t => Complex.I * q t * c t *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ))
      (K := C * (Real.pi / 2)) (hq.add continuousOn_const)
    · intro t ht
      exact ((hderiv t ht).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)).add_const 1
    · simp [hinit]
    · intro t ht
      calc
        ‖Complex.I * q t * c t *
            (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)‖ =
            ‖c t‖ * (‖q t‖ * |PrimitiveCutoffs.vartheta δ (Complex.arg (-q t))|) := by
          simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          ring
        _ ≤ ‖c t‖ * ((Real.pi / 2) * ‖q t + 1‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_vartheta_arg_le δ (q t)) (norm_nonneg _)
        _ ≤ C * ((Real.pi / 2) * ‖q t + 1‖) :=
          mul_le_mul_of_nonneg_right (hc t ht)
            (mul_nonneg Real.pi_div_two_pos.le (norm_nonneg _))
        _ = (C * (Real.pi / 2)) * ‖q t + 1‖ := by ring
  intro t ht
  exact eq_neg_of_add_eq_zero_left (hzero t ht)

/-- Continuous coefficients on a finite segment are bounded, giving the practical
scalar uniqueness interface. Both endpoints are included in the conclusion. -/
theorem angular_scalar_eq_neg_one
    {q c : ℝ → ℂ} {δ a b : ℝ}
    (hq : ContinuousOn q (Icc a b))
    (hc : ContinuousOn c (Icc a b))
    (hderiv : ∀ t ∈ Ico a b,
      HasDerivWithinAt q
        (Complex.I * q t * c t *
          (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)) (Icc a b) t)
    (hinit : q a = -1) :
    ∀ t ∈ Icc a b, q t = -1 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact angular_scalar_eq_neg_one_of_bounded hq hderiv hinit
    (fun t ht => hC t ⟨ht.1, ht.2.le⟩)

/-- A native `HasDerivAt` interface for coefficients already known continuous on the segment. -/
theorem angular_scalar_eq_neg_one_of_hasDerivAt
    {q c : ℝ → ℂ} {δ a b : ℝ}
    (hq : ContinuousOn q (Icc a b))
    (hc : ContinuousOn c (Icc a b))
    (hderiv : ∀ t ∈ Ico a b,
      HasDerivAt q
        (Complex.I * q t * c t *
          (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)) t)
    (hinit : q a = -1) :
    ∀ t ∈ Icc a b, q t = -1 :=
  angular_scalar_eq_neg_one hq hc
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hinit

end ClusterSkeleton.InteriorPartnerPropagation

namespace ClusterSkeleton.InteriorPartnerPropagation

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- A smooth one-variable evaluation of the actual amplitude derivative. -/
def characterCoefficient (ε κ : ℝ) (i : Fin d) (a : ℝ) : ℝ :=
  fderiv ℝ (TorusLiouvilleDynamics.amplitude S ε κ i) (Pi.single i a) (Pi.single i 1)

omit hdet in
theorem characterCoefficient_continuous (ε κ : ℝ) (i : Fin d) :
    Continuous (characterCoefficient S ε κ i) := by
  classical
  have hp : Continuous (fun a : Fin d → ℝ =>
      fderiv ℝ (TorusLiouvilleDynamics.amplitude S ε κ i) a (Pi.single i 1)) :=
    (((TorusLiouvilleDynamics.amplitude_smooth S ε κ i).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  apply hp.comp
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Pi.single_eq_same] using (continuous_id' : Continuous (fun a : ℝ => a))
  · simpa [Pi.single_apply, hj] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

/-- The character has its genuine native time derivative at every forward time,
including the initial endpoint. -/
theorem shifted_character_hasDerivAt {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => exchangeCharacter (γ (t₀+u)) i)
      (Complex.I * exchangeCharacter (γ (t₀+t)) i *
        (characterCoefficient S ε κ i (GlobalLiouvilleField.A S (γ (t₀+t)) i) : ℂ) *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter (γ (t₀+t)) i)) : ℂ)) t := by
  letI := SmoothAtlas.charts S hdet
  have htime : t₀ - η < t₀+t := by linarith
  have hn := NativeRadialOrbit.coordinate_ne_zero S hdet hε hκ hδ hη hγ i hi htime
  have hrow := neighbors_unit_forward S hdet hε hκ hδ hη hγ hp i hr ht
  have hnonzero (j : Fin d) (hj : S.B i j ≠ 0) : (γ (t₀+t)).a j ≠ 0 := by
    intro he
    have hu := hrow j hj
    simp [he] at hu
  have hd := LocalAngularDynamics.hasDerivWithinAt_complex_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ htime
    (mdifferentiableAt_character_row S hdet _ i hnonzero)
  have hdA := hd.hasDerivAt (isOpen_Ioi.mem_nhds htime)
  rw [differential_character_of_unit_neighbors S hdet hε hκ hδ _ i hn hrow] at hdA
  convert! hdA.scomp t ((hasDerivAt_id t).const_add t₀) using 1 <;>
    simp [characterCoefficient, TorusCorrection.angular]

/-- Finite-segment uniqueness for the derived character equation. The selected
coordinate stays nonzero by the accepted native zero-stratum theorem. -/
theorem character_eq_neg_one_forward {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1)
    {t : ℝ} (ht : 0 ≤ t) : exchangeCharacter (γ (t₀+t)) i = -1 := by
  let q : ℝ → ℂ := fun u => exchangeCharacter (γ (t₀+u)) i
  let c : ℝ → ℂ := fun u =>
    (characterCoefficient S ε κ i (GlobalLiouvilleField.A S (γ (t₀+u)) i) : ℂ)
  have hd (u : ℝ) (hu : 0 ≤ u) :=
    shifted_character_hasDerivAt S hdet hε hκ hδ hη hγ hp i hi hr hu
  have hq : ContinuousOn q (Icc 0 t) :=
    fun u hu => (hd u hu.1).continuousAt.continuousWithinAt
  have hc : ContinuousOn c (Icc 0 t) := by
    intro u hu
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((characterCoefficient_continuous S ε κ i).continuousAt.comp
        (NativeRadialOrbit.shifted_hasDerivAt_A S hdet hε hκ hδ hη hγ i hi hu.1).continuousAt)).continuousWithinAt
  exact angular_scalar_eq_neg_one_of_hasDerivAt hq hc (fun u hu => hd u hu.1)
    (by simpa [q] using CapAngularTangency.exchangeCharacter_eq_neg_one_of_interior S hp i hr)
    t ⟨ht, le_rfl⟩

/-- Strict-interior nonzero partner propagation, with every later neighbor
premise derived from the one initial cap membership. -/
theorem propagate {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
    (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    exchangeCharacter (γ (t₀+t)) i = -1 ∧
    normalizedPartner (γ (t₀+t)) i = 0 ∧ (γ (t₀+t)).b i = 0 := by
  have hq := character_eq_neg_one_forward S hdet hε hκ hδ hη hγ hp i hi hr ht
  refine ⟨hq, partners_zero_of_character S _ i
    (NativeRadialOrbit.coordinate_ne_zero S hdet hε hκ hδ hη hγ i hi (by linarith)) ?_ hq⟩
  intro j hj hz
  have hu := neighbors_unit_forward S hdet hε hκ hδ hη hγ hp i hr ht j hj
  simp [hz] at hu

end ClusterSkeleton.InteriorPartnerPropagation

namespace ClusterSkeleton

/-- The complete lane target. This proposition is separate from its proof. -/
def InteriorPartnerPropagationTarget
    {d : ℕ} (S : Seed d) (hdet : S.Unimodular) : Prop :=
  ∀ {ε κ δ t₀ η : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point},
    (letI := SmoothAtlas.charts S hdet;
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ)
        (Set.Ioi (t₀ - η))) →
    γ t₀ ∈ coordinateCap S →
    ∀ i : S.Mutable,
      (γ t₀).a i ≠ 0 →
      ‖(γ t₀).a i‖ < 1 →
      ∀ t ≥ 0,
        exchangeCharacter (γ (t₀+t)) i = -1 ∧
        normalizedPartner (γ (t₀+t)) i = 0 ∧
        (γ (t₀+t)).b i = 0

theorem interiorPartnerPropagationTarget {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    InteriorPartnerPropagationTarget S hdet := by
  intro ε κ δ t₀ η hε hκ hδ hη γ hγ hp i hi hr t ht
  exact InteriorPartnerPropagation.propagate S hdet hε hκ hδ hη hγ hp i hi hr ht

end ClusterSkeleton
