import ClusterSkeleton.NormalizedPartnerNormDrift

/-! Smooth angular coefficients and complex normalized-partner dynamics for the
actual global Liouville field, on every open node neighborhood. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.LocalAngularDynamics
open TorusLiouvilleDynamics

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Only the coordinates known nonzero on the node chart are logged. -/
def maskedLogs (I : Finset (Fin d)) (q : S.Point) (j : Fin d) : ℝ :=
  if j ∈ I then 0 else Real.log ‖q.a j‖

theorem maskedLogs_smooth (I : Finset (Fin d)) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Fin d → ℝ) ∞ (maskedLogs S I) q := by
  letI := SmoothAtlas.charts S hdet
  apply contMDiffAt_pi_space.mpr
  intro j
  by_cases hj : j ∈ I
  · simp only [maskedLogs, hj, ite_true]
    exact contMDiffAt_const
  · simp only [maskedLogs, hj, ite_false]
    exact GlobalLiouvilleField.contMDiffAt_A S hdet q j (hq j hj)

/-- A surviving amplitude uses only its own coordinate and its full row support.
This includes the derivatives of every dominance factor. -/
theorem amplitude_fderiv_congr (ε κ : ℝ) (i : Fin d) (a a' u : Fin d → ℝ)
    (hi : a i = a' i) (hr : ∀ k, S.B i k ≠ 0 → a k = a' k) :
    fderiv ℝ (amplitude S ε κ i) a u = fderiv ℝ (amplitude S ε κ i) a' u := by
  classical
  have hn (k : Fin d) (hk : k ∈ DominanceCutoff.mutableNeighbors S i) : a k = a' k :=
    hr k ((DominanceCutoff.mem_mutableNeighbors S i k).mp hk).2
  have hd : DominanceCutoff.dominance S ε i a = DominanceCutoff.dominance S ε i a' := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hi, hn k hk]
  have hD : fderiv ℝ (DominanceCutoff.dominance S ε i) a u =
      fderiv ℝ (DominanceCutoff.dominance S ε i) a' u := by
    rw [fderiv_dominance_apply, fderiv_dominance_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hi, hn k hk]
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    rw [hn l (Finset.mem_of_mem_erase hl)]
  have hrow : (∑ k : Fin d, (S.B i k : ℝ) * a k) =
      ∑ k : Fin d, (S.B i k : ℝ) * a' k := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : S.B i k = 0
    · simp [hk]
    · rw [hr k hk]
  rw [fderiv_amplitude_apply, fderiv_amplitude_apply, hi, hd, hD, hrow]

theorem amplitude_fderiv_mask (I : Finset (Fin d)) (ε κ : ℝ) (i : S.Mutable)
    (hi : i ∈ RegularCorrection.surviving S I) (q : S.Point) (u : Fin d → ℝ) :
    fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S q) u =
      fderiv ℝ (amplitude S ε κ i) (maskedLogs S I q) u := by
  obtain ⟨hiI, hrow⟩ := (RegularCorrection.mem_surviving S I i).mp hi
  apply amplitude_fderiv_congr S ε κ i _ _ u
  · simp [maskedLogs, hiI, TorusCorrection.A]
  · intro k hk
    have hkI : k ∉ I := fun h => hk (hrow k h)
    simp [maskedLogs, hkI, TorusCorrection.A]

/-- A genuine smooth derivative of a genuine smooth amplitude, evaluated at
the smooth masked logarithms; no coordinate division is involved. -/
theorem maskedPartial_smooth (I : Finset (Fin d)) (ε κ : ℝ) (i j : Fin d)
    (q : S.Point) (hq : q ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun r => fderiv ℝ (amplitude S ε κ i) (maskedLogs S I r) (Pi.single j 1)) q := by
  letI := SmoothAtlas.charts S hdet
  exact (((amplitude_smooth S ε κ i).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiff_const).comp_contMDiffAt (maskedLogs_smooth S hdet I q hq)

theorem survivingAngular_smooth (I : Finset (Fin d)) {δ : ℝ} (hδ : 0 < δ)
    (i : S.Mutable) (hi : i ∈ RegularCorrection.surviving S I)
    (q : S.Point) (hq : q ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun r => TorusCorrection.angular S δ r i) q := by
  letI := SmoothAtlas.charts S hdet
  exact (TorusCorrection.vartheta_arg_contDiffAt hδ
    (neg_ne_zero.mpr (RegularCorrection.character_nonzero S hi hq))).comp_contMDiffAt
      (f := fun r : S.Point => -exchangeCharacter r i)
      (RegularCorrection.contMDiffAt_character S hdet hi hq).neg

/-- The radial Hamiltonian derivative, with singular and adjacent terms removed
by their actual local germs and surviving terms evaluated on masked logs. -/
def angularRhs (ε κ δ : ℝ) (p q : S.Point) (j : Fin d) : ℝ :=
  ∑ i : S.Mutable,
    if (i : Fin d) ∈ p.zeroSet then
      (PrimitiveLocalization.nodeLog q i).im * (Pi.single j 1 : Fin d → ℝ) i
    else if i ∈ RegularCorrection.surviving S p.zeroSet then
      TorusCorrection.angular S δ q i *
        fderiv ℝ (amplitude S ε κ i) (maskedLogs S p.zeroSet q) (Pi.single j 1)
    else 0

/-- The inverse is of the FULL real matrix, including the frozen rows/columns. -/
def nu (ε κ δ : ℝ) (p q : S.Point) : Fin d → ℝ :=
  Matrix.mulVec ((fun i j => (S.B i j : ℝ)) : Matrix (Fin d) (Fin d) ℝ)⁻¹
    (angularRhs S ε κ δ p q)

theorem angularRhs_smooth (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (j : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun r => angularRhs S ε κ δ p r j) q := by
  letI := SmoothAtlas.charts S hdet
  unfold angularRhs
  apply ContMDiffAt.sum
  intro i _
  by_cases hi : (i : Fin d) ∈ p.zeroSet
  · simp only [hi, ite_true]
    exact (Complex.imCLM.contDiff.contDiffAt.contMDiffAt.comp q
      (BoundaryTangency.nodeLog_smooth S hdet p i hi q hq)).mul contMDiffAt_const
  · simp only [hi, ite_false]
    by_cases hs : i ∈ RegularCorrection.surviving S p.zeroSet
    · simp only [hs, ite_true]
      exact (survivingAngular_smooth S hdet p.zeroSet hδ i hs q hq.2.1).mul
        (maskedPartial_smooth S hdet p.zeroSet ε κ i j q hq.2.1)
    · simp only [hs, ite_false]
      exact contMDiffAt_const

theorem nu_smooth (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) (j : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun q => nu S ε κ δ p q j) (LocalPrimitive.neighborhood S ε κ δ p) := by
  letI := SmoothAtlas.charts S hdet
  intro q hq
  apply ContMDiffAt.contMDiffWithinAt
  unfold nu Matrix.mulVec dotProduct
  exact ContMDiffAt.sum fun k _ => contMDiffAt_const.mul
    (angularRhs_smooth S hdet ε κ hδ p q hq k)

include hdet in
theorem amplitude_partial_zeroIndex {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (j : Fin d) :
    fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S q) (Pi.single j 1) = (Pi.single j 1 : Fin d → ℝ) i := by
  classical
  letI := SmoothAtlas.charts S hdet
  have hg : (fun r : S.Point => amplitude S ε κ i (TorusCorrection.A S r)) =ᶠ[𝓝 q]
      (fun r => TorusCorrection.A S r i + κ) := by
    filter_upwards [(PrimitiveLocalization.isOpen_neighborhood ε κ δ p).mem_nhds hq.1,
      (isOpen_initialTorus S).mem_nhds ht] with r hr hrt
    obtain ⟨hd, hρ, _, hrad⟩ := PrimitiveLocalization.plateaus hε hκ hδ hr hrt i hi
    change PrimitiveCutoffs.radial ε κ (DominanceCutoff.logNorms S r i) *
      DominanceCutoff.dominance S ε i (DominanceCutoff.logNorms S r) *
        PrimitiveCutoffs.rho (PrimitiveLocalization.rowLog r i) =
      DominanceCutoff.logNorms S r i + κ
    rw [hd, hρ, hrad]
    simp
  have he : differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => amplitude S ε κ i (TorusCorrection.A S r)) q =
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => TorusCorrection.A S r i + κ) q := hg.mfderiv_eq
  have hAi := (contMDiffAt_pi_space.mp
    (TorusCorrection.contMDiffAt_A S hdet q ht) i.val).mdifferentiableAt (by simp)
  have hplus : differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => TorusCorrection.A S r i + κ) q =
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => TorusCorrection.A S r i) q := by
    change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      ((fun r => TorusCorrection.A S r i) + fun _ => κ) q = _
    erw [mfderiv_add hAi (mdifferentiableAt_const (c := κ)), mfderiv_const]
    exact add_zero _
  rw [← BoundaryTangency.differential_amplitude_radial S hdet ε κ q ht j i.val,
    he, hplus, differential_A S hdet q ht,
    logarithmic_radialTangent S hdet q ht j i.val]
  simp [Pi.single_apply, apply_ite]

theorem angularRhs_eq_radial {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (j : Fin d) :
    angularRhs S ε κ δ p q j =
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) q (radialTangent S hdet q ht j) := by
  classical
  rw [differential_H_radial S hdet ε κ hδ q ht j]
  rw [Finset.sum_subtype S.mutable (fun _ => Iff.rfl)]
  unfold angularRhs
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Fin d) ∈ p.zeroSet
  · simp only [hi, ite_true]
    rw [amplitude_partial_zeroIndex S hdet hε hκ hδ hq ht i hi j]
    congr 1
    symm
    simpa only [TorusCorrection.angular, PrimitiveLocalization.angle, Complex.log_im] using
      ((PrimitiveLocalization.plateaus hε hκ hδ hq.1 ht i hi).2.2.1.trans
        (PrimitiveLocalization.node_bridges hq.1 i hi).2.2.2.2.1)
  · simp only [hi, ite_false]
    by_cases hs : i ∈ RegularCorrection.surviving S p.zeroSet
    · simp only [hs, ite_true]
      rw [amplitude_fderiv_mask S p.zeroSet ε κ i hs q]
    · simp only [hs, ite_false]
      have hn : ∃ k ∈ p.zeroSet, S.B k i ≠ 0 := by
        have hr : ¬ ∀ k ∈ p.zeroSet, S.B i k = 0 :=
          fun hr => hs ((RegularCorrection.mem_surviving S p.zeroSet i).mpr ⟨hi, hr⟩)
        push Not at hr
        obtain ⟨k, hk, hki⟩ := hr
        exact ⟨k, hk, fun he => hki (by rw [S.skew i k, he, neg_zero])⟩
      rw [BoundaryTangency.amplitude_partial_adjacent S hdet hε hq ht j i hn, mul_zero]

/-- Inverting the actual full matrix identifies the smooth formula on the torus. -/
theorem nu_eq_torus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S) :
    nu S ε κ δ p q = fun j => (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ q j).im := by
  let R : Matrix (Fin d) (Fin d) ℝ := fun i j => (S.B i j : ℝ)
  have hd : R.det = 1 := by
    have h := (Int.castRingHom ℝ).map_det S.B
    change (S.B.det : ℝ) = R.det at h
    rw [hdet, Int.cast_one] at h
    exact h.symm
  have hu : IsUnit R.det := by rw [hd]; exact isUnit_one
  have he : R.mulVec (fun j => (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ q j).im) =
      angularRhs S ε κ δ p q := by
    funext j
    rw [GlobalLiouvilleField.logarithmicComponents_eq_torus S hdet hε hκ hδ q ht]
    exact (angular_equation S hdet ε κ hδ q ht j).trans
      (angularRhs_eq_radial S hdet hε hκ hδ p q hq ht j).symm
  change R⁻¹.mulVec (angularRhs S ε κ δ p q) = _
  rw [← he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R hu, Matrix.one_mulVec]

/-- Agreement at every nonzero coordinate, even when other coordinates vanish.
Density is used only for equality of continuous functions on an open set. -/
theorem nu_eq_logarithmicComponents {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (j : Fin d) (hj : q.a j ≠ 0) :
    nu S ε κ δ p q j = (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ q j).im := by
  letI := SmoothAtlas.charts S hdet
  let U := LocalPrimitive.neighborhood S ε κ δ p
  let V := U ∩ GlobalLiouvilleField.nonzeroLocus S j
  have hV : IsOpen V := (LocalPrimitive.isOpen_neighborhood S ε κ δ p).inter
    (GlobalLiouvilleField.isOpen_nonzeroLocus S j)
  have hn : ContinuousOn (fun r => nu S ε κ δ p r j) V :=
    (nu_smooth S hdet ε κ hδ p j).continuousOn.mono inter_subset_left
  have hL : ContinuousOn (fun r => (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ r j).im) V :=
    Complex.imCLM.continuous.comp_continuousOn
      ((BoundaryTangency.continuous_coordinate_drift S hdet hε hκ hδ j).continuousOn.div
        (continuous_originalCoordinate S j).continuousOn (fun r hr => hr.2))
  have he : EqOn (fun r => nu S ε κ δ p r j)
      (fun r => (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ r j).im)
      (V ∩ initialTorus S) :=
    fun r hr => congrFun (nu_eq_torus S hdet hε hκ hδ p r hr.1.1 hr.2) j
  exact he.of_subset_closure hn hL inter_subset_left
    (fun r hr => hV.inter_closure ⟨hr, dense_initialTorus S hdet r⟩) ⟨hq, hj⟩

/-- The entire complex logarithmic coefficient at a selected nonzero coordinate. -/
theorem logarithmic_selected {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (ha : q.a i ≠ 0) :
    GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ q i =
      -(κ : ℂ) + Complex.I * (nu S ε κ δ p q i : ℂ) := by
  have hr := BoundaryTangency.deep_radius S hdet hε hκ hδ p q hq i hi ha
  rw [GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ q i ha] at hr
  apply Complex.ext
  · simpa using hr
  · simpa using (nu_eq_logarithmicComponents S hdet hε hκ hδ p q hq i ha).symm

/-- Native coordinate dynamics on all simultaneous zero strata. -/
theorem coordinate_drift {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential i q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
      (-(κ : ℂ) + Complex.I * (nu S ε κ δ p q i : ℂ)) * q.a i := by
  by_cases ha : q.a i = 0
  · rw [BoundaryTangency.zero_coordinate_tangent S hdet hε hκ hδ q i ha, ha, mul_zero]
  · exact (div_eq_iff ha).mp (logarithmic_selected S hdet hε hκ hδ p q hq i hi ha)

/-- The full complex partner equation, extended as an equality of continuous
native derivatives on the open neighborhood, including every zero partner. -/
theorem partner_drift {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) q =
      (q.a i * normalizedPartner q i - 1) * nodeLogQuotient (q.a i, normalizedPartner q i) -
        normalizedPartner q i * (-(κ : ℂ) + Complex.I * (nu S ε κ δ p q i : ℂ)) := by
  letI := SmoothAtlas.charts S hdet
  let U := LocalPrimitive.neighborhood S ε κ δ p
  have hU : IsOpen U := LocalPrimitive.isOpen_neighborhood S ε κ δ p
  have hf : ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞
      (fun r => normalizedPartner r i) U :=
    fun r hr => (NormalizedPartnerNormDrift.partner_smooth S hdet p.zeroSet_independent
      i hi r hr.2.1).contMDiffWithinAt
  have hD := BoundaryTangency.contMDiffOn_complexDerivative
    (SmoothAtlas.presentation S hdet).manifold
    (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ) hU hf
  have hb := hf.continuousOn
  have ha := (continuous_originalCoordinate S i).continuousOn (s := U)
  have hQ : ContinuousOn (fun r : S.Point => nodeLogQuotient (r.a i, normalizedPartner r i)) U :=
    fun r hr => (NormalizedPartnerNormDrift.quotient_smooth S hdet p i hi r hr).continuousAt.continuousWithinAt
  have hn : ContinuousOn (fun r => (nu S ε κ δ p r i : ℂ)) U :=
    Complex.ofRealCLM.continuous.comp_continuousOn (nu_smooth S hdet ε κ hδ p i).continuousOn
  have hR := (((ha.mul hb).sub (continuousOn_const (c := (1 : ℂ)))).mul hQ).sub
    (hb.mul ((continuousOn_const (c := -(κ : ℂ))).add (hn.const_mul Complex.I)))
  have he : EqOn
      (BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i))
      (fun r => (r.a i * normalizedPartner r i - 1) * nodeLogQuotient (r.a i, normalizedPartner r i) -
        normalizedPartner r i * (-(κ : ℂ) + Complex.I * (nu S ε κ δ p r i : ℂ)))
      (U ∩ initialTorus S) := by
    intro r hr
    rw [NormalizedPartnerNormDrift.partner_drift_of_ne_zero S hdet hε hκ hδ p r hr.1 i hi (hr.2 i)]
    have hl := logarithmic_selected S hdet hε hκ hδ p r hr.1 i hi (hr.2 i)
    change _ / _ = _ at hl
    rw [hl]
  exact he.of_subset_closure hD.continuousOn hR inter_subset_left
    (fun r hr => hU.inter_closure ⟨hr, dense_initialTorus S hdet r⟩) hq

/-- Manuscript Lemma 2.5, equation (2.11), as a COMPLEX native equation. -/
theorem partner_drift_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (ha : q.a i = 0) :
    BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) q =
      (1 + (κ : ℂ) - Complex.I * (nu S ε κ δ p q i : ℂ)) * normalizedPartner q i := by
  rw [partner_drift S hdet hε hκ hδ p q hq i hi, ha, nodeLogQuotient_zero]
  ring

/-- Literal complex chain rule along a genuine native integral curve on any time set. -/
theorem hasDerivWithinAt_complex_along_integralCurve
    {n : ℕ} (M : SmoothManifold n)
    {W : (q : M.Point) → M.Tangent q}
    {γ : ℝ → M.Point} {s : Set ℝ} {t : ℝ} {f : M.Point → ℂ}
    (hγ : IsMIntegralCurveOn γ W s) (ht : t ∈ s)
    (hf : MDifferentiableAt 𝓘(ℝ, Model n) 𝓘(ℝ, ℂ) f (γ t)) :
    HasDerivWithinAt (fun u => f (γ u)) (complexDifferential M f (γ t) (W (γ t))) s t := by
  have hd := (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp
    (hf.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht))).hasDerivWithinAt
  apply hd.congr_deriv
  change complexDifferential M f (γ t) ((1 : ℝ) • W (γ t)) = _
  rw [one_smul]

/-- Pointwise membership in the neighborhood suffices; no invariant neighborhood
or globally defined flow is a premise. -/
theorem coordinate_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p →
    HasDerivWithinAt (fun u => (γ u).a i)
      ((-(κ : ℂ) + Complex.I * (nu S ε κ δ p (γ t) i : ℂ)) * (γ t).a i) s t := by
  letI := SmoothAtlas.charts S hdet
  intro hγ ht hq
  have hf := ((ContinuousLinearMap.proj i.val : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet)) (γ t)).mdifferentiableAt
      (by simp)
  have hd := hasDerivWithinAt_complex_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht hf
  change HasDerivWithinAt (fun u => (γ u).a i)
    ((SmoothAtlas.presentation S hdet).coordinateDifferential i (γ t)
      (GlobalLiouvilleField.Z S hdet ε κ hδ (γ t))) s t at hd
  rwa [coordinate_drift S hdet hε hκ hδ p (γ t) hq i hi] at hd

theorem partner_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p →
    HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
      (((γ t).a i * normalizedPartner (γ t) i - 1) *
        nodeLogQuotient ((γ t).a i, normalizedPartner (γ t) i) -
        normalizedPartner (γ t) i * (-(κ : ℂ) + Complex.I * (nu S ε κ δ p (γ t) i : ℂ))) s t := by
  letI := SmoothAtlas.charts S hdet
  intro hγ ht hq
  have hd := hasDerivWithinAt_complex_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht
    ((NormalizedPartnerNormDrift.partner_smooth S hdet p.zeroSet_independent i hi (γ t)
      hq.2.1).mdifferentiableAt (by simp))
  change HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
    (BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) (γ t)) s t at hd
  rwa [partner_drift S hdet hε hκ hδ p (γ t) hq i hi] at hd

theorem partner_hasDerivWithinAt_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p → (γ t).a i = 0 →
    HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
      ((1 + (κ : ℂ) - Complex.I * (nu S ε κ δ p (γ t) i : ℂ)) * normalizedPartner (γ t) i) s t := by
  letI := SmoothAtlas.charts S hdet
  intro hγ ht hq ha
  have hd := hasDerivWithinAt_complex_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht
    ((NormalizedPartnerNormDrift.partner_smooth S hdet p.zeroSet_independent i hi (γ t)
      hq.2.1).mdifferentiableAt (by simp))
  change HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
    (BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) (γ t)) s t at hd
  rwa [partner_drift_zero S hdet hε hκ hδ p (γ t) hq i hi ha] at hd

end ClusterSkeleton.LocalAngularDynamics
