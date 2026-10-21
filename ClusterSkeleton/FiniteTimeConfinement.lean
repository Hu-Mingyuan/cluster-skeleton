import ClusterSkeleton.AllStrataGrowth
import ClusterSkeleton.CapSet
import ClusterSkeleton.ZeroStratumEscape
import Mathlib.Analysis.ODE.Gronwall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.FiniteTimeConfinement
/-- Forward Gronwall on a closed segment, using actual derivatives. -/
theorem norm_le_exp_sub_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s‖ ≤ C * ‖f s‖) :
    ‖f b‖ ≤ ‖f a‖ * Real.exp (C * (b - a)) := by
  have hc : ContinuousOn f (Icc a b) :=
    fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hd : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s :=
    fun s hs => (hf s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f a‖) (K := C) (ε := 0) hc hd le_rfl
    (fun s hs => by simpa only [add_zero] using hb s ⟨hs.1, hs.2.le⟩)
    b ⟨hab, le_rfl⟩
  simpa only [gronwallBound_ε0] using h

/-- The same genuine derivative bound controls both time directions. -/
theorem norm_le_exp_abs_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C t₀ t : ℝ} {J : Set ℝ}
    (hJ : IsPreconnected J)
    (hf : ∀ s ∈ J, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ J, ‖f' s‖ ≤ C * ‖f s‖)
    (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    ‖f t‖ ≤ ‖f t₀‖ * Real.exp (C * |t - t₀|) := by
  rcases le_total t₀ t with hle | hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact norm_le_exp_sub_of_le hle
      (fun s hs => hf s (hJ.Icc_subset ht₀ ht hs))
      (fun s hs => hb s (hJ.Icc_subset ht₀ ht hs))
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    have hsJ (s : ℝ) (hs : s ∈ Icc (-t₀) (-t)) : -s ∈ J := by
      apply hJ.Icc_subset ht ht₀
      constructor <;> linarith [hs.1, hs.2]
    have hd : ∀ s ∈ Icc (-t₀) (-t),
        HasDerivAt (fun u => f (-u)) (-f' (-s)) s := by
      intro s hs
      simpa only [Function.comp_def, neg_one_smul] using
        (hf (-s) (hsJ s hs)).scomp s (hasDerivAt_neg s)
    have hb' : ∀ s ∈ Icc (-t₀) (-t), ‖-f' (-s)‖ ≤ C * ‖f (-s)‖ := by
      intro s hs
      simpa only [norm_neg] using hb (-s) (hsJ s hs)
    have h := norm_le_exp_sub_of_le (by linarith : -t₀ ≤ -t) hd hb'
    simpa only [neg_neg, neg_sub_neg] using h

/-- Scalar form; openness is only needed to obtain the derivative hypothesis. -/
theorem abs_le_exp_abs_sub {f f' : ℝ → ℝ} {C t₀ t : ℝ} {J : Set ℝ}
    (hJ : IsPreconnected J)
    (hf : ∀ s ∈ J, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ J, |f' s| ≤ C * |f s|)
    (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    |f t| ≤ |f t₀| * Real.exp (C * |t - t₀|) := by
  simpa only [Real.norm_eq_abs] using
    norm_le_exp_abs_sub hJ hf (by simpa only [Real.norm_eq_abs] using hb) ht₀ ht

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- A uniform scalar logarithmic bound, valid at every nonzero original coordinate. -/
theorem radial_component_bound {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : S.Point) (j : Fin d), p.a j ≠ 0 →
      |GlobalLiouvilleField.L S hdet ε κ hδ p j| ≤
        C * |GlobalLiouvilleField.A S p j| := by
  obtain ⟨C, hC, hb⟩ := NativeRadialOrbit.uniform_radial_error_bound S hdet hε hκ hδ
  refine ⟨1+C, by positivity, fun p j hj => ?_⟩
  have he := (hb p j hj).trans (mul_le_mul_of_nonneg_left
    (PrimitiveCutoffs.radial_abs_le hε (by linarith : 2*ε<κ) _) hC)
  calc
    _ = |(GlobalLiouvilleField.L S hdet ε κ hδ p j - GlobalLiouvilleField.A S p j) +
        GlobalLiouvilleField.A S p j| := by congr 1; ring
    _ ≤ |GlobalLiouvilleField.L S hdet ε κ hδ p j - GlobalLiouvilleField.A S p j| +
        |GlobalLiouvilleField.A S p j| := abs_add_le _ _
    _ ≤ C * |GlobalLiouvilleField.A S p j| + |GlobalLiouvilleField.A S p j| :=
      add_le_add he le_rfl
    _ = _ := by ring

/-- Positive two-sided modulus bounds extracted from a genuine logarithmic bound. -/
theorem norm_bounds_of_log_abs_le {z : ℂ} (hz : z ≠ 0) {M : ℝ}
    (hM : |Real.log ‖z‖| ≤ M) :
    Real.exp (-M) ≤ ‖z‖ ∧ ‖z‖ ≤ Real.exp M := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := abs_le.mp hM
  constructor
  · calc
      _ ≤ Real.exp (Real.log ‖z‖) := Real.exp_le_exp.mpr h.1
      _ = _ := Real.exp_log hn
  · calc
      _ = Real.exp (Real.log ‖z‖) := (Real.exp_log hn).symm
      _ ≤ _ := Real.exp_le_exp.mpr h.2

/-- A finite uniform bound for the normalized partner at an initial zero index.
The exact squared-norm law includes arbitrary partners, including zero. -/
theorem normalizedPartner_norm_le {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {s t T : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) (hs : s ∈ J) (ht : t ∈ J)
    (hT : |t-s| ≤ T) (i : S.Mutable) (ha : (γ s).a i = 0) :
    ‖normalizedPartner (γ t) i‖ ≤
      Real.exp (2*(1+κ)*T) * Complex.normSq (normalizedPartner (γ s) i) + 1 := by
  have hc : 0 ≤ 2*(1+κ) := by linarith
  have hexp : Real.exp (2*(1+κ)*(t-s)) ≤ Real.exp (2*(1+κ)*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hT) hc)
  have hn := ZeroStratumPartnerDynamics.normSq_eq_exp_mul S hdet hε hκ hδ
    hγ hJ hs ht i ha
  have hb : ‖normalizedPartner (γ t) i‖ ^ 2 ≤
      Real.exp (2*(1+κ)*T) * Complex.normSq (normalizedPartner (γ s) i) := by
    rw [← Complex.normSq_eq_norm_sq, hn]
    exact mul_le_mul_of_nonneg_right hexp (Complex.normSq_nonneg _)
  nlinarith [sq_nonneg (‖normalizedPartner (γ t) i‖ - 1),
    norm_nonneg (normalizedPartner (γ t) i)]


theorem logarithmic_component_bound {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : S.Point) (j : Fin d), p.a j ≠ 0 →
      |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re| ≤
        C * |GlobalLiouvilleField.A S p j| := by
  obtain ⟨C, hC, hb⟩ := radial_component_bound S hdet hε hκ hδ
  refine ⟨C, hC, fun p j hj => ?_⟩
  rw [← GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ p j hj]
  exact hb p j hj

/-- Every fixed-mask log radius satisfies a uniform two-sided exponential bound. -/
theorem fixed_mask_log_bound {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
      (letI := SmoothAtlas.charts S hdet;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
          (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
      IsOpen J → IsPreconnected J → t₀ ∈ J → ∀ t ∈ J, ∀ j : Fin d,
        |LocalAngularDynamics.maskedLogs S (γ t₀).zeroSet (γ t) j| ≤
          |LocalAngularDynamics.maskedLogs S (γ t₀).zeroSet (γ t₀) j| *
            Real.exp (C * |t - t₀|) := by
  obtain ⟨C, hC, hCb⟩ := logarithmic_component_bound S hdet hε hκ hδ
  refine ⟨C, hC, fun γ J t₀ hγ ho hp ht₀ t ht j => ?_⟩
  classical
  by_cases hj : j ∈ (γ t₀).zeroSet
  · simp only [LocalAngularDynamics.maskedLogs, hj, ite_true, abs_zero, zero_mul, le_refl]
  · have hjc : j ∈ (γ t₀).zeroSetᶜ := Finset.mem_compl.mpr hj
    have hd : ∀ s ∈ J,
        HasDerivAt (fun u => LocalAngularDynamics.maskedLogs S (γ t₀).zeroSet (γ u) j)
          (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ s) j).re s := by
      intro s hs
      exact (AllStrataGrowth.fixed_mask_hasDerivWithinAt S hdet hε hκ hδ
        hγ hp ht₀ hs j hjc).hasDerivAt (ho.mem_nhds hs)
    have hb : ∀ s ∈ J,
        |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ (γ s) j).re| ≤
          C * |LocalAngularDynamics.maskedLogs S (γ t₀).zeroSet (γ s) j| := by
      intro s hs
      have hz := ZeroStratumInvariance.zeroSet_eq S hdet hε hκ hδ hγ hp hs ht₀
      have hn := AllStrataGrowth.coordinate_ne_zero_of_mem_compl S (γ s) j (hz.symm ▸ hjc)
      simpa only [LocalAngularDynamics.maskedLogs, hj, ite_false, GlobalLiouvilleField.A] using
        hCb (γ s) j hn
    exact abs_le_exp_abs_sub hp hd hb ht₀ ht


end ClusterSkeleton.FiniteTimeConfinement

namespace ClusterSkeleton.CoordinateBounds

variable {d : ℕ} (S : Seed d)

/-- A box in the actual exchange carrier, with a positive frozen lower bound. -/
def coordinateBox (A B η : ℝ) : Set S.Point :=
  {p | (∀ j, ‖p.a j‖ ≤ A) ∧ (∀ i : S.Mutable, ‖p.b i‖ ≤ B) ∧
    ∀ f, f ∉ S.mutable → η ≤ ‖p.a f‖}

private abbrev Ambient := (Fin d → ℂ) × (S.Mutable → ℂ)

private def ambientBox (A B η : ℝ) : Set (Ambient S) :=
  {x | (∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
    (∀ j, ‖x.1 j‖ ≤ A) ∧ (∀ i : S.Mutable, ‖x.2 i‖ ≤ B) ∧
    ∀ f, f ∉ S.mutable → η ≤ ‖x.1 f‖}

private theorem isClosed_ambientBox (A B η : ℝ) :
    IsClosed (ambientBox S A B η) := by
  have he : IsClosed {x : Ambient S | ∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun i => isClosed_eq (by fun_prop) ?_
    unfold Seed.positiveMonomial Seed.negativeMonomial
    fun_prop
  have ha : IsClosed {x : Ambient S | ∀ j, ‖x.1 j‖ ≤ A} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hb : IsClosed {x : Ambient S | ∀ i : S.Mutable, ‖x.2 i‖ ≤ B} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hf : IsClosed {x : Ambient S | ∀ f, f ∉ S.mutable → η ≤ ‖x.1 f‖} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_le continuous_const (by fun_prop)
  exact he.inter (ha.inter (hb.inter hf))

private theorem image_coordinateBox (A B : ℝ) {η : ℝ} (hη : 0 < η) :
    Subtype.val '' coordinateBox S A B η = ambientBox S A B η := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2.1, hp⟩
  · intro hx
    have hfn : ∀ f, f ∉ S.mutable → x.1 f ≠ 0 := by
      intro f hf hzero
      exact (not_le_of_gt hη) (by simpa only [hzero, norm_zero] using hx.2.2.2 f hf)
    exact ⟨⟨x, hx.1, hfn⟩, hx.2, rfl⟩

/-- The topology is the inherited topology of the literal exchange-equation
carrier. The radius includes zero so the empty-coordinate cases need no inhabitant. -/
theorem isCompact_coordinateBox (A B : ℝ) {η : ℝ} (hη : 0 < η) :
    IsCompact (coordinateBox S A B η) := by
  let r : ℝ := max 0 (max A B)
  have hr : 0 ≤ r := le_max_left _ _
  have hAr : A ≤ r := (le_max_left A B).trans (le_max_right _ _)
  have hBr : B ≤ r := (le_max_right A B).trans (le_max_right _ _)
  have hclosed : IsClosed (Subtype.val '' coordinateBox S A B η) := by
    rw [image_coordinateBox S A B hη]
    exact isClosed_ambientBox S A B η
  have hbound : Subtype.val '' coordinateBox S A B η ⊆
      Metric.closedBall (0 : Ambient S) r := by
    rintro x ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change max ‖Seed.Point.a (S := S) p‖ ‖Seed.Point.b (S := S) p‖ ≤ r
    exact max_le
      ((pi_norm_le_iff_of_nonneg hr).2 fun j => (hp.1 j).trans hAr)
      ((pi_norm_le_iff_of_nonneg hr).2 fun i => (hp.2.1 i).trans hBr)
  have hc : IsCompact (Subtype.val '' coordinateBox S A B η) :=
    (isCompact_closedBall (0 : Ambient S) r).of_isClosed_subset hclosed hbound
  exact Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr hc

/-- Every fixed seed monomial has a uniform polynomial bound on a coordinate box.
The finite sum is taken over all original indices and may be empty. -/
theorem monomials_uniformly_bounded {A : ℝ} (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a : Fin d → ℂ), (∀ j, ‖a j‖ ≤ A) →
      ∀ i : Fin d, ‖S.positiveMonomial a i‖ ≤ M ∧ ‖S.negativeMonomial a i‖ ≤ M := by
  let P : Fin d → ℝ := fun i => ∏ j : Fin d, A ^ (S.B i j).toNat
  let Q : Fin d → ℝ := fun i => ∏ j : Fin d, A ^ (-S.B i j).toNat
  have hP : ∀ i, 0 ≤ P i := fun i => Finset.prod_nonneg fun j _ => pow_nonneg hA _
  have hQ : ∀ i, 0 ≤ Q i := fun i => Finset.prod_nonneg fun j _ => pow_nonneg hA _
  let M : ℝ := ∑ i : Fin d, (P i + Q i)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => add_nonneg (hP i) (hQ i)
  refine ⟨M, hM, fun a ha i => ?_⟩
  have hs : P i + Q i ≤ M :=
    Finset.single_le_sum (fun j _ => add_nonneg (hP j) (hQ j)) (Finset.mem_univ i)
  have hp : ‖S.positiveMonomial a i‖ ≤ P i := by
    simp only [Seed.positiveMonomial, norm_prod, norm_pow]
    exact Finset.prod_le_prod₀ (fun j _ => pow_nonneg (norm_nonneg _) _)
      (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hq : ‖S.negativeMonomial a i‖ ≤ Q i := by
    simp only [Seed.negativeMonomial, norm_prod, norm_pow]
    exact Finset.prod_le_prod₀ (fun j _ => pow_nonneg (norm_nonneg _) _)
      (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  exact ⟨hp.trans ((le_add_of_nonneg_right (hQ i)).trans hs),
    hq.trans ((le_add_of_nonneg_left (hP i)).trans hs)⟩

/-- Recovery at a zero original coordinate uses the proved nonzero denominator. -/
theorem partner_eq_normalized_mul {p : S.Point} (i : S.Mutable) (ha : p.a i = 0) :
    p.b i = normalizedPartner p i * S.negativeMonomial p.a i := by
  unfold normalizedPartner
  exact (div_mul_cancel₀ (p.b i) (ZeroStratumEscape.denominator_ne_zero S i ha)).symm

/-- Away from zero the original exchange equation recovers the original partner. -/
theorem partner_eq_div {p : S.Point} (i : S.Mutable) (ha : p.a i ≠ 0) :
    p.b i = (S.positiveMonomial p.a i + S.negativeMonomial p.a i) / p.a i := by
  rw [← p.exchange i, mul_div_cancel_left₀ _ ha]

/-- Bounds on normalized zero partners and nonzero original coordinates control
all literal mutable partners. No normalization is used where its denominator can vanish. -/
theorem norm_partner_le_of_bounds {p : S.Point} {M N η : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hη : 0 < η)
    (hmon : ∀ j : Fin d,
      ‖S.positiveMonomial p.a j‖ ≤ M ∧ ‖S.negativeMonomial p.a j‖ ≤ M)
    (hlo : ∀ i : S.Mutable, p.a i ≠ 0 → η ≤ ‖p.a i‖)
    (hz : ∀ i : S.Mutable, p.a i = 0 → ‖normalizedPartner p i‖ ≤ N)
    (i : S.Mutable) :
    ‖p.b i‖ ≤ max (N * M) ((M + M) / η) := by
  by_cases hi : p.a i = 0
  · rw [partner_eq_normalized_mul S i hi, norm_mul]
    exact (mul_le_mul (hz i hi) (hmon i).2 (norm_nonneg _) hN).trans (le_max_left _ _)
  · rw [partner_eq_div S i hi, norm_div]
    have hn : ‖S.positiveMonomial p.a i + S.negativeMonomial p.a i‖ ≤ M + M :=
      (norm_add_le _ _).trans (add_le_add (hmon i).1 (hmon i).2)
    exact (div_le_div₀ (add_nonneg hM hM) hn hη (hlo i hi)).trans (le_max_right _ _)

end ClusterSkeleton.CoordinateBounds

namespace ClusterSkeleton.FiniteTimeConfinement
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Uniform bounds in the literal original coordinates on a bounded time horizon.
The constants are selected before the native curve, its open domain, and its initial time. -/
theorem uniform_original_bounds {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (T : ℝ) (_hT : 0 ≤ T) :
    ∃ η A B : ℝ, 0 < η ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
        (letI := SmoothAtlas.charts S hdet;
          IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
            (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
        IsOpen J → IsPreconnected J → t₀ ∈ J → γ t₀ = p →
        ∀ t ∈ J, |t-t₀| ≤ T →
          (γ t).zeroSet = p.zeroSet ∧
          (∀ j, ‖(γ t).a j‖ ≤ A) ∧
          (∀ j, p.a j ≠ 0 → η ≤ ‖(γ t).a j‖) ∧
          (∀ i : S.Mutable, ‖(γ t).b i‖ ≤ B) := by
  classical
  obtain ⟨C, hC, hlog⟩ := fixed_mask_log_bound S hdet hε hκ hδ
  let M : ℝ := AllStrataGrowth.R S p * Real.exp (C*T)
  let η : ℝ := Real.exp (-M)
  let A : ℝ := Real.exp M
  have hη : 0 < η := Real.exp_pos _
  have hA : 0 ≤ A := (Real.exp_pos _).le
  obtain ⟨Q, hQ, hmon⟩ := CoordinateBounds.monomials_uniformly_bounded S hA
  let N : ℝ := ∑ i : S.Mutable,
    (Real.exp (2*(1+κ)*T) * Complex.normSq (normalizedPartner p i) + 1)
  have hNterm (i : S.Mutable) :
      0 ≤ Real.exp (2*(1+κ)*T) * Complex.normSq (normalizedPartner p i) + 1 := by
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)) zero_le_one
  have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => hNterm i
  let B : ℝ := max (N*Q) ((Q+Q)/η)
  have hB : 0 ≤ B := (mul_nonneg hN hQ).trans (le_max_left _ _)
  refine ⟨η, A, B, hη, hA, hB, fun γ J t₀ hγ ho hc ht₀ hinit t ht htime => ?_⟩
  have hz : (γ t).zeroSet = p.zeroSet := by
    simpa only [hinit] using
      ZeroStratumInvariance.zeroSet_eq S hdet hε hκ hδ hγ hc ht ht₀
  have hiff (j : Fin d) : p.a j = 0 ↔ (γ t).a j = 0 := by
    simpa only [hinit] using
      ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ hc ht₀ ht j
  have hl (j : Fin d) (hj : p.a j ≠ 0) : |Real.log ‖(γ t).a j‖| ≤ M := by
    have hjz : j ∉ p.zeroSet := fun hjz => hj ((p.mem_zeroSet j).mp hjz).2
    have hb := hlog γ J t₀ hγ ho hc ht₀ t ht j
    rw [hinit] at hb
    have hbase : |LocalAngularDynamics.maskedLogs S p.zeroSet p j| ≤ AllStrataGrowth.R S p :=
      Finset.single_le_sum (fun k _ => abs_nonneg (LocalAngularDynamics.maskedLogs S p.zeroSet p k)) (Finset.mem_univ j)
    have hexp : Real.exp (C*|t-t₀|) ≤ Real.exp (C*T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hC.le)
    have hb' := hb.trans (mul_le_mul hbase hexp (Real.exp_pos _).le
      (AllStrataGrowth.R_nonneg S p))
    simpa only [LocalAngularDynamics.maskedLogs, hjz, ite_false] using hb'
  have hnonzero (j : Fin d) (hj : p.a j ≠ 0) : (γ t).a j ≠ 0 :=
    fun h => hj ((hiff j).mpr h)
  have ha : ∀ j, ‖(γ t).a j‖ ≤ A := by
    intro j
    by_cases hj : p.a j = 0
    · simpa only [(hiff j).mp hj, norm_zero] using hA
    · exact (norm_bounds_of_log_abs_le (hnonzero j hj) (hl j hj)).2
  have hlo : ∀ j, p.a j ≠ 0 → η ≤ ‖(γ t).a j‖ := by
    intro j hj
    exact (norm_bounds_of_log_abs_le (hnonzero j hj) (hl j hj)).1
  refine ⟨hz, ha, hlo, fun i => ?_⟩
  apply CoordinateBounds.norm_partner_le_of_bounds S hQ hN hη (hmon _ ha)
  · intro i hi
    exact hlo i (fun hp => hi ((hiff i).mp hp))
  · intro i hi
    have hip : p.a i = 0 := (hiff i).mpr hi
    have hb := normalizedPartner_norm_le S hdet hε hκ hδ hγ hc ht₀ ht htime i
      (by simpa only [hinit] using hip)
    rw [hinit] at hb
    exact hb.trans (Finset.single_le_sum (fun j _ => hNterm j) (Finset.mem_univ i))

/-- Finite-time compact confinement for the exact native global Liouville field.
Only the segment joining two times must lie in the open preconnected domain;
the full closed time horizon need not be contained in it. -/
theorem finite_time_compact_confinement {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : Set S.Point, IsCompact K ∧
      ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
        (letI := SmoothAtlas.charts S hdet;
          IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
            (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
        IsOpen J → IsPreconnected J → t₀ ∈ J → γ t₀ = p →
        ∀ t ∈ J, |t-t₀| ≤ T → γ t ∈ K := by
  obtain ⟨η, A, B, hη, hA, hB, hb⟩ := uniform_original_bounds S hdet hε hκ hδ p T hT
  refine ⟨CoordinateBounds.coordinateBox S A B η,
    CoordinateBounds.isCompact_coordinateBox S A B hη,
    fun γ J t₀ hγ ho hc ht₀ hinit t ht htime => ?_⟩
  obtain ⟨hz, ha, hlo, hpartners⟩ := hb γ J t₀ hγ ho hc ht₀ hinit t ht htime
  exact ⟨ha, hpartners, fun f hf => hlo f (p.frozen_ne_zero f hf)⟩

/-- The closure of every bounded-horizon image lies in a single compact set
chosen before the curve or domain, including domains with omitted finite endpoints. -/
theorem bounded_horizon_closure {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : Set S.Point, IsCompact K ∧
      ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
        (letI := SmoothAtlas.charts S hdet;
          IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
            (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
        IsOpen J → IsPreconnected J → t₀ ∈ J → γ t₀ = p →
        closure (γ '' {t | t ∈ J ∧ |t-t₀| ≤ T}) ⊆ K ∧
        IsCompact (closure (γ '' {t | t ∈ J ∧ |t-t₀| ≤ T})) := by
  obtain ⟨K, hK, hb⟩ := finite_time_compact_confinement S hdet hε hκ hδ p T hT
  refine ⟨K, hK, fun γ J t₀ hγ ho hc ht₀ hinit => ?_⟩
  have him : γ '' {t | t ∈ J ∧ |t-t₀| ≤ T} ⊆ K := by
    rintro q ⟨t, ⟨ht, htime⟩, rfl⟩
    exact hb γ J t₀ hγ ho hc ht₀ hinit t ht htime
  have hcl := closure_minimal him hK.isClosed
  exact ⟨hcl, hK.of_isClosed_subset isClosed_closure hcl⟩

end ClusterSkeleton.FiniteTimeConfinement
