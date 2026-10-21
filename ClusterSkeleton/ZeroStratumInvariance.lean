import ClusterSkeleton.BoundaryTangency
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Clopen

/-! Native squared-coordinate-norm law and zero-stratum invariance along the
accepted Liouville field, on arbitrary preconnected relative time domains. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.ZeroStratumInvariance

theorem local_zero_propagation {f : ℝ → ℝ} {J : Set ℝ} {k s r : ℝ}
    (hJ : IsPreconnected J) (hs : s ∈ J) (hr : 0 < r) (hs0 : f s = 0)
    (hd : ∀ t ∈ J ∩ Metric.ball s r,
      HasDerivWithinAt f (-2 * k * f t) (J ∩ Metric.ball s r) t) :
    ∀ t ∈ J ∩ Metric.ball s r, f t = 0 := by
  let K := J ∩ Metric.ball s r
  have hK : Convex ℝ K := hJ.convex.inter (convex_ball s r)
  have hsK : s ∈ K := ⟨hs, Metric.mem_ball_self hr⟩
  have hprod : ∀ t ∈ K,
      HasDerivWithinAt (fun u => Real.exp (2 * k * u) * f u) 0 K t := by
    intro t ht
    have he : HasDerivWithinAt (fun u : ℝ => Real.exp (2 * k * u))
        (Real.exp (2 * k * t) * (2 * k)) K t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * k)).exp.hasDerivWithinAt
    convert he.mul (hd t ht) using 1
    ring
  intro t ht
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hprod (fun t ht => (show ‖(0 : ℝ)‖ ≤ (0 : ℝ) by simp)) hK hsK ht
  have heq : Real.exp (2 * k * t) * f t = 0 := by
    have hn : ‖Real.exp (2 * k * t) * f t‖ ≤ 0 := by
      simpa only [hs0, mul_zero, sub_zero, zero_mul] using hb
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  exact (mul_eq_zero.mp heq).resolve_left (Real.exp_ne_zero _)

theorem zero_iff_of_local_linear_ode {f : ℝ → ℝ} {J : Set ℝ} {k : ℝ}
    (hJ : IsPreconnected J) (hf : ContinuousOn f J)
    (hd : ∀ s ∈ J, f s = 0 → ∃ r > 0, ∀ t ∈ J ∩ Metric.ball s r,
      HasDerivWithinAt f (-2 * k * f t) (J ∩ Metric.ball s r) t)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) : f s = 0 ↔ f t = 0 := by
  let Z : Set J := {u | f u = 0}
  have hZclosed : IsClosed Z := isClosed_eq hf.domRestrict continuous_const
  have hZopen : IsOpen Z := by
    apply Metric.isOpen_iff.mpr
    intro u hu
    obtain ⟨r, hr, hdr⟩ := hd u u.property hu
    refine ⟨r, hr, ?_⟩
    intro v hv
    exact local_zero_propagation hJ u.property hr hu hdr v
      ⟨v.property, hv⟩
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hJ
  have hZ : IsClopen Z := ⟨hZclosed, hZopen⟩
  have hprop : ∀ u v : J, f u = 0 → f v = 0 := by
    intro u v hu
    have heq : Z = Set.univ := hZ.eq_univ ⟨u, hu⟩
    have hv : v ∈ Z := by rw [heq]; exact Set.mem_univ _
    exact hv
  exact ⟨hprop ⟨s, hs⟩ ⟨t, ht⟩, hprop ⟨t, ht⟩ ⟨s, hs⟩⟩


variable {d : ℕ} (S : Seed d)

theorem coordinate_smooth (P : SmoothPresentation S) (i : Fin d) :
    letI := P.charts
    ContMDiff 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞ (fun q : S.Point => q.a i) := by
  letI := P.charts
  exact (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
    (TorusNondegeneracy.original_smooth S P)

theorem differential_normSq (P : SmoothPresentation S) (i : Fin d) (q : S.Point)
    (v : P.manifold.Tangent q) :
    P.manifold.scalarDerivative (fun r : S.Point => Complex.normSq (r.a i)) q v =
      2 * inner ℝ (q.a i) (P.coordinateDifferential i q v) := by
  letI := P.charts
  have hc := ((coordinate_smooth S P i) q).mdifferentiableAt (by simp)
  have hn : HasFDerivAt (fun z : ℂ => Complex.normSq z) (2 • innerSL ℝ (q.a i)) (q.a i) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (hasStrictFDerivAt_norm_sq (q.a i)).hasFDerivAt
  have h := hn.hasMFDerivAt.comp q hc.hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
    (fun r : S.Point => Complex.normSq (r.a i)) q v = _
  erw [h.mfderiv]
  change (2 : ℕ) • inner ℝ (q.a i) (P.coordinateDifferential i q v) = _
  simp only [two_smul, two_mul]

theorem inner_eq_normSq_mul_re_div (z w : ℂ) (hz : z ≠ 0) :
    inner ℝ z w = Complex.normSq z * (w / z).re := by
  have hn : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.div_re]
  field_simp
  ring

variable (hdet : S.Unimodular)

theorem normSq_drift {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun r : S.Point => Complex.normSq (r.a i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
        -2 * κ * Complex.normSq (q.a i) := by
  rw [differential_normSq]
  by_cases ha : q.a i = 0
  · simp [ha]
  · rw [inner_eq_normSq_mul_re_div _ _ ha]
    have hr := BoundaryTangency.deep_radius S hdet hε hκ hδ p q hq i hi ha
    rw [GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ q i ha] at hr
    change ((SmoothAtlas.presentation S hdet).coordinateDifferential i q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) / q.a i).re = -κ at hr
    rw [hr]
    ring

theorem coordinate_hasDerivWithinAt {ε κ δ : ℝ} (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    {t : ℝ} (ht : t ∈ J) (i : Fin d) :
    HasDerivWithinAt (fun s => (γ s).a i)
      ((SmoothAtlas.presentation S hdet).coordinateDifferential i (γ t)
        (GlobalLiouvilleField.Z S hdet ε κ hδ (γ t))) J t := by
  letI := SmoothAtlas.charts S hdet
  have hc := ((coordinate_smooth S (SmoothAtlas.presentation S hdet) i) (γ t)).mdifferentiableAt
    (by simp)
  have hd := (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp
    (hc.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht))).hasDerivWithinAt
  apply hd.congr_deriv
  change (SmoothAtlas.presentation S hdet).coordinateDifferential i (γ t)
    ((1 : ℝ) • GlobalLiouvilleField.Z S hdet ε κ hδ (γ t)) = _
  rw [one_smul]

theorem normSq_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    {t : ℝ} (ht : t ∈ J) (hq : γ t ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    HasDerivWithinAt (fun s => Complex.normSq ((γ s).a i))
      (-2 * κ * Complex.normSq ((γ t).a i)) J t := by
  have hd := (coordinate_hasDerivWithinAt S hdet hδ hγ ht i).norm_sq
  have hv := normSq_drift S hdet hε hκ hδ p (γ t) hq i hi
  rw [differential_normSq] at hv
  simpa only [Complex.normSq_eq_norm_sq] using hd.congr_deriv hv

/-- Every coordinate zero persists in both directions on an arbitrary preconnected
relative time domain of a genuine integral curve of the accepted field. -/
theorem coordinate_zero_iff {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : Fin d) : (γ s).a i = 0 ↔ (γ t).a i = 0 := by
  letI := SmoothAtlas.charts S hdet
  by_cases hi : i ∈ S.mutable
  · have hf : ContinuousOn (fun u => Complex.normSq ((γ u).a i)) J :=
      Complex.continuous_normSq.comp_continuousOn
        ((coordinate_smooth S (SmoothAtlas.presentation S hdet) i).continuous.comp_continuousOn
          hγ.continuousOn)
    have hd : ∀ u ∈ J, Complex.normSq ((γ u).a i) = 0 →
        ∃ r > 0, ∀ v ∈ J ∩ Metric.ball u r,
          HasDerivWithinAt (fun w => Complex.normSq ((γ w).a i))
            (-2 * κ * Complex.normSq ((γ v).a i)) (J ∩ Metric.ball u r) v := by
      intro u hu hz
      have ha : (γ u).a i = 0 := Complex.normSq_eq_zero.mp hz
      have hp : i ∈ (γ u).zeroSet := ((γ u).mem_zeroSet i).mpr ⟨hi, ha⟩
      have hn := (hγ.continuousWithinAt hu).preimage_mem_nhdsWithin
        ((LocalPrimitive.isOpen_neighborhood S ε κ δ (γ u)).mem_nhds
          (LocalPrimitive.mem_neighborhood S ε κ hδ (γ u)))
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hn
      refine ⟨r, hr, ?_⟩
      intro v hv
      exact (normSq_hasDerivWithinAt S hdet hε hκ hδ (γ u) hγ hv.1
        (hsub ⟨hv.2, hv.1⟩) ⟨i, hi⟩ hp).mono inter_subset_left
    simpa only [Complex.normSq_eq_zero] using zero_iff_of_local_linear_ode hJ hf hd hs ht
  · exact iff_of_false ((γ s).frozen_ne_zero i hi) ((γ t).frozen_ne_zero i hi)

/-- The full independent zero stratum is constant along the given native curve. -/
theorem zeroSet_eq {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    (γ s).zeroSet = (γ t).zeroSet := by
  ext i
  simp only [Seed.Point.mem_zeroSet]
  rw [coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs ht i]

/-- Nonvanishing persists in either time direction, including frozen coordinates. -/
theorem coordinate_ne_zero_iff {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : Fin d) : (γ s).a i ≠ 0 ↔ (γ t).a i ≠ 0 :=
  not_congr (coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs ht i)

end ClusterSkeleton.ZeroStratumInvariance
