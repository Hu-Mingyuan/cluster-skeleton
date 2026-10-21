import ClusterSkeleton.ZeroStratumInvariance
import ClusterSkeleton.NormalizedPartnerNormDrift

/-! Exact normalized-partner norm dynamics on an initially zero coordinate of
a genuine native Liouville curve. The zero stratum is derived, not assumed. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.ZeroStratumPartnerDynamics

/-- A native within-derivative linear ODE on a preconnected real set has the
exact exponential law, including relative endpoints and singleton domains. -/
theorem exp_law_of_hasDerivWithinAt {f : ℝ → ℝ} {J : Set ℝ} {c s t : ℝ}
    (hJ : IsPreconnected J)
    (hd : ∀ u ∈ J, HasDerivWithinAt f (c * f u) J u)
    (hs : s ∈ J) (ht : t ∈ J) :
    f t = Real.exp (c * (t - s)) * f s := by
  have hprod : ∀ u ∈ J,
      HasDerivWithinAt (fun v => Real.exp (c * (t - v)) * f v) 0 J u := by
    intro u hu
    have he : HasDerivWithinAt (fun v : ℝ => Real.exp (c * (t - v)))
        (Real.exp (c * (t - u)) * (-c)) J u := by
      simpa using (((hasDerivAt_const u t).sub (hasDerivAt_id u)).const_mul c).exp.hasDerivWithinAt
    convert he.mul (hd u hu) using 1
    ring
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hprod (fun u hu => (show ‖(0 : ℝ)‖ ≤ (0 : ℝ) by simp)) hJ.convex hs ht
  have hz : ‖f t - Real.exp (c * (t - s)) * f s‖ ≤ 0 := by
    simpa using hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Composition of native zero-stratum invariance and the global pointwise
partner derivative. No single node neighborhood contains the curve by assumption. -/
theorem normSq_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2 * (1 + κ) * Complex.normSq (normalizedPartner (γ t) i)) J t := by
  exact NormalizedPartnerNormDrift.normSq_hasDerivWithinAt_zero S hdet hε hκ hδ i hγ ht
    ((ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs ht i).mp ha)

/-- Exact exponential squared-norm growth in either time direction. -/
theorem normSq_eq_exp_mul {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    Complex.normSq (normalizedPartner (γ t) i) =
      Real.exp (2 * (1 + κ) * (t - s)) * Complex.normSq (normalizedPartner (γ s) i) :=
  exp_law_of_hasDerivWithinAt hJ
    (fun u hu => normSq_hasDerivWithinAt S hdet hε hκ hδ hγ hJ hs hu i ha) hs ht

/-- A normalized partner vanishes at one time iff it vanishes at any other time
in the same native curve domain with initially zero original coordinate. -/
theorem partner_zero_iff {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    normalizedPartner (γ s) i = 0 ↔ normalizedPartner (γ t) i = 0 := by
  have he := normSq_eq_exp_mul S hdet hε hκ hδ hγ hJ hs ht i ha
  have hz : Complex.normSq (normalizedPartner (γ t) i) = 0 ↔
      Complex.normSq (normalizedPartner (γ s) i) = 0 := by
    rw [he, mul_eq_zero]
    simp only [Real.exp_ne_zero, false_or]
  simpa only [Complex.normSq_eq_zero] using hz.symm

theorem partner_ne_zero_iff {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    normalizedPartner (γ s) i ≠ 0 ↔ normalizedPartner (γ t) i ≠ 0 :=
  not_congr (partner_zero_iff S hdet hε hκ hδ hγ hJ hs ht i ha)

/-- Strict growth needs a nonzero partner; the exact law also covers zero partners. -/
theorem normSq_lt {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0)
    (hb : normalizedPartner (γ s) i ≠ 0) (hst : s < t) :
    Complex.normSq (normalizedPartner (γ s) i) <
      Complex.normSq (normalizedPartner (γ t) i) := by
  rw [normSq_eq_exp_mul S hdet hε hκ hδ hγ hJ hs ht i ha]
  have hc : 0 < 2 * (1 + κ) := by linarith
  have he : 1 < Real.exp (2 * (1 + κ) * (t - s)) :=
    Real.one_lt_exp_iff.mpr (mul_pos hc (sub_pos.mpr hst))
  simpa only [one_mul] using mul_lt_mul_of_pos_right he (Complex.normSq_pos.mpr hb)

/-- Strict monotonicity on the whole relative domain, from one nonzero partner. -/
theorem strictMonoOn_normSq {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s : ℝ} (hs : s ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) (hb : normalizedPartner (γ s) i ≠ 0) :
    StrictMonoOn (fun t => Complex.normSq (normalizedPartner (γ t) i)) J := by
  intro u hu v hv huv
  exact normSq_lt S hdet hε hκ hδ hγ hJ hu hv i
    ((ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs hu i).mp ha)
    ((partner_ne_zero_iff S hdet hε hκ hδ hγ hJ hs hu i ha).mp hb) huv

end ClusterSkeleton.ZeroStratumPartnerDynamics
