import ClusterSkeleton.ZeroStratumPartnerDynamics
import ClusterSkeleton.TrappedSet
import Mathlib.Topology.Order.Compact

/-! Compact escape for native Liouville curves with an initially zero original
coordinate and a nonzero original exchange partner. Compact sets may meet larger
zero strata: normalization is justified at each point using its own zero set. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.ZeroStratumEscape

variable {d : ℕ} (S : Seed d)

theorem isClosed_zero_coordinate (i : Fin d) :
    IsClosed {p : S.Point | p.a i = 0} :=
  isClosed_eq (continuous_originalCoordinate S i) continuous_const

/-- The denominator is nonzero on the entire original-coordinate zero locus. -/
theorem denominator_ne_zero {p : S.Point} (i : S.Mutable) (ha : p.a i = 0) :
    S.negativeMonomial p.a i ≠ 0 :=
  negativeMonomial_ne_zero_on_independent_locus p.zeroSet_independent
    (PrimitiveLocalization.mem_zero_locus p) ((p.mem_zeroSet i).mpr ⟨i.property, ha⟩)

/-- No global continuity of the quotient is asserted. -/
theorem continuousAt_normalizedPartner {p : S.Point} (i : S.Mutable)
    (ha : p.a i = 0) : ContinuousAt (fun q : S.Point => normalizedPartner q i) p :=
  PrimitiveLocalization.continuousAt_normalizedPartner p.zeroSet_independent
    (PrimitiveLocalization.mem_zero_locus p) i ((p.mem_zeroSet i).mpr ⟨i.property, ha⟩)

theorem normalizedPartner_eq_zero_iff {p : S.Point} (i : S.Mutable) (ha : p.a i = 0) :
    normalizedPartner p i = 0 ↔ p.b i = 0 := by
  simp only [normalizedPartner, div_eq_zero_iff, denominator_ne_zero S i ha, or_false]

theorem compact_zero_slice_bound (i : S.Mutable) {K : Set S.Point} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ p ∈ K, p.a i = 0 → Complex.normSq (normalizedPartner p i) ≤ M := by
  have hslice := hK.inter_right (isClosed_zero_coordinate S i)
  have hcont : ContinuousOn (fun p : S.Point => Complex.normSq (normalizedPartner p i))
      (K ∩ {p : S.Point | p.a i = 0}) := by
    intro p hp
    exact (Complex.continuous_normSq.continuousAt.comp
      (continuousAt_normalizedPartner S i hp.2)).continuousWithinAt
  obtain ⟨M, hM⟩ := hslice.bddAbove_image hcont
  exact ⟨M, fun p hp ha => hM ⟨p, ⟨hp, ha⟩, rfl⟩⟩

variable (hdet : S.Unimodular)

/-- Every compact subset of the actual exchange carrier is eventually avoided.
Zero invariance and normalized growth are derived from the accepted native ODE
theorems; neither raw-partner growth nor a fixed chart is used. -/
theorem eventually_not_mem_compact {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici t₀))
    (i : S.Mutable) (ha : (γ t₀).a i = 0) (hb : (γ t₀).b i ≠ 0)
    {K : Set S.Point} (hK : IsCompact K) :
    ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K := by
  obtain ⟨M, hM⟩ := compact_zero_slice_bound S i hK
  let A := Complex.normSq (normalizedPartner (γ t₀) i)
  let c := 2 * (1 + κ)
  have hA : 0 < A := Complex.normSq_pos.mpr
    (fun hz => hb ((normalizedPartner_eq_zero_iff S i ha).mp hz))
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨max t₀ (t₀ + (M / A + 1) / c), le_max_left _ _, ?_⟩
  intro t ht hmem
  have ht₀ : t ∈ Ici t₀ := (le_max_left _ _).trans ht
  have haz := (ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ
    hγ isPreconnected_Ici (show t₀ ∈ Ici t₀ by simp) ht₀ i).mp ha
  have he := ZeroStratumPartnerDynamics.normSq_eq_exp_mul S hdet hε hκ hδ
    hγ isPreconnected_Ici (show t₀ ∈ Ici t₀ by simp) ht₀ i ha
  have hbound : Real.exp (c * (t - t₀)) * A ≤ M := by
    simpa only [he] using hM (γ t) hmem haz
  have hlow : M / A + 1 ≤ c * (t - t₀) := by
    rw [mul_comm c]
    apply (div_le_iff₀ hc).mp
    have htime := (le_max_right t₀ (t₀ + (M / A + 1) / c)).trans ht
    linarith
  have hlowmul := mul_le_mul_of_nonneg_right hlow hA.le
  have hexp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c * (t - t₀))) hA.le
  have hcancel := div_mul_cancel₀ M (ne_of_gt hA)
  nlinarith

theorem not_isCompact_closure_forward_image {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici t₀))
    (i : S.Mutable) (ha : (γ t₀).a i = 0) (hb : (γ t₀).b i ≠ 0) :
    ¬ IsCompact (closure (γ '' Ici t₀)) := by
  intro hK
  obtain ⟨T, hT, hescape⟩ := eventually_not_mem_compact S hdet hε hκ hδ hγ i ha hb hK
  exact hescape T le_rfl (subset_closure ⟨T, hT, rfl⟩)

theorem partner_eq_zero_of_isCompact_closure {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici t₀))
    (hcompact : IsCompact (closure (γ '' Ici t₀)))
    (i : S.Mutable) (ha : (γ t₀).a i = 0) : (γ t₀).b i = 0 := by
  by_contra hb
  exact not_isCompact_closure_forward_image S hdet hε hκ hδ hγ i ha hb hcompact

/-- Conditional on a supplied native flow whose orbit solves exactly Z. -/
theorem partner_eq_zero_of_mem_trappedSet {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point) (p : S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici 0))
    (hp : p ∈ trappedSet flow) (i : S.Mutable) (ha : p.a i = 0) : p.b i = 0 := by
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
  simpa only [Flow.map_zero_apply] using
    partner_eq_zero_of_isCompact_closure S hdet hε hκ hδ hflow hcompact i
      (by simpa only [Flow.map_zero_apply] using ha)

theorem not_mem_trappedSet {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point) (p : S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici 0))
    (i : S.Mutable) (ha : p.a i = 0) (hb : p.b i ≠ 0) : p ∉ trappedSet flow :=
  fun hp => hb (partner_eq_zero_of_mem_trappedSet S hdet hε hκ hδ flow p hflow hp i ha)

end ClusterSkeleton.ZeroStratumEscape
