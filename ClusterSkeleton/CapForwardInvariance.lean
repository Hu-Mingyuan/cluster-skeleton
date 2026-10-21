import ClusterSkeleton.InteriorPartnerPropagation
import ClusterSkeleton.ZeroStratumEscape

/-! Forward preservation of the independently defined coordinate cap along any
native integral curve of the actual global Liouville field. Only the initial
point is assumed to lie in the cap. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry

namespace ClusterSkeleton.CapForwardInvariance

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ t₀ η : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
  (hδ : 0 < δ) (hη : 0 < η) {γ : ℝ → S.Point}
  (hγ : letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))

include hε hκ hδ hη hγ

/-- On an initially zero original coordinate, both native zero-persistence
theorems apply. The nonvanishing exchange denominator recovers the actual partner. -/
theorem zero_forward (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
    (hi : (γ t₀).a i = 0) {t : ℝ} (ht : 0 ≤ t) :
    (γ (t₀+t)).a i = 0 ∧ normalizedPartner (γ (t₀+t)) i = 0 ∧
      (γ (t₀+t)).b i = 0 := by
  have hs : t₀ ∈ Ioi (t₀ - η) := by change t₀ - η < t₀; linarith
  have hu : t₀+t ∈ Ioi (t₀ - η) := by change t₀ - η < t₀+t; linarith
  have ha := (ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ
    isPreconnected_Ioi hs hu i).mp hi
  have hb₀ := CapAngularTangency.normalizedPartner_eq_zero_of_interior S hp i
    (show ‖(γ t₀).a i‖ < 1 by simp [hi])
  have hb := (ZeroStratumPartnerDynamics.partner_zero_iff S hdet hε hκ hδ hγ
    isPreconnected_Ioi hs hu i hi).mp hb₀
  exact ⟨ha, hb, (ZeroStratumEscape.normalizedPartner_eq_zero_iff S i ha).mp hb⟩

/-- A nonzero strict-interior original remains strictly inside the unit disk.
The accepted partner theorem supplies the actual partner without a radius cutoff. -/
theorem interior_forward (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1) {t : ℝ} (ht : 0 ≤ t) :
    (γ (t₀+t)).a i ≠ 0 ∧ ‖(γ (t₀+t)).a i‖ < 1 ∧
      normalizedPartner (γ (t₀+t)) i = 0 ∧ (γ (t₀+t)).b i = 0 := by
  have hn := NativeRadialOrbit.coordinate_ne_zero S hdet hε hκ hδ hη hγ i hi
    (show t₀ - η < t₀+t by linarith)
  have hlog : GlobalLiouvilleField.A S (γ t₀) i < 0 :=
    Real.log_neg (norm_pos_iff.mpr hi) hr
  have hl := (NativeRadialOrbit.negative_log_laws S hdet hε hκ hδ hη hγ i hi hlog).2.1 t ht
  have hlt : ‖(γ (t₀+t)).a i‖ < 1 :=
    (Real.log_neg_iff (norm_pos_iff.mpr hn)).mp hl
  exact ⟨hn, hlt,
    (InteriorPartnerPropagation.propagate S hdet hε hκ hδ hη hγ hp i hi hr ht).2⟩

/-- The mutable cap product follows in all three initial cases. Unit-boundary
partners have no vanishing premise or conclusion. -/
theorem mutable_constraints_forward (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(γ (t₀+t)).a i‖ ≤ 1 ∧
      ((1 - ‖(γ (t₀+t)).a i‖ ^ 2 : ℝ) : ℂ) * (γ (t₀+t)).b i = 0 := by
  by_cases hi : (γ t₀).a i = 0
  · obtain ⟨ha, _, hb⟩ := zero_forward S hdet hε hκ hδ hη hγ hp i hi ht
    simp [ha, hb]
  · rcases lt_or_eq_of_le (hp.2 i).1 with hr | hr
    · obtain ⟨_, hlt, _, hb⟩ := interior_forward S hdet hε hκ hδ hη hγ hp i hi hr ht
      exact ⟨hlt.le, by simp [hb]⟩
    · have hu := InteriorPartnerPropagation.unit_norm_forward S hdet hε hκ hδ hη hγ i hr ht
      simp [hu]

/-- Frozen coordinates retain unit norm, with arbitrary initial phases and
their native evolution. Frozen variables are never specialized in the seed. -/
theorem frozen_norm_forward (hp : γ t₀ ∈ coordinateCap S) (f : Fin d)
    (hf : f ∉ S.mutable) {t : ℝ} (ht : 0 ≤ t) : ‖(γ (t₀+t)).a f‖ = 1 :=
  InteriorPartnerPropagation.unit_norm_forward S hdet hε hκ hδ hη hγ f (hp.1 f hf) ht

/-- Full literal cap membership at every forward time, from one initial cap point. -/
theorem forward (hp : γ t₀ ∈ coordinateCap S) {t : ℝ} (ht : 0 ≤ t) :
    γ (t₀+t) ∈ coordinateCap S :=
  ⟨fun f hf => frozen_norm_forward S hdet hε hκ hδ hη hγ hp f hf ht,
    fun i => mutable_constraints_forward S hdet hε hκ hδ hη hγ hp i ht⟩

end ClusterSkeleton.CapForwardInvariance

namespace ClusterSkeleton

/-- The complete forward-invariance target, separate from its proof. -/
def CoordinateCapForwardInvarianceTarget
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
    ∀ t ≥ 0, γ (t₀ + t) ∈ coordinateCap S

theorem coordinateCapForwardInvarianceTarget {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    CoordinateCapForwardInvarianceTarget S hdet := by
  intro ε κ δ t₀ η hε hκ hδ hη γ hγ hp t ht
  exact CapForwardInvariance.forward S hdet hε hκ hδ hη hγ hp ht

end ClusterSkeleton
