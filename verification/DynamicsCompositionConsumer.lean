import ClusterSkeleton.LocalAngularDynamics
import ClusterSkeleton.ZeroStratumEscape

/-! Private composition consumer. The source-matched checking context prepends the
unchanged accepted angular103 and escape109 consumer bodies (with their ordered
imports). Those contexts supply only the already proved example fixtures below.
The generic declarations use the literal exchange carrier and its inherited
topology, the accepted atlas, and exactly the accepted global Liouville field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry

namespace DynamicsCompositionConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- A conclusion about a supplied curve, not an assumption about its dynamics.
Every local complex assertion has its own pointwise neighborhood premise. -/
def ZeroCurveLaws (ε κ δ t₀ : ℝ) (γ : ℝ → S.Point) (i : S.Mutable) : Prop :=
  ∀ t ≥ t₀, (γ t).a i = 0 ∧ S.negativeMonomial (γ t).a i ≠ 0 ∧
    ((γ t).b i = 0 ↔ (γ t₀).b i = 0) ∧
    Complex.normSq (normalizedPartner (γ t) i) =
      Real.exp (2*(1+κ)*(t-t₀)) * Complex.normSq (normalizedPartner (γ t₀) i) ∧
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ t) i)) (Ici t₀) t ∧
    ∀ p : S.Point, (i : Fin d) ∈ p.zeroSet →
      γ t ∈ LocalPrimitive.neighborhood S ε κ δ p →
      HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
        ((1+(κ : ℂ)-Complex.I*(LocalAngularDynamics.nu S ε κ δ p (γ t) i : ℂ)) *
          normalizedPartner (γ t) i) (Ici t₀) t

/-- The same genuine native curve supplies the local complex equation and the
exact global norm law, deriving zero persistence and denominator facts. -/
theorem native_zero_dynamics {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici t₀))
    (i : S.Mutable) (ha : (γ t₀).a i = 0) :
    ZeroCurveLaws S ε κ δ t₀ γ i := by
  letI := SmoothAtlas.charts S hdet
  intro t ht
  have hs : t₀ ∈ Ici t₀ := by simp
  have haz := (ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ
    isPreconnected_Ici hs ht i).mp ha
  refine ⟨haz, ZeroStratumEscape.denominator_ne_zero S i haz, ?_,
    ZeroStratumPartnerDynamics.normSq_eq_exp_mul S hdet hε hκ hδ hγ
      isPreconnected_Ici hs ht i ha,
    ZeroStratumPartnerDynamics.normSq_hasDerivWithinAt S hdet hε hκ hδ hγ
      isPreconnected_Ici hs ht i ha, ?_⟩
  · exact (ZeroStratumEscape.normalizedPartner_eq_zero_iff S i haz).symm.trans
      ((ZeroStratumPartnerDynamics.partner_zero_iff S hdet hε hκ hδ hγ
        isPreconnected_Ici hs ht i ha).symm.trans
          (ZeroStratumEscape.normalizedPartner_eq_zero_iff S i ha))
  · intro p hi hq
    exact LocalAngularDynamics.partner_hasDerivWithinAt_zero S hdet hε hκ hδ
      p i hi hγ ht hq haz

/-- The field in the local complex differential is literally the field in the
native curve and in the escape theorem, on the accepted presentation. -/
theorem native_complex_differential {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    (p q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (ha : q.a i = 0) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) (fun r => normalizedPartner r i) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
      (1+(κ : ℂ)-Complex.I*(LocalAngularDynamics.nu S ε κ δ p q i : ℂ)) *
        normalizedPartner q i :=
  LocalAngularDynamics.partner_drift_zero S hdet hε hκ hδ p q hq i hi ha

/-- Original-partner nonvanishing is the honest escape premise. -/
theorem native_zero_escape {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici t₀))
    (i : S.Mutable) (ha : (γ t₀).a i = 0) (hb : (γ t₀).b i ≠ 0) :
    ZeroCurveLaws S ε κ δ t₀ γ i ∧
    (∀ K : Set S.Point, IsCompact K → ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K) ∧
    ¬ IsCompact (closure (γ '' Ici t₀)) :=
  ⟨native_zero_dynamics S hdet hε hκ hδ hδπ hγ i ha,
    fun K hK => ZeroStratumEscape.eventually_not_mem_compact S hdet hε hκ hδ hγ i ha hb hK,
    ZeroStratumEscape.not_isCompact_closure_forward_image S hdet hε hκ hδ hγ i ha hb⟩

/-- The zero original partner persists; no escape assertion is made for it. -/
theorem original_partner_zero_persistence {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici t₀))
    (i : S.Mutable) (ha : (γ t₀).a i = 0) (hb : (γ t₀).b i = 0) :
    ZeroCurveLaws S ε κ δ t₀ γ i ∧ ∀ t ≥ t₀, (γ t).b i = 0 := by
  have h := native_zero_dynamics S hdet hε hκ hδ hδπ hγ i ha
  exact ⟨h, fun t ht => (h t ht).2.2.1.mpr hb⟩

/-- Existing supplied native flow, existing trappedSet, exact-Z orbit premise. -/
theorem supplied_flow_joint_exclusion {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (flow : Flow ℝ S.Point) (p : S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici 0))
    (i : S.Mutable) (ha : p.a i = 0) (hb : p.b i ≠ 0) :
    ZeroCurveLaws S ε κ δ 0 (fun t => flow t p) i ∧ p ∉ trappedSet flow :=
  ⟨native_zero_dynamics S hdet hε hκ hδ hδπ hflow i
      (by simpa only [Flow.map_zero_apply] using ha),
    ZeroStratumEscape.not_mem_trappedSet S hdet hε hκ hδ flow p hflow i ha hb⟩

/-- The closed starting point is retained after an arbitrary time shift. -/
theorem shifted_closed_endpoint {ε κ δ s τ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici (s+τ)))
    (i : S.Mutable) (ha : (γ (s+τ)).a i = 0) (hb : (γ (s+τ)).b i ≠ 0) :
    ZeroCurveLaws S ε κ δ (s+τ) γ i ∧
    HasDerivWithinAt (fun t => normalizedPartner (γ t) i)
      ((1+(κ : ℂ)-Complex.I*
        (LocalAngularDynamics.nu S ε κ δ (γ (s+τ)) (γ (s+τ)) i : ℂ)) *
          normalizedPartner (γ (s+τ)) i) (Ici (s+τ)) (s+τ) ∧
    (∀ K : Set S.Point, IsCompact K → ∃ T ≥ s+τ, ∀ t ≥ T, γ t ∉ K) := by
  have h := native_zero_escape S hdet hε hκ hδ hδπ hγ i ha hb
  exact ⟨h.1, (h.1 (s+τ) le_rfl).2.2.2.2.2 (γ (s+τ))
    (((γ (s+τ)).mem_zeroSet i).mpr ⟨i.property, ha⟩)
    (LocalPrimitive.mem_neighborhood S ε κ hδ _), h.2.1⟩

/-- The literal coordinate inclusion retains the exchange subtype topology. -/
theorem literal_carrier_and_frozen (p : S.Point) :
    Continuous (fun q : S.Point => q.val) ∧
    (∀ i : S.Mutable, p.a i*p.b i = S.positiveMonomial p.a i+S.negativeMonomial p.a i) ∧
    ∀ f : Fin d, f ∉ S.mutable → p.a f ≠ 0 :=
  ⟨continuous_subtype_val, p.exchange, p.frozen_ne_zero⟩

/-! The following fixtures are supplied verbatim by the two accepted source-matched
consumer contexts. They do not add a replacement seed, partner, field or flow. -/
open ZeroStratumEscapeConsumer

theorem a2_joint (w : ℂ) {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    {γ : ℝ → Examples.a2Seed.Point}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ici t₀))
    (hstart : γ t₀ = boundaryPoint w) :
    ZeroCurveLaws Examples.a2Seed ε κ δ t₀ γ ⟨0, by simp [Examples.a2Seed]⟩ ∧
    (w = 0 → ∀ t ≥ t₀, (γ t).b ⟨0, by simp [Examples.a2Seed]⟩ = 0) ∧
    (w ≠ 0 → ∀ K : Set Examples.a2Seed.Point, IsCompact K → ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K) := by
  have ha : (γ t₀).a 0 = 0 := by rw [hstart]; rfl
  have hb : (γ t₀).b ⟨0, by simp [Examples.a2Seed]⟩ = w := by
    rw [hstart]; exact (boundary_coordinates w).2.2
  refine ⟨native_zero_dynamics _ Examples.a2Seed_unimodular hε hκ hδ hδπ hγ _ ha, ?_, ?_⟩
  · intro hw
    exact (original_partner_zero_persistence _ Examples.a2Seed_unimodular hε hκ hδ hδπ
      hγ _ ha (hb.trans hw)).2
  · intro hw
    exact (native_zero_escape _ Examples.a2Seed_unimodular hε hκ hδ hδπ hγ _ ha
      (fun hz => hw (hb.symm.trans hz))).2.1

theorem simultaneous_joint (v : ℂ) (hv : v ≠ 0) {ε κ δ t₀ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hδπ : δ < Real.pi)
    {γ : ℝ → pairSeed.Point}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ici t₀))
    (hstart : γ t₀ = doubleBoundary 0 v) :
    ZeroCurveLaws pairSeed ε κ δ t₀ γ ⟨0, by simp [pairSeed]⟩ ∧
    ZeroCurveLaws pairSeed ε κ δ t₀ γ ⟨2, by simp [pairSeed]⟩ ∧
    (∀ t ≥ t₀, (γ t).b ⟨0, by simp [pairSeed]⟩ = 0) ∧
    (∀ K : Set pairSeed.Point, IsCompact K → ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K) := by
  have ha0 : (γ t₀).a 0 = 0 := by rw [hstart]; rfl
  have ha2 : (γ t₀).a 2 = 0 := by rw [hstart]; rfl
  have hz : (γ t₀).b ⟨0, by simp [pairSeed]⟩ = 0 := by rw [hstart]; rfl
  have hn : (γ t₀).b ⟨2, by simp [pairSeed]⟩ ≠ 0 := by
    simpa [hstart, doubleBoundary, Seed.Point.b] using hv
  have h0 := original_partner_zero_persistence pairSeed pair_unimodular hε hκ hδ hδπ hγ _ ha0 hz
  have h2 := native_zero_escape pairSeed pair_unimodular hε hκ hδ hδπ hγ _ ha2 hn
  exact ⟨h0.1, h2.1, h0.2, h2.2.1⟩

theorem variable_frozen_joint (w z : ℂ) (hw : w ≠ 0) (hz : z ≠ 0)
    {ε κ δ t₀ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi) {γ : ℝ → pairSeed.Point}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ici t₀))
    (hstart : γ t₀ = variableFrozenBoundary w z hz) :
    (γ t₀).a 3 = z ∧ (∀ t : ℝ, (γ t).a 3 ≠ 0) ∧
    ZeroCurveLaws pairSeed ε κ δ t₀ γ ⟨0, by simp [pairSeed]⟩ ∧
    (∀ K : Set pairSeed.Point, IsCompact K → ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K) := by
  have h := variable_frozen_escape w z hw hz hε hκ hδ hγ hstart
  exact ⟨h.1, h.2.1,
    native_zero_dynamics pairSeed pair_unimodular hε hκ hδ hδπ hγ _ (by rw [hstart]; rfl),
    h.2.2.1⟩

theorem empty_mutable_joint (hM : S.mutable = ∅) (ε κ δ : ℝ) (p q : S.Point) :
    p.zeroSet = ∅ ∧ IsEmpty S.Mutable ∧ LocalAngularDynamics.nu S ε κ δ p q = 0 :=
  ⟨(empty_mutable_scope S hM p).1, (empty_mutable_scope S hM p).2,
    LocalAngularDynamicsConsumer.empty_mutable_nu S hM ε κ δ p q⟩

theorem dimension_zero_joint (ε κ t₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts emptySeed empty_unimodular
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model 0)) (fun _ : ℝ => emptySeed.unitPoint)
      (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ) (Ici t₀) ∧
    IsCompact (closure ((fun _ : ℝ => emptySeed.unitPoint) '' Ici t₀)) ∧
    IsEmpty emptySeed.Mutable ∧
    LocalAngularDynamics.nu emptySeed ε κ δ emptySeed.unitPoint emptySeed.unitPoint = 0 := by
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  have h := dimension_zero_compact_forward ε κ t₀ hδ
  exact ⟨h.1, h.2.1, h.2.2,
    LocalAngularDynamicsConsumer.empty_mutable_nu emptySeed rfl ε κ δ _ _⟩

/-- Reuse the accepted A4 fixture with its proved nonzero surviving correction;
combine it with exact norm dynamics and compact escape for that same seed/field. -/
theorem a4_nonzero_correction_joint (w : ℂ) (hw : w ≠ 0) {t₀ : ℝ}
    {γ : ℝ → LocalAngularDynamicsConsumer.a4Seed.Point}
    (hγ : letI := SmoothAtlas.charts LocalAngularDynamicsConsumer.a4Seed LocalAngularDynamicsConsumer.a4_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z LocalAngularDynamicsConsumer.a4Seed
          LocalAngularDynamicsConsumer.a4_unimodular 1 3
          (by positivity : 0 < Real.pi/2)) (Ici t₀))
    (hstart : γ t₀ = LocalAngularDynamicsConsumer.a4Boundary w (-5) (Real.pi/8)) :
    let p := LocalAngularDynamicsConsumer.a4Boundary w (-5) (Real.pi/8)
    p.zeroSet = {0} ∧
    LocalAngularDynamicsConsumer.a4v2 ∈ RegularCorrection.surviving
      LocalAngularDynamicsConsumer.a4Seed p.zeroSet ∧
    PrimitiveLocalization.correction 1 3 (Real.pi/2) LocalAngularDynamicsConsumer.a4v2 p ≠ 0 ∧
    ZeroCurveLaws LocalAngularDynamicsConsumer.a4Seed 1 3 (Real.pi/2) t₀ γ
      LocalAngularDynamicsConsumer.a4v0 ∧
    HasDerivWithinAt (fun t => normalizedPartner (γ t) LocalAngularDynamicsConsumer.a4v0)
      ((1+(3 : ℂ)-Complex.I*
        (LocalAngularDynamics.nu LocalAngularDynamicsConsumer.a4Seed 1 3 (Real.pi/2) p p 0 : ℂ))*w)
      (Ici t₀) t₀ ∧
    (∀ K : Set LocalAngularDynamicsConsumer.a4Seed.Point, IsCompact K →
      ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K) := by
  have hfix := LocalAngularDynamicsConsumer.a4_nonvacuous w
  let p := LocalAngularDynamicsConsumer.a4Boundary w (-5) (Real.pi/8)
  have ha : (γ t₀).a LocalAngularDynamicsConsumer.a4v0 = 0 := by rw [hstart]; rfl
  have hb : (γ t₀).b LocalAngularDynamicsConsumer.a4v0 ≠ 0 := by
    rw [hstart]
    exact hw
  have h := native_zero_escape LocalAngularDynamicsConsumer.a4Seed
    LocalAngularDynamicsConsumer.a4_unimodular (by norm_num : (0:ℝ)<1)
    (by norm_num : (2:ℝ)*1+1≤3) (by positivity : 0 < Real.pi/2)
    (by linarith [Real.pi_pos] : Real.pi/2 < Real.pi) hγ _ ha hb
  refine ⟨hfix.1, hfix.2.1, hfix.2.2.2, h.1, ?_, h.2.1⟩
  have hd := (h.1 t₀ le_rfl).2.2.2.2.2 p
    (by rw [LocalAngularDynamicsConsumer.a4_zeroSet]; exact Finset.mem_singleton_self 0)
    (by simpa only [hstart] using hfix.2.2.1)
  simpa only [hstart, p, LocalAngularDynamicsConsumer.a4_partner, Complex.ofReal_ofNat,
    show (LocalAngularDynamicsConsumer.a4v0 : Fin 4) = 0 from rfl] using hd

end DynamicsCompositionConsumer
