import ClusterSkeleton.FiniteTimeConfinement
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

/-! Source-matched consumers. Accepted fixture proof ranges are supplied verbatim
by the private combined checker; this file does not recreate those fixtures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.FiniteTimeConfinement

namespace FiniteTimeConfinementConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The same compact set works for both time signs and every shifted initial time. -/
theorem both_time_directions {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : Set S.Point, IsCompact K ∧
      ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
        (letI := SmoothAtlas.charts S hdet;
          IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
            (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
        IsOpen J → IsPreconnected J → t₀ ∈ J → γ t₀ = p →
        ∀ r : ℝ, |r| ≤ T → t₀-r ∈ J → t₀+r ∈ J →
          γ (t₀-r) ∈ K ∧ γ (t₀+r) ∈ K := by
  obtain ⟨K, hK, hb⟩ := finite_time_compact_confinement S hdet hε hκ hδ p T hT
  refine ⟨K, hK, fun γ J t₀ hγ ho hc hs hi r hr hm hp => ?_⟩
  constructor
  · apply hb γ J t₀ hγ ho hc hs hi (t₀-r) hm
    simpa only [sub_sub_cancel_left, abs_neg] using hr
  · apply hb γ J t₀ hγ ho hc hs hi (t₀+r) hp
    simpa only [add_sub_cancel_left] using hr

/-- Horizon 3 about time 7 covers the whole open interval (5,9), including
approach to both missing endpoints; no closed horizon lies inside this domain. -/
theorem omitted_endpoints {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) :
    ∃ K : Set S.Point, IsCompact K ∧ ∀ γ : ℝ → S.Point,
      (letI := SmoothAtlas.charts S hdet;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
          (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioo 5 9)) →
      γ 7 = p → γ '' Ioo 5 9 ⊆ K ∧
        closure (γ '' Ioo 5 9) ⊆ K ∧ IsCompact (closure (γ '' Ioo 5 9)) := by
  obtain ⟨K, hK, hb⟩ := finite_time_compact_confinement S hdet hε hκ hδ p 3 (by norm_num)
  refine ⟨K, hK, fun γ hγ hi => ?_⟩
  have him : γ '' Ioo 5 9 ⊆ K := by
    rintro q ⟨t, ht, rfl⟩
    exact hb γ (Ioo 5 9) 7 hγ isOpen_Ioo isPreconnected_Ioo (by norm_num) hi t ht
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hcl := closure_minimal him hK.isClosed
  exact ⟨him, hcl, hK.of_isClosed_subset isClosed_closure hcl⟩

/-- The excluded endpoints are a genuine feature of the consumer domain. -/
theorem closed_horizon_not_in_domain : ¬ Icc (7-3 : ℝ) (7+3) ⊆ Ioo 5 9 := by
  intro h
  have hh := h (show (5 : ℝ) ∈ Icc (7-3) (7+3) by norm_num)
  norm_num at hh

/-- Zero horizon is included in the native confinement theorem. -/
theorem zero_horizon {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) :
    ∃ K : Set S.Point, IsCompact K ∧
      ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
        (letI := SmoothAtlas.charts S hdet;
          IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
            (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
        IsOpen J → IsPreconnected J → t₀ ∈ J → γ t₀ = p →
        ∀ t ∈ J, |t-t₀| ≤ 0 → γ t ∈ K ∧ γ t = p := by
  obtain ⟨K, hK, hb⟩ := finite_time_compact_confinement S hdet hε hκ hδ p 0 le_rfl
  refine ⟨K, hK, fun γ J t₀ hγ ho hc hs hi t ht hz => ⟨hb γ J t₀ hγ ho hc hs hi t ht hz, ?_⟩⟩
  have he : t = t₀ := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
  simpa only [he] using hi

/-- Every point of the initial torus is covered, with no fixed coordinate values. -/
theorem torus_confinement {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (a : CoordinateTorus d) :
    (pointOfCoordinateTorus S a).zeroSet = ∅ ∧
    ∃ K : Set S.Point, IsCompact K ∧ ∀ γ : ℝ → S.Point,
      (letI := SmoothAtlas.charts S hdet;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
          (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioo 5 9)) →
      γ 7 = pointOfCoordinateTorus S a → γ '' Ioo 5 9 ⊆ K ∧
        closure (γ '' Ioo 5 9) ⊆ K ∧ IsCompact (closure (γ '' Ioo 5 9)) := by
  refine ⟨?_, omitted_endpoints S hdet hε hκ hδ _⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact (a j).property ((Seed.Point.mem_zeroSet _ _).mp hj).2

section Triple
open NativeRadialOrbitConsumer

/-- Two simultaneous zero coordinates have independent arbitrary original partners. -/
theorem simultaneous_zero_confinement {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x : ℝ) (u v : ℂ) :
    (triplePoint x u v).zeroSet = {2,4} ∧
    (triplePoint x u v).b ⟨2, by simp [tripleSeed]⟩ = u ∧
    (triplePoint x u v).b ⟨4, by simp [tripleSeed]⟩ = v ∧
    ∃ K : Set tripleSeed.Point, IsCompact K ∧ ∀ γ : ℝ → tripleSeed.Point,
      (letI := SmoothAtlas.charts tripleSeed triple_unimodular;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model 12)) γ
          (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) (Ioo 5 9)) →
      γ 7 = triplePoint x u v → γ '' Ioo 5 9 ⊆ K ∧
        closure (γ '' Ioo 5 9) ⊆ K ∧ IsCompact (closure (γ '' Ioo 5 9)) :=
  ⟨triple_zeroSet x u v, (triple_coordinates x u v).2.2.2.2.1,
    (triple_coordinates x u v).2.2.2.2.2,
    omitted_endpoints tripleSeed triple_unimodular hε hκ hδ _⟩

/-- The arbitrary partner parameters may both be zero. -/
theorem simultaneous_zero_partners {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x : ℝ) :
    ∃ K : Set tripleSeed.Point, IsCompact K ∧ ∀ γ : ℝ → tripleSeed.Point,
      (letI := SmoothAtlas.charts tripleSeed triple_unimodular;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model 12)) γ
          (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) (Ioo 5 9)) →
      γ 7 = triplePoint x 0 0 → γ '' Ioo 5 9 ⊆ K ∧
        closure (γ '' Ioo 5 9) ⊆ K ∧ IsCompact (closure (γ '' Ioo 5 9)) :=
  (simultaneous_zero_confinement hε hκ hδ x 0 0).2.2.2

/-- All original partners are bounded on the open interval, while the initially
nonzero coordinate has a strictly positive lower bound. -/
theorem triple_original_bounds {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x : ℝ) (u v : ℂ) :
    ∃ η A B : ℝ, 0 < η ∧ 0 ≤ A ∧ 0 ≤ B ∧ ∀ γ : ℝ → tripleSeed.Point,
      (letI := SmoothAtlas.charts tripleSeed triple_unimodular;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model 12)) γ
          (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) (Ioo 5 9)) →
      γ 7 = triplePoint x u v → ∀ t ∈ Ioo (5 : ℝ) 9,
        η ≤ ‖(γ t).a 0‖ ∧ (∀ j, ‖(γ t).a j‖ ≤ A) ∧
          (∀ i : tripleSeed.Mutable, ‖(γ t).b i‖ ≤ B) := by
  obtain ⟨η, A, B, hη, hA, hB, hb⟩ := uniform_original_bounds tripleSeed triple_unimodular
    hε hκ hδ (triplePoint x u v) 3 (by norm_num)
  refine ⟨η, A, B, hη, hA, hB, fun γ hγ hi t ht => ?_⟩
  obtain ⟨hz, ha, hlo, hp⟩ := hb γ (Ioo 5 9) 7 hγ isOpen_Ioo isPreconnected_Ioo
    (by norm_num) hi t ht (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact ⟨hlo 0 (triple_selected_nonzero x u v), ha, hp⟩
end Triple

section Partners
open ZeroStratumEscapeConsumer

/-- At a nonzero original index the denominator can vanish. The actual partner
is recovered from its exchange equation, not from that totalized quotient. -/
theorem nonzero_original_partner (w : ℂ) :
    (boundaryPoint w).a 1 = -1 ∧
    Examples.a2Seed.negativeMonomial (boundaryPoint w).a 1 = 0 ∧
    normalizedPartner (boundaryPoint w) ⟨1, by simp [Examples.a2Seed]⟩ = 0 ∧
    (boundaryPoint w).b ⟨1, by simp [Examples.a2Seed]⟩ =
      (Examples.a2Seed.positiveMonomial (boundaryPoint w).a 1 +
        Examples.a2Seed.negativeMonomial (boundaryPoint w).a 1) / (boundaryPoint w).a 1 ∧
    (boundaryPoint w).b ⟨1, by simp [Examples.a2Seed]⟩ = -1 := by
  refine ⟨(boundary_coordinates w).2.1, ?_, ?_, ?_, ?_⟩
  · simp [boundaryPoint, Seed.Point.a, Seed.negativeMonomial, Examples.a2Seed,
      Examples.a2Matrix, Fin.prod_univ_two]
  · simp [normalizedPartner, boundaryPoint, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]
  · exact CoordinateBounds.partner_eq_div Examples.a2Seed _
      (by simp [boundaryPoint, Seed.Point.a])
  · simp [boundaryPoint, Seed.Point.b]

/-- A nontrivial denominator at a zero original coordinate is retained in reconstruction. -/
theorem zero_original_partner (w : ℂ) :
    (reversedBoundary w).b ⟨1, by simp [Examples.a2Seed]⟩ =
      normalizedPartner (reversedBoundary w) ⟨1, by simp [Examples.a2Seed]⟩ *
        Examples.a2Seed.negativeMonomial (reversedBoundary w).a 1 := by
  exact CoordinateBounds.partner_eq_normalized_mul Examples.a2Seed _
    (by simp [reversedBoundary, Seed.Point.a])

/-- A frozen complex variable remains independently free beside a zero mutable coordinate. -/
theorem variable_frozen_confinement {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (w z : ℂ) (hz : z ≠ 0) :
    (variableFrozenBoundary w z hz).a 3 = z ∧
    ∃ K : Set pairSeed.Point, IsCompact K ∧ ∀ γ : ℝ → pairSeed.Point,
      (letI := SmoothAtlas.charts pairSeed pair_unimodular;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
          (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ioo 5 9)) →
      γ 7 = variableFrozenBoundary w z hz → γ '' Ioo 5 9 ⊆ K ∧
        closure (γ '' Ioo 5 9) ⊆ K ∧ IsCompact (closure (γ '' Ioo 5 9)) :=
  ⟨rfl, omitted_endpoints pairSeed pair_unimodular hε hκ hδ _⟩
end Partners

/-- When the mutable set is empty, every original variable has both bounds. -/
theorem empty_mutable_bounds (hM : S.mutable = ∅) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (T : ℝ) (hT : 0 ≤ T) :
    ∃ η A : ℝ, 0 < η ∧ 0 ≤ A ∧
      ∀ (γ : ℝ → S.Point) (J : Set ℝ) (t₀ : ℝ),
        (letI := SmoothAtlas.charts S hdet;
          IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
            (GlobalLiouvilleField.Z S hdet ε κ hδ) J) →
        IsOpen J → IsPreconnected J → t₀ ∈ J → γ t₀ = p →
        ∀ t ∈ J, |t-t₀| ≤ T → ∀ j, η ≤ ‖(γ t).a j‖ ∧ ‖(γ t).a j‖ ≤ A := by
  obtain ⟨η, A, B, hη, hA, hB, hb⟩ := uniform_original_bounds S hdet hε hκ hδ p T hT
  refine ⟨η, A, hη, hA, fun γ J t₀ hγ ho hc hs hi t ht hh j => ?_⟩
  have h := hb γ J t₀ hγ ho hc hs hi t ht hh
  exact ⟨h.2.2.1 j (p.frozen_ne_zero j (by simp [hM])), h.2.1 j⟩

section Frozen
open NativeRadialOrbitConsumer

/-- The two frozen moduli vary independently over all positive values. -/
theorem two_independent_frozen_variables {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x y : ℝ) :
    ‖(frozenPoint x y).a 0‖ = Real.exp x ∧ ‖(frozenPoint x y).a 1‖ = Real.exp y ∧
    ∃ K : Set frozenSeed.Point, IsCompact K ∧ ∀ γ : ℝ → frozenSeed.Point,
      (letI := SmoothAtlas.charts frozenSeed frozen_unimodular;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
          (GlobalLiouvilleField.Z frozenSeed frozen_unimodular ε κ hδ) (Ioo 5 9)) →
      γ 7 = frozenPoint x y → γ '' Ioo 5 9 ⊆ K ∧
        closure (γ '' Ioo 5 9) ⊆ K ∧ IsCompact (closure (γ '' Ioo 5 9)) :=
  ⟨(frozen_norms x y).1, (frozen_norms x y).2,
    omitted_endpoints frozenSeed frozen_unimodular hε hκ hδ _⟩

/-- A genuine native curve is supplied by the already proved identity flow in
dimension zero. The bounded-horizon closure theorem is applied to that curve. -/
theorem dimension_zero_native_application {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : emptySeed.Point) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : Set emptySeed.Point, IsCompact K ∧
      (∀ t : ℝ, |t-7| ≤ T → Flow.id ℝ emptySeed.Point t p ∈ K) ∧
      IsCompact (closure ((fun t => Flow.id ℝ emptySeed.Point t p) ''
        {t : ℝ | |t-7| ≤ T})) := by
  obtain ⟨K, hK, hb⟩ := bounded_horizon_closure emptySeed empty_unimodular hε hκ hδ p T hT
  have h := hb (fun t => Flow.id ℝ emptySeed.Point t p) univ 7
    (dimension_zero_flow_native ε κ hδ p) isOpen_univ isPreconnected_univ (mem_univ _) rfl
  refine ⟨K, hK, fun t ht => h.1 (subset_closure ?_), ?_⟩
  · exact ⟨t, ⟨mem_univ _, ht⟩, rfl⟩
  · simpa only [mem_univ, true_and] using h.2
end Frozen

end FiniteTimeConfinementConsumer

-- Native audit: unchanged accepted collectAxioms selection and traversal.
section
set_option maxHeartbeats 800000

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let before ← getEnv
    for (name, info) in before.constants.toList do
      let idx := before.getModuleIdxFor? name
      let fresh := idx.any fun i => #[`ClusterSkeleton.AllStrataGrowth, `ClusterSkeleton.FiniteTimeConfinement].contains before.header.moduleNames[i]!
      if fresh || idx.isNone then
        match info with
        | .defnInfo _ =>
          let _ ← Lean.Meta.getEqnsFor? name
          pure ()
        | _ => pure ()
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.NativeRadialOrbit.c, `NativeRadialOrbitConsumer.tripleSeed, `NativeRadialOrbitConsumer.triplePoint, `NativeRadialOrbitConsumer.frozenSeed, `NativeRadialOrbitConsumer.frozenPoint, `NativeRadialOrbitConsumer.emptySeed, `ClusterSkeleton.ScalarOrbitDynamics.RadialEquation, `ScalarOrbitDynamicsConsumer.frozenSeed, `ScalarOrbitDynamicsConsumer.variableFrozenPoint, `ClusterSkeleton.LocalAngularDynamics.maskedLogs, `ClusterSkeleton.LocalAngularDynamics.angularRhs, `ClusterSkeleton.LocalAngularDynamics.nu, `DynamicsCompositionConsumer.ZeroCurveLaws, `ZeroStratumEscapeConsumer.boundaryPoint,
        `ZeroStratumEscapeConsumer.reversedBoundary,
        `ZeroStratumEscapeConsumer.pairSeed,
        `ZeroStratumEscapeConsumer.frozenSeed,
        `ZeroStratumEscapeConsumer.frozenPoint,
        `ZeroStratumEscapeConsumer.emptySeed,
        `ZeroStratumEscapeConsumer.doubleBoundary,
        `ZeroStratumEscapeConsumer.variableFrozenBoundary,
        `ClusterSkeleton.BoundaryTangency.nodeProduct,
        `ClusterSkeleton.BoundaryTangency.drift,
        `ClusterSkeleton.BoundaryTangency.boundaryPerturb,
        `ClusterSkeleton.GlobalLiouvilleField.Z,
        `ClusterSkeleton.GlobalLiouvilleField.logarithmicComponents,
        `ClusterSkeleton.GlobalLiouvilleField.A,
        `ClusterSkeleton.GlobalLiouvilleField.L,
        `ClusterSkeleton.GlobalLiouvilleField.nonzeroLocus,
        `ClusterSkeleton.TorusLiouvilleDynamics.Z,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicComponents,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.angularTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.amplitude,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialCorrection,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicHamiltonian,
        `ClusterSkeleton.GlobalPrimitive.alpha,
        `ClusterSkeleton.PrimitiveCutoffs.angularRadius,
        `ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a,
        `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.LocalPrimitive.neighborhood,
        `ClusterSkeleton.LocalPrimitive.eta,
        `ClusterSkeleton.RegularCorrection.surviving,
        `ClusterSkeleton.RegularCorrection.regularH,
        `ClusterSkeleton.RegularCorrection.regularForm,
        `ClusterSkeleton.RegularCorrection.singularH,
        `ClusterSkeleton.LocalFormGluing.LocallySmooth,
        `ClusterSkeleton.LocalFormGluing.glue,
        `ClusterSkeleton.NativeNodePrimitive.nodeMap,
        `ClusterSkeleton.NativeNodePrimitive.locus,
        `ClusterSkeleton.NativeNodePrimitive.nodeDifferential,
        `ClusterSkeleton.NativeNodePrimitive.lambda,
        `ClusterSkeleton.NativeNodePrimitive.block,
        `ClusterSkeleton.PrimitiveResidual.tau,
        `ClusterSkeleton.PrimitiveResidual.logRow,
        `ClusterSkeleton.PrimitiveResidual.residual,
        `ClusterSkeleton.PrimitiveLocalization.rowLog,
        `ClusterSkeleton.PrimitiveLocalization.angle,
        `ClusterSkeleton.PrimitiveLocalization.nodeLog,
        `ClusterSkeleton.PrimitiveLocalization.correction,
        `ClusterSkeleton.PrimitiveLocalization.affineCorrection,
        `ClusterSkeleton.PrimitiveLocalization.region,
        `ClusterSkeleton.PrimitiveLocalization.neighborhood,
        `ClusterSkeleton.NodePrimitiveCancellation.L,
        `ClusterSkeleton.NodePrimitiveCancellation.A,
        `ClusterSkeleton.NodePrimitiveCancellation.S,
        `ClusterSkeleton.NodePrimitiveCancellation.T,
        `ClusterSkeleton.NodePrimitiveCancellation.du,
        `ClusterSkeleton.NodePrimitiveCancellation.dL,
        `ClusterSkeleton.NodePrimitiveCancellation.dtheta,
        `ClusterSkeleton.NodePrimitiveCancellation.lambda,
        `ClusterSkeleton.NodePrimitiveCancellation.oneForm] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize equations for {name}"
  let env ← getEnv
  let mut report : Array String := #[]
  for mod in env.header.moduleNames do
    report := report.push s!"IMPORT {mod}"
    let nativePath ← Lean.findOLean mod
    report := report.push s!"NATIVEPATH {mod}: {nativePath}"
  let required := #[`ClusterSkeleton.ZeroStratumEscape, `ClusterSkeleton.ZeroStratumPartnerDynamics, `ClusterSkeleton.ZeroStratumInvariance, `ClusterSkeleton.NormalizedPartnerNormDrift, `ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
    `ClusterSkeleton.TorusLiouvilleDynamics, `FsFltz.Geometry.SmoothLiouville,
    `FsFltz.Geometry.VectorFieldBridge, `ClusterSkeleton.GlobalPrimitive, `ClusterSkeleton.GlobalSymplectic,
    `ClusterSkeleton.LocalPrimitive, `ClusterSkeleton.RegularCorrection,
    `ClusterSkeleton.LocalFormGluing, `ClusterSkeleton.NativeNodePrimitive, `ClusterSkeleton.PrimitiveResidual,
    `ClusterSkeleton.TorusPrimitive, `ClusterSkeleton.NodePrimitiveCancellation,
    `ClusterSkeleton.PrimitiveLocalization, `ClusterSkeleton.PrimitiveCutoffs,
    `ClusterSkeleton.DominanceCutoff]
  for mod in required do
    unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  let mods := env.header.moduleNames.filter fun m => m.toString.startsWith "ClusterSkeleton." || m.toString.startsWith "FsFltz."
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  for name in supplements do
    unless env.contains name do throwError "Missing supplement {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut count := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => mods.contains env.header.moduleNames[i]!
    let named := name.toString.startsWith "ClusterSkeleton." ||
      name.toString.startsWith "_private.ClusterSkeleton." ||
      name.toString.startsWith "FsFltz." || name.toString.startsWith "_private.FsFltz."
    if defining || named || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      let origin := match idx with
        | some i => env.header.moduleNames[i]!.toString
        | none => "<consumer>"
      report := report.push s!"AUDITMODULE {name}: {origin}"
      report := report.push s!"AUDIT {name}: {axs}"
      logInfo m!"AUDIT {name}: {axs}"
      count := count + 1
  if count == 0 then throwError "Empty audit selection"
  report := report.push s!"AUDITED native combined/imported/local/supplement roots: {count}"
  let dir ← IO.getEnv "TMPDIR"
  let path := System.FilePath.mk (dir.getD "/tmp") / "finite-time-confinement136-joint-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"

end
