import ClusterSkeleton.NativeCompleteFlow
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

/-! Source-matched native consumers. The accepted fixture proof ranges are
inserted verbatim by the combined checker; this fragment does not redefine them. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.NativeCompleteFlow

namespace NativeCompleteFlowConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Destructure the proved witness and test its actual native ODE, its chart
ODE, joint smoothness, and the two-sided action laws on the literal carrier. -/
theorem constructed_flow_contract {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ∃ F : CompleteLiouvilleFlow (SmoothAtlas.presentation S hdet).manifold
        (GlobalLiouvilleField.Z S hdet ε κ hδ),
      (∀ p : S.Point, IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d)))
        (fun t => F.flow t p) (GlobalLiouvilleField.Z S hdet ε κ hδ)) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model (2*d)))) (𝓘(ℝ, Model (2*d))) ∞
        (fun q : ℝ × S.Point => F.flow q.1 q.2) ∧
      (∀ (p : S.Point) (t : ℝ) (a : S.Point),
        F.flow t p ∈ (chartAt (Model (2*d)) a).source →
        HasDerivAt (fun s : ℝ => chartAt (Model (2*d)) a (F.flow s p))
          ((SmoothAtlas.presentation S hdet).manifold.chartTangentMap a (F.flow t p)
            (GlobalLiouvilleField.Z S hdet ε κ hδ (F.flow t p))) t) ∧
      (∀ p : S.Point, F.flow 0 p = p) ∧
      (∀ (s t : ℝ) (p : S.Point), F.flow (s+t) p = F.flow s (F.flow t p)) ∧
      (∀ (t : ℝ) (p : S.Point),
        F.flow (-t) (F.flow t p) = p ∧ F.flow t (F.flow (-t) p) = p) := by
  letI := SmoothAtlas.charts S hdet
  obtain ⟨F⟩ := exists_completeLiouvilleFlow S hdet hε hκ hδ
  refine ⟨F, F.isMIntegralCurve, F.smooth_action, F.solves,
    F.flow.map_zero_apply, F.flow.map_add, ?_⟩
  intro t p
  constructor <;> simp only [← Flow.map_add, neg_add_cancel, add_neg_cancel,
    Flow.map_zero_apply]

/-- Arbitrary initial time, time zero, and both signs of every elapsed time
have actual native derivatives, without a supplied-flow assumption. -/
theorem shifted_native_both_signs {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (t₀ : ℝ) :
    letI := SmoothAtlas.charts S hdet
    ∃ γ : ℝ → S.Point, γ t₀ = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2*d)) γ 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (GlobalLiouvilleField.Z S hdet ε κ hδ (γ 0))) ∧
      ∀ r : ℝ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2*d)) γ (t₀-r)
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (GlobalLiouvilleField.Z S hdet ε κ hδ (γ (t₀-r)))) ∧
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2*d)) γ (t₀+r)
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (GlobalLiouvilleField.Z S hdet ε κ hδ (γ (t₀+r)))) := by
  letI := SmoothAtlas.charts S hdet
  obtain ⟨γ, hi, hγ⟩ := exists_global_integralCurve_through S hdet hε hκ hδ p t₀
  exact ⟨γ, hi, hγ, hγ 0, fun r => ⟨hγ (t₀-r), hγ (t₀+r)⟩⟩

/-- An arbitrary old curve on (5,9) is extended through its time-7 value.
Native derivatives at 5 and 9 belong to the extension; no old endpoint values
or old endpoint regularity are assumed. -/
theorem extension_across_omitted_endpoints {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioo 5 9))
    (hi : γ 7 = p) :
    letI := SmoothAtlas.charts S hdet
    ∃ Γ : ℝ → S.Point,
      IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) Γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) ∧
      EqOn Γ γ (Ioo 5 9) ∧ Γ 7 = p ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2*d)) Γ 5
        ((1 : ℝ →L[ℝ] ℝ).smulRight (GlobalLiouvilleField.Z S hdet ε κ hδ (Γ 5))) ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2*d)) Γ 9
        ((1 : ℝ →L[ℝ] ℝ).smulRight (GlobalLiouvilleField.Z S hdet ε κ hδ (Γ 9))) := by
  letI := SmoothAtlas.charts S hdet
  obtain ⟨Γ, hΓ, heq, hΓ₇⟩ := exists_extension_Ioo S hdet hε hκ hδ
    (show (7 : ℝ) ∈ Ioo 5 9 by norm_num) hγ
  exact ⟨Γ, hΓ, heq, hΓ₇.trans hi, hΓ 5, hΓ 9⟩

/-- Global existence also includes every initial-torus point without fixing
any original coordinate or frozen variable. -/
theorem initial_torus_global {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (a : CoordinateTorus d) (t₀ : ℝ) :
    (pointOfCoordinateTorus S a).zeroSet = ∅ ∧
    (letI := SmoothAtlas.charts S hdet
      ∃ γ : ℝ → S.Point, γ t₀ = pointOfCoordinateTorus S a ∧
        IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) γ
          (GlobalLiouvilleField.Z S hdet ε κ hδ)) := by
  refine ⟨?_, exists_global_integralCurve_through S hdet hε hκ hδ _ t₀⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact (a j).property ((Seed.Point.mem_zeroSet _ _).mp hj).2

section Triple
open NativeRadialOrbitConsumer

/-- Two simultaneous zeros and two independently arbitrary original partners
are exact initial data for one constructed all-real native curve. The same
two-coordinate zero stratum persists at every positive and negative time. -/
theorem simultaneous_zero_global {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x : ℝ) (u v : ℂ) (t₀ : ℝ) :
    (triplePoint x u v).zeroSet = {2,4} ∧
    (triplePoint x u v).b ⟨2, by simp [tripleSeed]⟩ = u ∧
    (triplePoint x u v).b ⟨4, by simp [tripleSeed]⟩ = v ∧
    (letI := SmoothAtlas.charts tripleSeed triple_unimodular
      ∃ γ : ℝ → tripleSeed.Point, γ t₀ = triplePoint x u v ∧
        IsMIntegralCurve (I := 𝓘(ℝ, Model 12)) γ
          (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) ∧
        ∀ t : ℝ, (γ t).zeroSet = {2,4}) := by
  refine ⟨triple_zeroSet x u v, (triple_coordinates x u v).2.2.2.2.1,
    (triple_coordinates x u v).2.2.2.2.2, ?_⟩
  letI := SmoothAtlas.charts tripleSeed triple_unimodular
  obtain ⟨γ, hi, hγ⟩ := exists_global_integralCurve_through tripleSeed triple_unimodular
    hε hκ hδ (triplePoint x u v) t₀
  refine ⟨γ, hi, hγ, fun t => ?_⟩
  have hz := ZeroStratumInvariance.zeroSet_eq tripleSeed triple_unimodular hε hκ hδ
    (hγ.isMIntegralCurveOn univ) isPreconnected_univ (mem_univ t) (mem_univ t₀)
  rw [hi, triple_zeroSet] at hz
  exact hz

/-- Both free partners may vanish simultaneously, including at initial time 7. -/
theorem simultaneous_zero_partners_global {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x : ℝ) :
    letI := SmoothAtlas.charts tripleSeed triple_unimodular
    ∃ γ : ℝ → tripleSeed.Point, γ 7 = triplePoint x 0 0 ∧
      IsMIntegralCurve (I := 𝓘(ℝ, Model 12)) γ
        (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) ∧
      ∀ t : ℝ, (γ t).zeroSet = {2,4} :=
  (simultaneous_zero_global hε hκ hδ x 0 0 7).2.2.2
end Triple

section Partners
open ZeroStratumEscapeConsumer

/-- The nonzero original coordinate a₁ has zero normalized denominator. The
actual global curve is still constructed, retaining its original partner. -/
theorem vanished_normalization_denominator_global {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (w : ℂ) :
    (boundaryPoint w).a 1 = -1 ∧
    Examples.a2Seed.negativeMonomial (boundaryPoint w).a 1 = 0 ∧
    normalizedPartner (boundaryPoint w) ⟨1, by simp [Examples.a2Seed]⟩ = 0 ∧
    (boundaryPoint w).b ⟨1, by simp [Examples.a2Seed]⟩ = -1 ∧
    (letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      ∃ γ : ℝ → Examples.a2Seed.Point, γ 7 = boundaryPoint w ∧
        IsMIntegralCurve (I := 𝓘(ℝ, Model 4)) γ
          (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ)) := by
  refine ⟨(boundary_coordinates w).2.1, ?_, ?_, ?_,
    exists_global_integralCurve_through Examples.a2Seed Examples.a2Seed_unimodular
      hε hκ hδ (boundaryPoint w) 7⟩
  · simp [boundaryPoint, Seed.Point.a, Seed.negativeMonomial, Examples.a2Seed,
      Examples.a2Matrix, Fin.prod_univ_two]
  · simp [normalizedPartner, boundaryPoint, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]
  · simp [boundaryPoint, Seed.Point.b]

/-- The frozen complex variable z remains arbitrary and nonzero beside a
mutable zero and its arbitrary original partner w. -/
theorem variable_frozen_boundary_global {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (w z : ℂ) (hz : z ≠ 0) (t₀ : ℝ) :
    (variableFrozenBoundary w z hz).a 0 = 0 ∧
    (variableFrozenBoundary w z hz).a 3 = z ∧
    (variableFrozenBoundary w z hz).b ⟨0, by simp [pairSeed]⟩ = w ∧
    (letI := SmoothAtlas.charts pairSeed pair_unimodular
      ∃ γ : ℝ → pairSeed.Point, γ t₀ = variableFrozenBoundary w z hz ∧
        IsMIntegralCurve (I := 𝓘(ℝ, Model 8)) γ
          (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ)) :=
  ⟨rfl, rfl, rfl, exists_global_integralCurve_through pairSeed pair_unimodular
    hε hκ hδ (variableFrozenBoundary w z hz) t₀⟩
end Partners

/-- Empty mutable scope still constructs a genuine global curve; all original
variables remain nonzero by the actual exchange carrier's frozen condition. -/
theorem empty_mutable_global (hM : S.mutable = ∅) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (t₀ : ℝ) :
    letI := SmoothAtlas.charts S hdet
    ∃ γ : ℝ → S.Point, γ t₀ = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) ∧
      ∀ (t : ℝ) (j : Fin d), (γ t).a j ≠ 0 := by
  letI := SmoothAtlas.charts S hdet
  obtain ⟨γ, hi, hγ⟩ := exists_global_integralCurve_through S hdet hε hκ hδ p t₀
  exact ⟨γ, hi, hγ, fun t j => (γ t).frozen_ne_zero j (by simp [hM])⟩

section Frozen
open NativeRadialOrbitConsumer

/-- Every pair of independently varying frozen moduli supplies exact initial
data for a native all-real curve, with no specialization to constants. -/
theorem independent_frozen_variables_global {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x y t₀ : ℝ) :
    ‖(frozenPoint x y).a 0‖ = Real.exp x ∧
    ‖(frozenPoint x y).a 1‖ = Real.exp y ∧
    (letI := SmoothAtlas.charts frozenSeed frozen_unimodular
      ∃ γ : ℝ → frozenSeed.Point, γ t₀ = frozenPoint x y ∧
        IsMIntegralCurve (I := 𝓘(ℝ, Model 4)) γ
          (GlobalLiouvilleField.Z frozenSeed frozen_unimodular ε κ hδ) ∧
        ∀ (t : ℝ) (j : Fin 2), (γ t).a j ≠ 0) :=
  ⟨(frozen_norms x y).1, (frozen_norms x y).2,
    empty_mutable_global frozenSeed frozen_unimodular rfl hε hκ hδ (frozenPoint x y) t₀⟩

/-- The chosen constructed flow is the identity in dimension zero because the
literal exchange-equation carrier is a subsingleton. Its native ODE is retained. -/
theorem dimension_zero_constructed_identity {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    letI := SmoothAtlas.charts emptySeed empty_unimodular
    let F := completeFlow emptySeed empty_unimodular hε hκ hδ
    F.flow = Flow.id ℝ emptySeed.Point ∧
      (∀ (t : ℝ) (p : emptySeed.Point), F.flow t p = p) ∧
      ∀ p : emptySeed.Point, IsMIntegralCurve (I := 𝓘(ℝ, Model 0))
        (fun t => F.flow t p) (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ) := by
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  letI : Subsingleton emptySeed.Point := ⟨fun p q => by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · funext i
      exact Fin.elim0 i.val⟩
  let F := completeFlow emptySeed empty_unimodular hε hκ hδ
  exact ⟨Flow.ext (fun _ _ => Subsingleton.elim _ _),
    fun _ _ => Subsingleton.elim _ _, F.isMIntegralCurve⟩
end Frozen

/-- Apply the accepted confinement theorem to the constructed global orbit on
univ, at arbitrary initial time and finite horizon. No all-time compactness
claim is made; the compact set may depend on T. -/
theorem constructed_orbit_finite_horizon {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (t₀ T : ℝ) (hT : 0 ≤ T) :
    let F := completeFlow S hdet hε hκ hδ
    ∃ K : Set S.Point, IsCompact K ∧
      (∀ t : ℝ, |t-t₀| ≤ T → F.flow (t-t₀) p ∈ K) ∧
      (∀ r : ℝ, |r| ≤ T → F.flow (-r) p ∈ K ∧ F.flow r p ∈ K) ∧
      closure ((fun t : ℝ => F.flow (t-t₀) p) '' {t : ℝ | |t-t₀| ≤ T}) ⊆ K ∧
      IsCompact (closure ((fun t : ℝ => F.flow (t-t₀) p) ''
        {t : ℝ | |t-t₀| ≤ T})) := by
  letI := SmoothAtlas.charts S hdet
  let F := completeFlow S hdet hε hκ hδ
  let γ : ℝ → S.Point := fun t => F.flow (t-t₀) p
  have hγ : IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) γ
      (GlobalLiouvilleField.Z S hdet ε κ hδ) :=
    isMIntegralCurve_comp_sub.mpr (F.isMIntegralCurve p)
  have hi : γ t₀ = p := by simp only [γ, sub_self, Flow.map_zero_apply]
  obtain ⟨K, hK, hb⟩ := FiniteTimeConfinement.finite_time_compact_confinement S hdet
    hε hκ hδ p T hT
  have htime : ∀ t : ℝ, |t-t₀| ≤ T → γ t ∈ K := fun t ht =>
    hb γ univ t₀ (hγ.isMIntegralCurveOn univ) isOpen_univ isPreconnected_univ
      (mem_univ _) hi t (mem_univ _) ht
  have hcl : closure (γ '' {t : ℝ | |t-t₀| ≤ T}) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    rintro q ⟨t, ht, rfl⟩
    exact htime t ht
  refine ⟨K, hK, htime, ?_, hcl, hK.of_isClosed_subset isClosed_closure hcl⟩
  intro r hr
  constructor
  · simpa only [γ, sub_sub_cancel_left] using htime (t₀-r)
      (by simpa only [sub_sub_cancel_left, abs_neg] using hr)
  · simpa only [γ, add_sub_cancel_left] using htime (t₀+r)
      (by simpa only [add_sub_cancel_left] using hr)

/-- The old radial restriction theorem now applies to a constructed flow.
The trapped set retains its original independent dynamical definition. -/
theorem constructed_flow_trapped_radial_restrictions {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {p : S.Point}
    (hp : p ∈ trappedSet (completeFlow S hdet hε hκ hδ).flow) :
    (∀ j : Fin d, ‖p.a j‖ ≤ 1) ∧
      (∀ j : Fin d, j ∉ S.mutable → ‖p.a j‖ = 1) := by
  letI := SmoothAtlas.charts S hdet
  let F := completeFlow S hdet hε hκ hδ
  exact NativeRadialOrbit.trapped_radial_restrictions S hdet hε hκ hδ F.flow
    (fun p => (F.isMIntegralCurve p).isMIntegralCurveOn univ) hp

end NativeCompleteFlowConsumer


-- Native audit: unchanged accepted collectAxioms selection and traversal.
section
set_option maxHeartbeats 800000

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let before ← getEnv
    for (name, info) in before.constants.toList do
      let idx := before.getModuleIdxFor? name
      let fresh := idx.any fun i => (#[`ClusterSkeleton.AllStrataGrowth, `ClusterSkeleton.FiniteTimeConfinement, `ClusterSkeleton.NativeCompleteFlow].contains before.header.moduleNames[i]! || before.header.moduleNames[i]!.toString.startsWith "FsFltz.")
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "native-complete-flow139-joint-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"

end
