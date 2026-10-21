import ClusterSkeleton.ConstructedFlowCapInclusion

/-! Source-matched consumer fragment. The managed integrated fixture supplies
the unchanged accepted NativeFlowCapCompositionConsumer and
CapForwardInvarianceConsumer declarations before this body; see the interface.
Every orbit below is the constructed flow, with no supplied curve or ODE. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Manifold ContDiff Topology
open Set ClusterSkeleton FsFltz.Geometry

namespace ConstructedFlowCapInclusionConsumer

section Generic
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
local notation "F" => NativeCompleteFlow.completeFlow S hdet hε hκ hδ

/-- The native orbit is an all-real solution of exactly the prescribed field. -/
theorem actual_native_orbit (p : S.Point) :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) (fun t => (F).flow t p)
      (GlobalLiouvilleField.Z S hdet ε κ hδ) := by
  letI := SmoothAtlas.charts S hdet
  exact (F).isMIntegralCurve p

theorem one_initial_cap (p : S.Point) (hp : p ∈ coordinateCap S) {t : ℝ} (ht : 0 ≤ t) :
    (F).flow t p ∈ coordinateCap S :=
  ConstructedFlowCapInclusion.forward S hdet hε hκ hδ hp ht

/-- Simultaneous initially zero coordinates retain both partner equations. -/
theorem all_initial_zeros (p : S.Point) (hp : p ∈ coordinateCap S)
    (J : Set S.Mutable) (hJ : ∀ i ∈ J, p.a i = 0) {t : ℝ} (ht : 0 ≤ t) :
    (F).flow t p ∈ coordinateCap S ∧
      ∀ i ∈ J, ((F).flow t p).a i = 0 ∧ normalizedPartner ((F).flow t p) i = 0 ∧
        ((F).flow t p).b i = 0 := by
  refine ⟨one_initial_cap S hdet hε hκ hδ p hp ht, ?_⟩
  intro i hi
  simpa only [Flow.map_zero_apply, zero_add] using
    CapForwardInvariance.zero_forward S hdet hε hκ hδ (t₀ := 0) (η := 1)
      (by norm_num) (ConstructedFlowCapInclusion.integralCurveOn S hdet hε hκ hδ p)
      (by simpa only [Flow.map_zero_apply] using hp) i
      (by simpa only [Flow.map_zero_apply] using hJ i hi) ht

theorem nonzero_interior (p : S.Point) (hp : p ∈ coordinateCap S)
    (i : S.Mutable) (hi : p.a i ≠ 0) (hr : ‖p.a i‖ < 1) {t : ℝ} (ht : 0 ≤ t) :
    ((F).flow t p).a i ≠ 0 ∧ ‖((F).flow t p).a i‖ < 1 ∧
      normalizedPartner ((F).flow t p) i = 0 ∧ ((F).flow t p).b i = 0 := by
  simpa only [Flow.map_zero_apply, zero_add] using
    CapForwardInvariance.interior_forward S hdet hε hκ hδ (t₀ := 0) (η := 1)
      (by norm_num) (ConstructedFlowCapInclusion.integralCurveOn S hdet hε hκ hδ p)
      (by simpa only [Flow.map_zero_apply] using hp) i
      (by simpa only [Flow.map_zero_apply] using hi)
      (by simpa only [Flow.map_zero_apply] using hr) ht

/-- No vanishing premise is imposed on a unit-boundary partner. -/
theorem mutable_unit_boundary (p : S.Point) (hp : p ∈ coordinateCap S)
    (i : S.Mutable) (hi : ‖p.a i‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    (F).flow t p ∈ coordinateCap S ∧ ‖((F).flow t p).a i‖ = 1 := by
  refine ⟨one_initial_cap S hdet hε hκ hδ p hp ht, ?_⟩
  simpa only [Flow.map_zero_apply, zero_add] using
    InteriorPartnerPropagation.unit_norm_forward S hdet hε hκ hδ (t₀ := 0) (η := 1)
      (by norm_num) (ConstructedFlowCapInclusion.integralCurveOn S hdet hε hκ hδ p)
      i (by simpa only [Flow.map_zero_apply] using hi) ht

theorem frozen_unit (p : S.Point) (hp : p ∈ coordinateCap S)
    (f : Fin d) (hf : f ∉ S.mutable) {t : ℝ} (ht : 0 ≤ t) :
    ‖((F).flow t p).a f‖ = 1 :=
  (one_initial_cap S hdet hε hκ hδ p hp ht).1 f hf

theorem compact_forward_closure (p : S.Point) (hp : p ∈ coordinateCap S) :
    IsCompact (closure ((F).flow.forwardOrbit p)) :=
  ConstructedFlowCapInclusion.isCompact_forwardOrbit_closure S hdet hε hκ hδ hp

/-- This is the exact complete flow in the already accepted LiouvilleData. -/
theorem liouvilleData_cap_inclusion :
    coordinateCap S ⊆ trappedSet
      (NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow :=
  ConstructedFlowCapInclusion.subset_trappedSet S hdet hε hκ hδ

theorem liouvilleData_compact_forward_closure (p : S.Point) (hp : p ∈ coordinateCap S) :
    IsCompact (closure
      ((NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow.forwardOrbit p)) :=
  compact_forward_closure S hdet hε hκ hδ p hp

/-- The initial point at an arbitrary time is enough; no earlier cap history is used. -/
theorem shifted_initial_cap (p : S.Point) (t₀ : ℝ)
    (hp : (F).flow t₀ p ∈ coordinateCap S) {t : ℝ} (ht : 0 ≤ t) :
    (F).flow (t₀ + t) p ∈ coordinateCap S := by
  rw [add_comm t₀ t, Flow.map_add]
  exact one_initial_cap S hdet hε hκ hδ ((F).flow t₀ p) hp ht

end Generic

open CapForwardInvarianceConsumer

/-- This disk family includes zero, strict interior and unit boundary points,
with the other mutable coordinate on the unit circle. -/
theorem a2_disk_trapped {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    interiorPoint z ∈ trappedSet
      (NativeCompleteFlow.completeFlow Examples.a2Seed Examples.a2Seed_unimodular
        hε hκ hδ).flow :=
  ConstructedFlowCapInclusion.subset_trappedSet _ _ hε hκ hδ (interiorPoint_mem z hz)

theorem simultaneous_zero_trapped {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    simultaneousPoint z ∈ trappedSet
      (NativeCompleteFlow.completeFlow pairSeed pair_unimodular hε hκ hδ).flow :=
  ConstructedFlowCapInclusion.subset_trappedSet _ _ hε hκ hδ (simultaneousPoint_mem z hz)

/-- The two frozen phases are arbitrary independent unit complex numbers. -/
theorem independent_frozen_phases_trapped {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    (r z w : ℂ) (hr : ‖r‖ ≤ 1) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    phasePoint r z w hz hw ∈ trappedSet
      (NativeCompleteFlow.completeFlow phaseSeed phase_unimodular hε hκ hδ).flow :=
  ConstructedFlowCapInclusion.subset_trappedSet _ _ hε hκ hδ (phasePoint_mem r z w hr hz hw)

/-- The shallow collar is covered without an initial deep-radius assumption. -/
theorem shallow_collar_trapped {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) :
    interiorPoint (Real.exp (-ε) : ℂ) ∈ trappedSet
      (NativeCompleteFlow.completeFlow Examples.a2Seed Examples.a2Seed_unimodular
        hε hκ hδ).flow :=
  ConstructedFlowCapInclusion.subset_trappedSet _ _ hε hκ hδ (shallow_family_initial hε).1

theorem exact_target {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    ConstructedFlowCapInclusionTarget S hdet := constructedFlowCapInclusionTarget S hdet

end ConstructedFlowCapInclusionConsumer
