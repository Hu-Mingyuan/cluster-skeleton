import ClusterSkeleton.ConstructedFlowReverseInclusion

/-! Exact-source JOINT consumers. This file is checked after the unchanged accepted143
consumer bodies, which supply NativeFlowCapCompositionConsumer.liouvilleData and
CompactInteriorRigidityConsumer's literal point families. These are verification
declarations, not imported library theorems; no standalone-check claim is made. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.ConstructedFlowReverseInclusion

namespace ConstructedFlowReverseInclusionConsumer

section Generic
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)

/-- An arbitrary trapped point of the actual constructed flow lies in the cap. -/
theorem arbitrary_trapped_point (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow) :
    p ∈ coordinateCap S :=
  trappedSet_subset_coordinateCap S hdet hε hκ hδ hp

/-- The accepted LiouvilleData contains definitionally the same flow. -/
theorem package_flow_identity :
    (NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow =
      (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow := rfl

/-- The reverse inclusion holds for the actual accepted Liouville package. -/
theorem package_reverse_inclusion :
    trappedSet (NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow ⊆
      coordinateCap S :=
  trappedSet_subset_coordinateCap S hdet hε hκ hδ

/-- No nonzero-original restriction is smuggled into the zero-stratum case. -/
theorem zero_original (p : S.Point)
    (hp : p ∈ trappedSet (NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow)
    (i : S.Mutable) (ha : p.a i = 0) : normalizedPartner p i = 0 ∧ p.b i = 0 := by
  have hb := initially_zero_partner S hdet hε hκ hδ p hp i ha
  exact ⟨(ZeroStratumEscape.normalizedPartner_eq_zero_iff S i ha).mpr hb, hb⟩

/-- Other coordinates may already vanish when the selected original is nonzero. -/
theorem nonzero_interior (p : S.Point)
    (hp : p ∈ trappedSet (NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow)
    (i : S.Mutable) (ha : p.a i ≠ 0) (hr : ‖p.a i‖ < 1) :
    normalizedPartner p i = 0 ∧ p.b i = 0 :=
  initially_nonzero_interior_partners S hdet hε hκ hδ p hp i ha hr

/-- At a unit original, the product vanishes for every complex partner value. -/
theorem unit_boundary_unrestricted (p : S.Point) (i : S.Mutable)
    (hr : ‖p.a i‖ = 1) (b : ℂ) : ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * b = 0 := by
  simp [hr]

/-- Frozen phases are variables; trapped membership forces only their unit norm. -/
theorem frozen_unit (p : S.Point)
    (hp : p ∈ trappedSet (NativeFlowCapCompositionConsumer.liouvilleData S hdet hε hκ hδ).completeFlow.flow)
    (f : Fin d) (hf : f ∉ S.mutable) : p.a f ≠ 0 ∧ ‖p.a f‖ = 1 :=
  ⟨p.frozen_ne_zero f hf, (radial_and_frozen_restrictions S hdet hε hκ hδ p hp).2 f hf⟩

omit hε hκ hδ in
/-- Exact target witness, universally quantified over all admissible parameters. -/
theorem exact_target : ConstructedFlowReverseInclusionTarget S hdet :=
  constructedFlowReverseInclusionTarget S hdet
end Generic

open CompactInteriorRigidityConsumer

/-- One literal point simultaneously tests a nonzero strict-interior original and
an initially zero original with arbitrary input partner v. Both restrictions are
derived from trapped membership for the constructed flow. -/
theorem simultaneous_zero_and_nonzero {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    (r z v : ℂ) (hr : r ≠ 0) (hz : z ≠ 0) (hrlt : ‖r‖ < 1)
    (hp : simultaneousPoint r z v hr hz ∈ trappedSet
      (NativeCompleteFlow.completeFlow pairSeed pair_unimodular hε hκ hδ).flow) :
    z = -1 ∧ v = 0 := by
  have hzero := initially_zero_partner pairSeed pair_unimodular hε hκ hδ
    (simultaneousPoint r z v hr hz) hp ⟨2, by simp [pairSeed]⟩
    (by simp [simultaneousPoint, Seed.Point.a])
  have hnonzero := initially_nonzero_interior_partners pairSeed pair_unimodular
    hε hκ hδ (simultaneousPoint r z v hr hz) hp ⟨0, by simp [pairSeed]⟩
    (by simpa [simultaneousPoint, Seed.Point.a] using hr)
    (by simpa [simultaneousPoint, Seed.Point.a] using hrlt)
  have he : (z + 1) / r = 0 := by
    simpa [simultaneousPoint, Seed.Point.b] using hnonzero.2
  exact ⟨eq_neg_of_add_eq_zero_left ((div_eq_zero_iff.mp he).resolve_right hr),
    by simpa [simultaneousPoint, Seed.Point.b] using hzero⟩

/-- Independent nonzero frozen variables become unit and obey the exchange-product
restriction through the exact package flow; unit norms are not input premises. -/
theorem variable_frozen_family {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    (r u z w : ℂ) (hr : r ≠ 0) (hu : u ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hrlt : ‖r‖ < 1)
    (hp : phasePoint r u z w hr hu hz hw ∈ trappedSet
      (NativeFlowCapCompositionConsumer.liouvilleData phaseSeed phase_unimodular
        hε hκ hδ).completeFlow.flow) :
    ‖u‖ = 1 ∧ ‖z‖ = 1 ∧ ‖w‖ = 1 ∧ u * z * w = -1 := by
  have hcap := package_reverse_inclusion phaseSeed phase_unimodular hε hκ hδ hp
  have hb := coordinateCap_b_eq_zero hcap ⟨0, by simp [phaseSeed]⟩
    (by simpa [phasePoint, Seed.Point.a] using hrlt)
  have he : (u * z * w + 1) / r = 0 := by
    simpa [phasePoint, Seed.Point.b] using hb
  exact ⟨by simpa [phasePoint, Seed.Point.a] using hcap.1 1 (by simp [phaseSeed]),
    by simpa [phasePoint, Seed.Point.a] using hcap.1 2 (by simp [phaseSeed]),
    by simpa [phasePoint, Seed.Point.a] using hcap.1 3 (by simp [phaseSeed]),
    eq_neg_of_add_eq_zero_left ((div_eq_zero_iff.mp he).resolve_right hr)⟩

end ConstructedFlowReverseInclusionConsumer
