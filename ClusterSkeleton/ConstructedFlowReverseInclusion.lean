import ClusterSkeleton.NativeCompleteFlow
import ClusterSkeleton.CompactInteriorRigidity
import ClusterSkeleton.ZeroStratumEscape

/-! The reverse cap inclusion for the actual constructed complete flow, including
initially zero originals. Compactness is obtained from trapped membership. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry

namespace ClusterSkeleton.ConstructedFlowReverseInclusion

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)

/-- The forward-image compactness premise of rigidity follows from the independently
defined trapped set of this same constructed flow. -/
theorem compact_forward_image (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow) :
    IsCompact (closure ((fun t =>
      (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow t p) '' Ici 0)) := by
  let F := NativeCompleteFlow.completeFlow S hdet hε hκ hδ
  have horbit : (fun t => F.flow t p) '' Ici 0 = F.flow.forwardOrbit p := by
    rw [F.flow.forwardOrbit_eq_range_nonneg]
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, rfl⟩
  change IsCompact (closure ((fun t => F.flow t p) '' Ici 0))
  rw [horbit]
  exact hp

/-- Radial escape bounds all originals; compact accumulation and nonvanishing of
the variable frozen coordinates force their norms to be one. -/
theorem radial_and_frozen_restrictions (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow) :
    (∀ j : Fin d, ‖p.a j‖ ≤ 1) ∧
      (∀ f : Fin d, f ∉ S.mutable → ‖p.a f‖ = 1) := by
  letI := SmoothAtlas.charts S hdet
  let F := NativeCompleteFlow.completeFlow S hdet hε hκ hδ
  have hγ := (F.isMIntegralCurve p).isMIntegralCurveOn (Ioi (0 - 1 : ℝ))
  have hK := compact_forward_image S hdet hε hκ hδ p hp
  constructor
  · intro j
    simpa only [Flow.map_zero_apply] using
      CompactInteriorRigidity.original_norm_le_one S hdet hε hκ hδ
        (show (0 : ℝ) < 1 by norm_num) hγ hK j
  · intro f hf
    simpa only [Flow.map_zero_apply] using
      CompactInteriorRigidity.frozen_norm_eq_one S hdet hε hκ hδ
        (show (0 : ℝ) < 1 by norm_num) hγ hK f hf

/-- Initially zero originals use the accepted zero-stratum partner-growth escape
theorem with the native ODE of the constructed flow. -/
theorem initially_zero_partner (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow)
    (i : S.Mutable) (ha : p.a i = 0) : p.b i = 0 := by
  letI := SmoothAtlas.charts S hdet
  let F := NativeCompleteFlow.completeFlow S hdet hε hκ hδ
  exact ZeroStratumEscape.partner_eq_zero_of_mem_trappedSet S hdet hε hκ hδ
    F.flow p ((F.isMIntegralCurve p).isMIntegralCurveOn (Ici 0)) hp i ha

/-- Initially nonzero strict-interior originals use compact-orbit angular rigidity
and backward propagation; no angular or whole-orbit hypothesis is supplied. -/
theorem initially_nonzero_interior_partners (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow)
    (i : S.Mutable) (ha : p.a i ≠ 0) (hr : ‖p.a i‖ < 1) :
    normalizedPartner p i = 0 ∧ p.b i = 0 := by
  letI := SmoothAtlas.charts S hdet
  let F := NativeCompleteFlow.completeFlow S hdet hε hκ hδ
  have hγ := (F.isMIntegralCurve p).isMIntegralCurveOn (Ioi (0 - 1 : ℝ))
  have hK := compact_forward_image S hdet hε hκ hδ p hp
  simpa only [Flow.map_zero_apply] using
    CompactInteriorRigidity.initial_partners_zero S hdet hε hκ hδ
      (show (0 : ℝ) < 1 by norm_num) hγ hK i
      (by simpa only [Flow.map_zero_apply] using ha)
      (by simpa only [Flow.map_zero_apply] using hr)

/-- Every strict-interior mutable partner vanishes, with no initial nonzero premise. -/
theorem interior_partner (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow)
    (i : S.Mutable) (hr : ‖p.a i‖ < 1) : p.b i = 0 := by
  by_cases ha : p.a i = 0
  · exact initially_zero_partner S hdet hε hκ hδ p hp i ha
  · exact (initially_nonzero_interior_partners S hdet hε hκ hδ p hp i ha hr).2

/-- The mutable cap product imposes no partner restriction at the unit boundary. -/
theorem mutable_cap_product (p : S.Point)
    (hp : p ∈ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow)
    (i : S.Mutable) : ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0 := by
  by_cases hr : ‖p.a i‖ = 1
  · simp [hr]
  · have hlt : ‖p.a i‖ < 1 := lt_of_le_of_ne
      ((radial_and_frozen_restrictions S hdet hε hκ hδ p hp).1 i) hr
    rw [interior_partner S hdet hε hκ hδ p hp i hlt, mul_zero]

/-- Literal trapped-to-cap inclusion for the constructed native complete flow. -/
theorem trappedSet_subset_coordinateCap :
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow ⊆
      coordinateCap S := by
  intro p hp
  have hrestr := radial_and_frozen_restrictions S hdet hε hκ hδ p hp
  exact ⟨hrestr.2, fun i =>
    ⟨hrestr.1 i, mutable_cap_product S hdet hε hκ hδ p hp i⟩⟩

end ClusterSkeleton.ConstructedFlowReverseInclusion

namespace ClusterSkeleton

/-- The exact reverse-inclusion target, separate from its witness. -/
def ConstructedFlowReverseInclusionTarget {d : ℕ} (S : Seed d)
    (hdet : S.Unimodular) : Prop :=
  ∀ {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ),
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow ⊆ coordinateCap S

/-- Checked witness of the unaltered target, with no supplied dynamics premise. -/
theorem constructedFlowReverseInclusionTarget {d : ℕ} (S : Seed d)
    (hdet : S.Unimodular) : ConstructedFlowReverseInclusionTarget S hdet := by
  intro ε κ δ hε hκ hδ
  exact ConstructedFlowReverseInclusion.trappedSet_subset_coordinateCap S hdet hε hκ hδ

end ClusterSkeleton
