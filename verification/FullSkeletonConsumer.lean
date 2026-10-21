import ClusterSkeleton.FullSkeleton

/-! Consumers of the actual full-skeleton equality and the unchanged target. -/
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set ClusterSkeleton FsFltz.Geometry

namespace FullSkeletonConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)

/-- Compact closure is characterized by the independent coordinate equations. -/
theorem compact_forward_iff_cap (p : S.Point) :
    IsCompact (closure
      ((FullSkeleton.liouvilleData S hdet hε hκ hδ).completeFlow.flow.forwardOrbit p)) ↔
      p ∈ coordinateCap S := by
  change p ∈ trappedSet (FullSkeleton.liouvilleData S hdet hε hκ hδ).completeFlow.flow ↔ _
  rw [FullSkeleton.liouvilleData_trappedSet S hdet hε hκ hδ]

/-- Frozen unit norms and the mutable cap products are precisely the condition;
there is no choice of frozen coordinate values or restriction on unit partners. -/
theorem compact_forward_iff_coordinates (p : S.Point) :
    IsCompact (closure
      ((FullSkeleton.liouvilleData S hdet hε hκ hδ).completeFlow.flow.forwardOrbit p)) ↔
      (∀ f : Fin d, f ∉ S.mutable → ‖p.a f‖ = 1) ∧
        ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧
          ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0 :=
  compact_forward_iff_cap S hdet hε hκ hδ p

/-- The equality also applies at initially zero original coordinates. -/
theorem initially_zero_partner (p : S.Point)
    (hp : IsCompact (closure
      ((FullSkeleton.liouvilleData S hdet hε hκ hδ).completeFlow.flow.forwardOrbit p)))
    (i : S.Mutable) (ha : p.a i = 0) : p.b i = 0 := by
  have hcap := (compact_forward_iff_coordinates S hdet hε hκ hδ p).mp hp
  simpa [ha] using (hcap.2 i).2

/-- A cap point stays in the full skeleton at every forward time on this flow. -/
theorem forward_cap_is_trapped {p : S.Point} (hp : p ∈ coordinateCap S)
    {t : ℝ} (ht : 0 ≤ t) :
    (FullSkeleton.liouvilleData S hdet hε hκ hδ).completeFlow.flow t p ∈
      trappedSet (FullSkeleton.liouvilleData S hdet hε hκ hδ).completeFlow.flow := by
  rw [FullSkeleton.liouvilleData_trappedSet S hdet hε hκ hδ]
  exact ConstructedFlowCapInclusion.forward S hdet hε hκ hδ hp ht

/-- Conversion to the pinned FsFltz complete manifold preserves this skeleton. -/
theorem complete_manifold_skeleton :
    trappedSet (FullSkeleton.liouvilleData S hdet hε hκ hδ).toCompleteLiouvilleManifold.completeFlow.flow =
      coordinateCap S :=
  FullSkeleton.liouvilleData_trappedSet S hdet hε hκ hδ

include hdet in
/-- The result inhabits the original target with no dynamics assumptions. -/
theorem original_target : LiouvilleSkeletonTarget S :=
  FullSkeleton.liouvilleSkeletonTarget S hdet

theorem original_general_target : FirstGeometricTarget :=
  FullSkeleton.firstGeometricTarget

end FullSkeletonConsumer
