import ClusterSkeleton.FullSkeleton
import ClusterSkeleton.SkewSeedSkeleton
import ClusterSkeleton.Examples.NonSkewSkeleton

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

/-! ## The genuinely non-skew input

Consumers of the same universal theorem at the concrete skew-symmetrizable but
not skew-symmetric seed of Section 4 of `target-theorem.pdf`. Nothing here is a
specialized construction: every witness comes from `FullSkeleton`, applied to
`Examples.nonSkewSeed`. The quantified statement `original_general_target`
above is not replaced. -/

namespace NonSkewConsumer

open ClusterSkeleton.Examples

variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)

/-- The target holds for the weighted seed that the old library cannot express:
`E 0 1 = 1` while `E 1 0 = -2`, with weights `diag(1,2,1,2)`. -/
theorem non_skew_target : LiouvilleSkeletonTarget nonSkewSeed :=
  nonSkewSeed_liouvilleSkeletonTarget

/-- The weights genuinely matter: the exchange matrix of this seed is not
skew-symmetric, so the recovered old theorem does not cover it. -/
theorem non_skew_not_skew : ¬ ∀ i j, nonSkewSeed.E i j = -nonSkewSeed.E j i :=
  nonSkewSeed_not_skew

/-- The compact-forward-orbit characterization at the non-skew seed: relative
compactness of the forward orbit is exactly the coordinate cap condition. -/
theorem non_skew_compact_forward_iff_cap (p : nonSkewSeed.Point) :
    IsCompact (closure
      ((FullSkeleton.liouvilleData nonSkewSeed nonSkewSeed_unimodular
        hε hκ hδ).completeFlow.flow.forwardOrbit p)) ↔
      p ∈ coordinateCap nonSkewSeed :=
  FullSkeletonConsumer.compact_forward_iff_cap nonSkewSeed
    nonSkewSeed_unimodular hε hκ hδ p

/-- The same characterization in explicit coordinates: unit norms at the frozen
vertices `2, 3` and the cap products at the mutable vertices `0, 1`. -/
theorem non_skew_compact_forward_iff_coordinates (p : nonSkewSeed.Point) :
    IsCompact (closure
      ((FullSkeleton.liouvilleData nonSkewSeed nonSkewSeed_unimodular
        hε hκ hδ).completeFlow.flow.forwardOrbit p)) ↔
      (∀ f : Fin 4, f ∉ nonSkewSeed.mutable → ‖p.a f‖ = 1) ∧
        ∀ i : nonSkewSeed.Mutable, ‖p.a i‖ ≤ 1 ∧
          ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0 :=
  FullSkeletonConsumer.compact_forward_iff_coordinates nonSkewSeed
    nonSkewSeed_unimodular hε hκ hδ p

/-- The skeleton of the constructed flow of this seed, in stratified form. -/
theorem non_skew_skeleton_iUnion :
    trappedSet (FullSkeleton.liouvilleData nonSkewSeed nonSkewSeed_unimodular
        hε hκ hδ).completeFlow.flow =
      ⋃ I : {I : Finset (Fin 4) // nonSkewSeed.Independent I},
        lambdaStratum nonSkewSeed I.val :=
  nonSkewSeed_trappedSet_iUnion hε hκ hδ

end NonSkewConsumer

/-! ## Recovery of the old `D = I` theorem

Consumers of `ClusterSkeleton.SkewSeed.skeleton_recovery`: the old
skew-symmetric input keeps its geometry, on its own carrier, with the form
written in the old integer matrix. -/

namespace RecoveryConsumer

open ClusterSkeleton.SkewSeed

variable {d : ℕ} (S : SkewSeed d) (hdet : S.Unimodular)

include hdet in
/-- The recovered package: density of the old torus, and one presentation and
Liouville datum carrying the old-matrix torus anchor and both forms of the old
skeleton identity on the old carrier. -/
theorem old_recovery :
    Dense (ClusterSkeleton.SkewSeed.initialTorus S) ∧
    ∃ (P : SmoothPresentation S.toSeed) (L : LiouvilleData P),
      (∀ p : (S.toSeed).Point, p ∈ ClusterSkeleton.initialTorus S.toSeed → ∀ v w,
          SmoothManifold.evalTwo
            (P.manifold.exteriorDerivative L.primitive) p v w =
            ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
              ((P.coordinateDifferential i p v / p.a i) *
                (P.coordinateDifferential j p w / p.a j) -
               (P.coordinateDifferential i p w / p.a i) *
                (P.coordinateDifferential j p v / p.a j))).im) ∧
      trappedSet (conjFlow S L.completeFlow.flow) =
        ClusterSkeleton.SkewSeed.coordinateCap S ∧
      trappedSet (conjFlow S L.completeFlow.flow) =
        ⋃ I : {I : Finset (Fin d) // S.Independent I},
          ClusterSkeleton.SkewSeed.lambdaStratum S I.val :=
  skeleton_recovery S hdet

include hdet in
/-- The old skeleton is compact, as in the old library: it is the old
coordinate cap. -/
theorem old_skeleton_isCompact :
    ∃ (P : SmoothPresentation S.toSeed) (L : LiouvilleData P),
      IsCompact (trappedSet (conjFlow S L.completeFlow.flow)) := by
  obtain ⟨-, P, L, -, hcap, -⟩ := skeleton_recovery S hdet
  exact ⟨P, L, hcap ▸ isCompact_coordinateCap S⟩

include hdet in
/-- The weighted target is available for the old input as well. -/
theorem old_weighted_target : LiouvilleSkeletonTarget S.toSeed :=
  ClusterSkeleton.SkewSeed.liouvilleSkeletonTarget S hdet

end RecoveryConsumer
