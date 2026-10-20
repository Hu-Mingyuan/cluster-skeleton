import ClusterSkeleton.CapSet
import ClusterSkeleton.CoordinateLoci
import ClusterSkeleton.TrappedSet
import FsFltz.Geometry.Liouville

/-!
# The first cluster Liouville target

This file specifies, but does not prove, the first geometric target from
Theorem 2.1 of `acyclic_cluster_HMS.pdf`.

The point type and its topology are fixed by the actual complex exchange
coordinates. A presentation must make the actual inclusion a smooth immersion;
an arbitrary manifold and a bare point equivalence are not accepted.

The differential form and flow interfaces are the pinned FsFltz definitions,
which use native Mathlib tangent spaces, `mfderiv`, `extDeriv`, and `Flow`.
The torus equality below fixes the differential form to the imaginary part of
the manuscript's logarithmic form. Holomorphic extension is a separate target.
-/

noncomputable section

open scoped Manifold ContDiff BigOperators
open Set
open FsFltz.Geometry
open FsFltz.Geometry.SmoothManifold

namespace ClusterSkeleton

variable {d : ℕ}

/-- A smooth structure on the fixed coordinate subtype, compatible with its
native ambient inclusion. Constructing this presentation is an output
obligation, eventually discharged by the integral node charts. -/
structure SmoothPresentation (S : Seed d) where
  charts : ChartedSpace (Model (2 * d)) S.Point
  smooth : @IsManifold ℝ _ (Model (2 * d)) _ _ (Model (2 * d)) _
    (𝓘(ℝ, Model (2 * d))) ∞ S.Point inferInstance charts
  inclusion_smooth :
    letI := charts
    ContMDiff (𝓘(ℝ, Model (2 * d)))
      (𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ))) ∞
      (fun p : S.Point => p.val)
  inclusion_immersion :
    letI := charts
    ∀ p : S.Point, Function.Injective
      (mfderiv (𝓘(ℝ, Model (2 * d)))
        (𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ)))
        (fun q : S.Point => q.val) p)

namespace SmoothPresentation

/-- Packaging the already fixed point type and subspace topology for FsFltz.
There is deliberately no freely chosen point type or point equivalence. -/
def manifold {S : Seed d} (P : SmoothPresentation S) : SmoothManifold (2 * d) where
  Point := S.Point
  topology := inferInstance
  charts := P.charts
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := P.smooth

/-- The derivative of an actual ambient cluster coordinate. -/
def coordinateDifferential {S : Seed d} (P : SmoothPresentation S)
    (j : Fin d) (p : S.Point) :
    letI := P.charts
    P.manifold.Tangent p →L[ℝ] ℂ := by
  letI := P.charts
  exact mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, ℂ))
    (fun q : S.Point => q.a j) p

/-- Evaluation of Im(1/2 Σ Bᵢⱼ dlog(aᵢ) ∧ dlog(aⱼ)).
Only its restriction to `initialTorus` is used in the target. -/
def logarithmicImaginaryValue {S : Seed d} (P : SmoothPresentation S)
    (p : S.Point) (v w : P.manifold.Tangent p) : ℝ :=
  ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d,
    (S.B i j : ℂ) *
      ((P.coordinateDifferential i p v / p.a i) *
        (P.coordinateDifferential j p w / p.a j) -
       (P.coordinateDifferential i p w / p.a i) *
        (P.coordinateDifferential j p v / p.a j))).im

end SmoothPresentation

/-- Liouville witnesses on the fixed cluster presentation.
All of these fields must be constructed; this structure is not an assumption
in any theorem claiming existence of the cluster Liouville structure. -/
structure LiouvilleData {S : Seed d} (P : SmoothPresentation S) where
  primitive : P.manifold.Form 1
  smooth_primitive : P.manifold.IsSmoothForm primitive
  symplectic : P.manifold.IsSymplecticOn
    (P.manifold.exteriorDerivative primitive) Set.univ
  field : (p : S.Point) → P.manifold.Tangent p
  smooth_field : P.manifold.IsSmoothVectorField field
  contraction : ∀ p v,
    evalTwo (P.manifold.exteriorDerivative primitive) p (field p) v =
      evalOne primitive p v
  completeFlow : CompleteLiouvilleFlow P.manifold field

/-- The fixed-carrier witnesses directly form a pinned FsFltz complete
Liouville manifold. This preserves the very same primitive, field, and flow;
there is no point equivalence or transport to another carrier. -/
def LiouvilleData.toCompleteLiouvilleManifold {S : Seed d}
    {P : SmoothPresentation S} (L : LiouvilleData P) :
    CompleteLiouvilleManifold (2 * d) where
  manifold := P.manifold
  primitive := L.primitive
  smooth_primitive := L.smooth_primitive
  symplectic := L.symplectic
  field := L.field
  smooth_field := L.smooth_field
  contraction := L.contraction
  completeFlow := L.completeFlow

/-- The specified flow field is the unique vector determined by the primitive. -/
theorem LiouvilleData.field_eq_liouvilleVector {S : Seed d}
    {P : SmoothPresentation S} (L : LiouvilleData P) (p : S.Point) :
    L.field p = P.manifold.liouvilleVector L.primitive p :=
  (P.manifold.liouvilleVector_eq L.primitive p
    (L.symplectic.2.2 p (Set.mem_univ p)) (L.contraction p)).symm

/-- The first-stage target: a compatible manifold presentation, a smooth
Liouville primitive with its actual complete flow, and literal equality of the
full dynamical skeleton with the independent coordinate cap set.

Density and agreement on the torus anchor the globally extended real two-form
without assuming a holomorphic extension as an input. This is a proposition
definition, not a proved existence theorem. -/
def LiouvilleSkeletonTarget (S : Seed d) : Prop :=
  Dense (initialTorus S) ∧
  ∃ (P : SmoothPresentation S) (L : LiouvilleData P),
    (∀ (p : S.Point), p ∈ initialTorus S → ∀ v w,
      evalTwo (P.manifold.exteriorDerivative L.primitive) p v w =
        P.logarithmicImaginaryValue p v w) ∧
    trappedSet L.completeFlow.flow = coordinateCap S

/-- The general first-stage statement. No theorem of this type is asserted here. -/
def FirstGeometricTarget : Prop :=
  ∀ (d : ℕ) (S : Seed d), S.Unimodular → LiouvilleSkeletonTarget S

end ClusterSkeleton
