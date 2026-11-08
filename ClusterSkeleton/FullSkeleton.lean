import ClusterSkeleton.CapStrata
import ClusterSkeleton.ConstructedFlowCapInclusion
import ClusterSkeleton.ConstructedFlowReverseInclusion

/-!
# The complete Liouville structure and its full skeleton

The two accepted inclusions concern the same constructed native complete flow.
Their equality supplies the last field of the unchanged first geometric target.
The carrier, inherited topology, coordinate cap, and dynamical trapped set are
the original definitions. Frozen coordinates remain nonzero variables.
-/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry

namespace ClusterSkeleton.FullSkeleton

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)

/-- Equality of the independent dynamical and coordinate sets for the actual
constructed flow, without a supplied flow or either inclusion as a premise. -/
theorem trappedSet_eq_coordinateCap :
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow =
      coordinateCap S :=
  Set.Subset.antisymm
    (ConstructedFlowReverseInclusion.trappedSet_subset_coordinateCap S hdet hε hκ hδ)
    (ConstructedFlowCapInclusion.subset_trappedSet S hdet hε hκ hδ)

/-- The reference's stratified form of the skeleton identity: the dynamical
trapped set of the same constructed flow is the union of the strata `Λ_I` over
the independent subsets of the mutable vertices. -/
theorem trappedSet_eq_iUnion_lambdaStratum :
    trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val :=
  (trappedSet_eq_coordinateCap S hdet hε hκ hδ).trans
    (coordinateCap_eq_iUnion_lambdaStratum S)

/-- Construct all the original Liouville data using the accepted global
primitive, its actual vector field, and this very same complete flow. -/
def liouvilleData : LiouvilleData (SmoothAtlas.presentation S hdet) where
  primitive := GlobalPrimitive.alpha S hdet ε κ hδ
  smooth_primitive := GlobalPrimitive.isSmoothForm_alpha S hdet hε hκ hδ
  symplectic := GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha S hdet hε hκ hδ
  field := GlobalLiouvilleField.Z S hdet ε κ hδ
  smooth_field := GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ
  contraction := GlobalLiouvilleField.contraction_exteriorDerivative S hdet hε hκ hδ
  completeFlow := NativeCompleteFlow.completeFlow S hdet hε hκ hδ

/-- Packaging preserves the actual native flow on the literal point type. -/
theorem liouvilleData_flow :
    (liouvilleData S hdet hε hκ hδ).completeFlow.flow =
      (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow := rfl

/-- The actual exterior derivative has the prescribed logarithmic value on
the initial torus. No holomorphic extension is assumed. -/
theorem torus_anchor (p : S.Point) (hp : p ∈ initialTorus S)
    (v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (liouvilleData S hdet hε hκ hδ).primitive) p v w =
      (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p v w := by
  change SmoothManifold.evalTwo
    ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (GlobalPrimitive.alpha S hdet ε κ hδ)) p v w = _
  rw [GlobalPrimitive.exteriorDerivative_alpha S hdet hε hκ hδ]
  exact GlobalTwoForm.omega_torus S hdet p hp v w

/-- The constructed Liouville package has exactly the coordinate cap as its
full dynamical skeleton. -/
theorem liouvilleData_trappedSet :
    trappedSet (liouvilleData S hdet hε hκ hδ).completeFlow.flow = coordinateCap S :=
  trappedSet_eq_coordinateCap S hdet hε hκ hδ

include hdet hε hκ hδ in
/-- Witness the original target with any admissible construction parameters. -/
theorem liouvilleSkeletonTarget_of_parameters : LiouvilleSkeletonTarget S := by
  refine ⟨dense_initialTorus S hdet, SmoothAtlas.presentation S hdet,
    liouvilleData S hdet hε hκ hδ, ?_, liouvilleData_trappedSet S hdet hε hκ hδ⟩
  exact torus_anchor S hdet hε hκ hδ

include hdet in
/-- A uniform witness of the unchanged target. The chosen constants are
auxiliary cutoff parameters, not values of any frozen coordinate. -/
theorem liouvilleSkeletonTarget : LiouvilleSkeletonTarget S :=
  liouvilleSkeletonTarget_of_parameters S hdet
    (ε := 1) (κ := 3) (δ := 1) (by norm_num) (by norm_num) (by norm_num)

/-- The original general first geometric target, with all witnesses constructed. -/
theorem firstGeometricTarget : FirstGeometricTarget := by
  intro d S hdet
  exact liouvilleSkeletonTarget S hdet

end ClusterSkeleton.FullSkeleton
