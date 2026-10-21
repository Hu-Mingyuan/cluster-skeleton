import ClusterSkeleton.NativeCompleteFlow
import ClusterSkeleton.CapAngularTangency

/-! Composition of the accepted complete flow and pointwise cap tangency.
The independent cap and trapped set definitions are unchanged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
open scoped Manifold ContDiff Topology
open Set ClusterSkeleton FsFltz.Geometry

namespace NativeFlowCapCompositionConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- All fields of the original LiouvilleData interface are constructed using
the accepted primitive, its exact vector field and its proved complete flow. -/
def liouvilleData {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) : LiouvilleData (SmoothAtlas.presentation S hdet) where
  primitive := GlobalPrimitive.alpha S hdet ε κ hδ
  smooth_primitive := GlobalPrimitive.isSmoothForm_alpha S hdet hε hκ hδ
  symplectic := GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha S hdet hε hκ hδ
  field := GlobalLiouvilleField.Z S hdet ε κ hδ
  smooth_field := GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ
  contraction := GlobalLiouvilleField.contraction_exteriorDerivative S hdet hε hκ hδ
  completeFlow := NativeCompleteFlow.completeFlow S hdet hε hκ hδ

/-- The constructed package is anchored to the prescribed torus two-form. -/
theorem torus_anchor {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S)
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

/-- At any cap time on the constructed all-real orbit, every unit original
coordinate has zero actual derivative. No whole-orbit cap premise is used. -/
theorem unit_coordinate_at_cap_time {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (t : ℝ)
    (hp : (liouvilleData S hdet hε hκ hδ).completeFlow.flow t p ∈ coordinateCap S)
    (j : Fin d)
    (hj : ‖((liouvilleData S hdet hε hκ hδ).completeFlow.flow t p).a j‖ = 1) :
    HasDerivAt
      (fun u => ((liouvilleData S hdet hε hκ hδ).completeFlow.flow u p).a j) 0 t := by
  letI := SmoothAtlas.charts S hdet
  let F := (liouvilleData S hdet hε hκ hδ).completeFlow
  have hγ := (F.isMIntegralCurve p).isMIntegralCurveOn (Set.univ : Set ℝ)
  exact (CapAngularTangency.coordinate_hasDerivWithinAt_zero S hdet hε hκ hδ
    hγ (Set.mem_univ t) hp j hj).hasDerivAt Filter.univ_mem

/-- In particular the conclusion holds at the initial cap point, including
arbitrary frozen unit coordinates and mutable boundary coordinates. -/
theorem initial_unit_coordinate {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (hp : p ∈ coordinateCap S) (j : Fin d) (hj : ‖p.a j‖ = 1) :
    HasDerivAt
      (fun u => ((liouvilleData S hdet hε hκ hδ).completeFlow.flow u p).a j) 0 0 := by
  apply unit_coordinate_at_cap_time S hdet hε hκ hδ p 0
  · simpa only [Flow.map_zero_apply] using hp
  · simpa only [Flow.map_zero_apply] using hj

end NativeFlowCapCompositionConsumer
