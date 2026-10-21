import ClusterSkeleton.NativeCompleteFlow
import ClusterSkeleton.CapForwardInvariance
import ClusterSkeleton.TrappedSet

/-! The coordinate cap is forward invariant and trapped for the constructed
complete native flow of the same global Liouville field. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry

namespace ClusterSkeleton.ConstructedFlowCapInclusion

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)

/-- Restrict the actual all-real orbit to the interval used by the accepted
cap theorem. The vector field and native atlas are exactly the constructed ones. -/
theorem integralCurveOn (p : S.Point) :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d)))
      (fun t => (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow t p)
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (0 - 1)) := by
  letI := SmoothAtlas.charts S hdet
  exact ((NativeCompleteFlow.completeFlow S hdet hε hκ hδ).isMIntegralCurve p).isMIntegralCurveOn _

/-- One initial cap membership suffices for all forward times, including zero. -/
theorem forward {p : S.Point} (hp : p ∈ coordinateCap S) {t : ℝ} (ht : 0 ≤ t) :
    (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow t p ∈ coordinateCap S := by
  have hinit : (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow 0 p ∈
      coordinateCap S := by simpa only [Flow.map_zero_apply] using hp
  simpa only [zero_add] using CapForwardInvariance.forward S hdet hε hκ hδ
    (t₀ := 0) (η := 1) (by norm_num) (integralCurveOn S hdet hε hκ hδ p) hinit ht

/-- Native forward invariance of the independently defined cap for this flow. -/
theorem isForwardInvariant :
    IsForwardInvariant (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow
      (coordinateCap S) := by
  intro t ht p hp
  exact forward S hdet hε hκ hδ hp ht

/-- Compactness in the inherited topology turns the proved forward invariance
into the literal inclusion in the independently defined dynamical trapped set. -/
theorem subset_trappedSet :
    coordinateCap S ⊆ trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow :=
  subset_trappedSet_of_isCompact_forwardInvariant _ (isCompact_coordinateCap S)
    (isForwardInvariant S hdet hε hκ hδ)

/-- The closure of the actual full forward orbit is compact. -/
theorem isCompact_forwardOrbit_closure {p : S.Point} (hp : p ∈ coordinateCap S) :
    IsCompact (closure
      ((NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow.forwardOrbit p)) :=
  subset_trappedSet S hdet hε hκ hδ hp

end ClusterSkeleton.ConstructedFlowCapInclusion

namespace ClusterSkeleton

/-- Exact constructed-flow cap inclusion target, separate from its witness. -/
def ConstructedFlowCapInclusionTarget
    {d : ℕ} (S : Seed d) (hdet : S.Unimodular) : Prop :=
  ∀ {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ),
    coordinateCap S ⊆
      trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow

theorem constructedFlowCapInclusionTarget {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    ConstructedFlowCapInclusionTarget S hdet := by
  intro ε κ δ hε hκ hδ
  exact ConstructedFlowCapInclusion.subset_trappedSet S hdet hε hκ hδ

end ClusterSkeleton
