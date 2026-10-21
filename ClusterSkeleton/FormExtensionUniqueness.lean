import ClusterSkeleton.SmoothAtlas
import ClusterSkeleton.InitialTorusDensity
import FsFltz.Geometry.FormCalculus

/-!
# Uniqueness of smooth forms from the initial torus

Density is applied to native chart coefficients, whose tangent arguments are
transported by the actual differential of the inverse chart. The native chart
reconstruction theorem then recovers equality in each dependent tangent fiber.
This proves uniqueness only; no extension, symplectic form, or primitive is
constructed here.
-/

noncomputable section

open scoped Manifold ContDiff
open Set
open FsFltz.Geometry
open FsFltz.Geometry.SmoothManifold

namespace ClusterSkeleton
namespace FormExtensionUniqueness

/-- Native smooth chart coefficients, composed with their chart, are continuous
on the chart source. The fixed codomain here is a space of alternating maps on
the model, not a silently identified family of tangent fibers. -/
theorem continuousOn_chartCoefficients {n k : ℕ} (M : SmoothManifold n)
    {omega : M.Form k} (h : M.IsSmoothForm omega) (a : M.Point) :
    ContinuousOn (fun p => M.formInChart a omega (chartAt (Model n) a p))
      (chartAt (Model n) a).source :=
  (h a).continuousOn.comp (chartAt (Model n) a).continuousOn
    (chartAt (Model n) a).mapsTo

/-- Smooth native forms of any degree are determined by their values on a dense
set. Continuity is used only after transport to a fixed native chart; the
proved differential cancellation restores the form in its original fiber. -/
theorem form_eq_of_dense {n k : ℕ} (M : SmoothManifold n)
    {s : Set M.Point} (hs : Dense s) {omega eta : M.Form k}
    (homega : M.IsSmoothForm omega) (heta : M.IsSmoothForm eta)
    (heq : ∀ p ∈ s, omega p = eta p) : omega = eta := by
  funext a
  let e := chartAt (Model n) a
  have hlocal : EqOn (fun p => M.formInChart a omega (e p))
      (fun p => M.formInChart a eta (e p)) (e.source ∩ s) := by
    intro p hp
    have hp' : e.symm (e p) ∈ s := by
      rw [e.left_inv hp.1]
      exact hp.2
    exact congrArg
      (fun f : M.Tangent (e.symm (e p)) [⋀^Fin k]→L[ℝ] ℝ =>
        f.compContinuousLinearMap (M.inverseChartTangentMap a (e p)))
      (heq _ hp')
  have hclosure : e.source ⊆ closure (e.source ∩ s) := by
    intro p hp
    exact e.open_source.inter_closure ⟨hp, hs p⟩
  have hcoeff := hlocal.of_subset_closure
    (continuousOn_chartCoefficients M homega a)
    (continuousOn_chartCoefficients M heta a) inter_subset_left hclosure
  have ha : a ∈ e.source := mem_chart_source (Model n) a
  have h := congrArg
    (fun f : Model n [⋀^Fin k]→L[ℝ] ℝ =>
      f.compContinuousLinearMap (M.chartTangentMap a a)) (hcoeff ha)
  exact (M.formInChart_comp_chartTangentMap omega a a ha).symm.trans
    (h.trans (M.formInChart_comp_chartTangentMap eta a a ha))

/-- Pairwise evaluation determines a native two-form in a single fiber. -/
theorem twoForm_fiber_ext {n : ℕ} (M : SmoothManifold n)
    {omega eta : M.Form 2} (p : M.Point)
    (h : ∀ v w : M.Tangent p, evalTwo omega p v w = evalTwo eta p v w) :
    omega p = eta p := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : ![v 0, v 1] = v := by
    funext i
    fin_cases i <;> rfl
  simpa only [evalTwo, hv] using h (v 0) (v 1)

/-- A reusable degree-two version with the usual two-vector evaluation
interface, applicable in particular to a later exterior-derivative comparison. -/
theorem twoForm_eq_of_dense {n : ℕ} (M : SmoothManifold n)
    {s : Set M.Point} (hs : Dense s) {omega eta : M.Form 2}
    (homega : M.IsSmoothForm omega) (heta : M.IsSmoothForm eta)
    (heq : ∀ p ∈ s, ∀ v w : M.Tangent p,
      evalTwo omega p v w = evalTwo eta p v w) : omega = eta :=
  form_eq_of_dense M hs homega heta fun p hp => twoForm_fiber_ext M p (heq p hp)

/-- Uniqueness on any smooth presentation of the actual exchange-point subtype.
The topology remains the inherited topology used by `dense_initialTorus`. -/
theorem twoForm_eq_of_initialTorus {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
    (P : SmoothPresentation S) {omega eta : P.manifold.Form 2}
    (homega : P.manifold.IsSmoothForm omega) (heta : P.manifold.IsSmoothForm eta)
    (heq : ∀ p ∈ initialTorus S, ∀ v w : P.manifold.Tangent p,
      evalTwo omega p v w = evalTwo eta p v w) : omega = eta :=
  twoForm_eq_of_dense P.manifold (dense_initialTorus S hdet) homega heta heq

/-- The concrete initial-torus extension-uniqueness bridge for the constructed
atlas. It requires only smoothness of the two forms and agreement on the torus,
and imposes no further restriction on the seed or its zero strata. -/
theorem smoothAtlas_twoForm_extension_unique {d : ℕ} (S : Seed d)
    (hdet : S.Unimodular)
    {omega eta : (SmoothAtlas.presentation S hdet).manifold.Form 2}
    (homega : (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm omega)
    (heta : (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm eta)
    (heq : ∀ p ∈ initialTorus S,
      ∀ v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p,
        evalTwo omega p v w = evalTwo eta p v w) : omega = eta :=
  twoForm_eq_of_initialTorus S hdet (SmoothAtlas.presentation S hdet) homega heta heq

end FormExtensionUniqueness
end ClusterSkeleton
