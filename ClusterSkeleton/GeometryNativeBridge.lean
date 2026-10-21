import ClusterSkeleton.GeometryTarget
import FsFltz.Geometry.FlowBridge
import Mathlib.Geometry.Manifold.ImmersionDiff

/-!
# Native manifold interfaces for the cluster target

This draft connects the existing fixed-carrier target to Mathlib's immersion,
tangent-bundle section, and integral-curve definitions. It neither constructs
the cluster smooth structure nor proves the Liouville existence target.

All statements concern the same coordinate subtype, primitive, vector field,
and flow already present in `GeometryTarget`.
-/

noncomputable section

open scoped Manifold ContDiff
open FsFltz.Geometry
open FsFltz.Geometry.SmoothManifold

namespace ClusterSkeleton

variable {d : ℕ} {S : Seed d}

namespace SmoothPresentation

/-- The existing ambient derivative condition is precisely the native
differential immersion condition in this finite-dimensional ambient space. -/
theorem inclusion_isDiffImmersionAt_iff (P : SmoothPresentation S) (p : S.Point) :
    letI := P.charts
    IsDiffImmersionAt (𝓘(ℝ, Model (2 * d)))
        (𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ)))
        (fun q : S.Point => q.val) p ↔
      Function.Injective
        (mfderiv (𝓘(ℝ, Model (2 * d)))
          (𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ)))
          (fun q : S.Point => q.val) p) := by
  letI := P.charts
  exact ⟨IsDiffImmersionAt.mfderiv_injective,
    IsDiffImmersionAt.of_injective_of_finiteDimensional⟩

/-- The actual coordinate inclusion is a Mathlib differential immersion.
This does not assert the stronger chart-normal-form immersion theorem, whose
converse from an injective derivative is not yet available in pinned Mathlib. -/
theorem inclusion_isDiffImmersionAt (P : SmoothPresentation S) (p : S.Point) :
    letI := P.charts
    IsDiffImmersionAt (𝓘(ℝ, Model (2 * d)))
      (𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ)))
      (fun q : S.Point => q.val) p := by
  letI := P.charts
  exact (P.inclusion_isDiffImmersionAt_iff p).mpr (P.inclusion_immersion p)

end SmoothPresentation

namespace LiouvilleData

variable {P : SmoothPresentation S}

/-- The field in the Liouville witness is smooth as a section of Mathlib's
actual tangent bundle, with no replacement or transport of tangent spaces. -/
theorem field_contMDiff_section (L : LiouvilleData P) :
    letI := P.charts
    letI := P.smooth
    ContMDiff (𝓘(ℝ, Model (2 * d)))
      ((𝓘(ℝ, Model (2 * d))).prod (𝓘(ℝ, Model (2 * d)))) ∞
      (fun p => (⟨p, L.field p⟩ :
        TangentBundle (𝓘(ℝ, Model (2 * d))) S.Point)) := by
  letI := P.charts
  letI := P.smooth
  exact L.smooth_field.contMDiff_section

/-- Every orbit of the same all-real-time flow is a native manifold integral
curve of the field determined by the Liouville contraction equation. -/
theorem isMIntegralCurve (L : LiouvilleData P) (p : S.Point) :
    letI := P.charts
    IsMIntegralCurve (I := 𝓘(ℝ, Model (2 * d)))
      (fun t => L.completeFlow.flow t p) L.field := by
  letI := P.charts
  exact L.completeFlow.isMIntegralCurve p

end LiouvilleData

end ClusterSkeleton
