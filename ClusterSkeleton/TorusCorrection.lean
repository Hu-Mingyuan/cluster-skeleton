import ClusterSkeleton.PrimitiveCutoffs
import ClusterSkeleton.DominanceCutoff
import ClusterSkeleton.TorusPrimitive
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! The manuscript correction (2.7) on the actual initial torus.
Off the torus the expression is merely totalized; no extension is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.TorusCorrection

open PrimitiveCutoffs


/-- The periodic cutoff depends only on the angle class. -/
theorem vartheta_eq_of_angle_eq {δ s t : ℝ}
    (h : (s : Real.Angle) = (t : Real.Angle)) : vartheta δ s = vartheta δ t := by
  have hs : Real.sin s = Real.sin t := congrArg Real.Angle.sin h
  have hc : Real.cos s = Real.cos t := congrArg Real.Angle.cos h
  simp only [vartheta, angularWindow, hs, hc]

/-- A real angle lift on a neighborhood of any nonzero base point. -/
def localAngle (b z : ℂ) : ℝ := (Complex.log (z / b)).im + Complex.arg b

theorem localAngle_self {b : ℂ} (hb : b ≠ 0) : localAngle b b = Complex.arg b := by
  simp [localAngle, div_self hb]

theorem localAngle_coe {b z : ℂ} (hb : b ≠ 0) (hz : z ≠ 0) :
    (localAngle b z : Real.Angle) = (Complex.arg z : Real.Angle) := by
  simp only [localAngle, Complex.log_im, Real.Angle.coe_add,
    Complex.arg_div_coe_angle hz hb, sub_add_cancel]

theorem localAngle_contDiffAt {b : ℂ} (hb : b ≠ 0) :
    ContDiffAt ℝ ∞ (localAngle b) b := by
  have hl : ContDiffAt ℝ ∞ Complex.log (b / b) := by
    rw [div_self hb]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  have hd : ContDiffAt ℝ ∞ (fun z : ℂ => z / b) b :=
    contDiffAt_id.div_const b
  exact ((Complex.imCLM.contDiff.contDiffAt.comp b (hl.comp b (f := fun z : ℂ => z / b) hd)).add contDiffAt_const)

theorem vartheta_localAngle {δ : ℝ} {b z : ℂ} (hb : b ≠ 0) (hz : z ≠ 0) :
    vartheta δ (localAngle b z) = vartheta δ (Complex.arg z) :=
  vartheta_eq_of_angle_eq (localAngle_coe hb hz)

/-- The angular cutoff is smooth on the punctured complex plane, including the
negative real axis: a smooth local logarithm supplies the representative. -/
theorem vartheta_arg_contDiffAt {δ : ℝ} (hδ : 0 < δ) {b : ℂ} (hb : b ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℂ => vartheta δ (Complex.arg z)) b := by
  have he : (fun z : ℂ => vartheta δ (Complex.arg z)) =ᶠ[𝓝 b]
      (fun z : ℂ => vartheta δ (localAngle b z)) := by
    filter_upwards [eventually_ne_nhds hb] with z hz
    exact (vartheta_localAngle hb hz).symm
  exact ((vartheta_smooth hδ).contDiffAt.comp b (localAngle_contDiffAt hb)).congr_of_eventuallyEq he


variable {d : ℕ} (S : Seed d)

/-- All original coordinates, including the variable frozen coordinates. -/
def A (p : S.Point) (j : Fin d) : ℝ := Real.log ‖p.a j‖

/-- The full matrix row; the sum is not restricted to mutable indices. -/
def rowLog (p : S.Point) (i : Fin d) : ℝ := ∑ j : Fin d, (S.B i j : ℝ) * A S p j

/-- The accepted exchange character with the manuscript's minus sign. -/
def angular (δ : ℝ) (p : S.Point) (i : Fin d) : ℝ :=
  PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter p i))

/-- A totalized finite expression, with no regularity assertion off the torus. -/
def H (ε κ δ : ℝ) (p : S.Point) : ℝ :=
  ∑ i ∈ S.mutable, PrimitiveCutoffs.radial ε κ (A S p i) *
    DominanceCutoff.dominance S ε i (A S p) * PrimitiveCutoffs.rho (rowLog S p i) *
      angular S δ p i

theorem manuscript_formula (ε κ δ : ℝ) (p : S.Point) (_hp : p ∈ initialTorus S) :
    H S ε κ δ p = ∑ i ∈ S.mutable,
      PrimitiveCutoffs.radial ε κ (Real.log ‖p.a i‖) *
      DominanceCutoff.dominance S ε i (fun j => Real.log ‖p.a j‖) *
      PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖) *
      PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter p i)) := rfl

theorem H_empty_mutable (ε κ δ : ℝ) (hM : S.mutable = ∅) :
    H S ε κ δ = fun _ => 0 := by
  funext p
  simp [H, hM]

theorem exchangeCharacter_ne_zero (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    exchangeCharacter p i ≠ 0 := by
  rw [exchangeCharacter_eq_zpow_product]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hp j)

variable (hdet : S.Unimodular)

theorem contMDiffAt_A (p : S.Point) (hp : p ∈ initialTorus S) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Fin d → ℝ) ∞ (A S) p := by
  letI := SmoothAtlas.charts S hdet
  apply contMDiffAt_pi_space.mpr
  intro i
  exact ((contDiffAt_norm ℂ (n := ∞) (hp i)).log (norm_ne_zero_iff.mpr (hp i))).comp_contMDiffAt (f := fun q : S.Point => q.a i)
    ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
      (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet)) p)

theorem contMDiffAt_rowLog (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (fun q => rowLog S q i) p := by
  letI := SmoothAtlas.charts S hdet
  have hf : ContDiff ℝ ∞ (fun x : Fin d → ℝ => ∑ j : Fin d, (S.B i j : ℝ) * x j) := by
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul (contDiff_apply ℝ ℝ j)
  exact hf.comp_contMDiffAt (contMDiffAt_A S hdet p hp)

theorem contMDiffAt_exchangeCharacter (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞ (fun q => exchangeCharacter q i) p := by
  letI := SmoothAtlas.charts S hdet
  have hP : ContDiff ℂ ∞ (fun x : Fin d → ℂ => S.positiveMonomial x i) := by
    apply contDiff_prod
    intro j _
    exact (contDiff_apply ℂ ℂ j).pow _
  have hQ : ContDiff ℂ ∞ (fun x : Fin d → ℂ => S.negativeMonomial x i) := by
    apply contDiff_prod
    intro j _
    exact (contDiff_apply ℂ ℂ j).pow _
  have hn : S.negativeMonomial p.a i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hp j)
  exact ((hP.contDiffAt.div hQ.contDiffAt hn).restrict_scalars ℝ).comp_contMDiffAt
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet) p)

theorem contMDiffAt_angular {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (fun q => angular S δ q i) p := by
  letI := SmoothAtlas.charts S hdet
  exact (vartheta_arg_contDiffAt hδ (neg_ne_zero.mpr (exchangeCharacter_ne_zero S p hp i))).comp_contMDiffAt (f := fun q : S.Point => -exchangeCharacter q i)
    (contMDiffAt_exchangeCharacter S hdet p hp i).neg

/-- Native smoothness is proved on the open initial torus, for the constructed H. -/
theorem contMDiffOn_H (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (H S ε κ δ) (initialTorus S) := by
  letI := SmoothAtlas.charts S hdet
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  unfold H
  apply ContMDiffAt.sum
  intro i _
  have hA := contMDiffAt_A S hdet p hp
  have hi := contMDiffAt_pi_space.mp hA i
  exact (((PrimitiveCutoffs.radial_smooth ε κ).comp_contMDiffAt hi).mul
    ((DominanceCutoff.contDiff_dominance S ε i).comp_contMDiffAt hA) |>.mul
    (PrimitiveCutoffs.rho_smooth.comp_contMDiffAt (contMDiffAt_rowLog S hdet p hp i))).mul
      (contMDiffAt_angular S hdet hδ p hp i)

/-- The corrected native one-form, using the constructed manuscript correction. -/
def alpha (ε κ δ : ℝ) : (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  TorusPrimitive.alpha S hdet (H S ε κ δ)

theorem evalOne_alpha (ε κ δ : ℝ) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalOne (alpha S hdet ε κ δ) p v =
      (∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im) -
      differentialCovector (SmoothAtlas.presentation S hdet).manifold (H S ε κ δ) p v := by
  rw [alpha, TorusPrimitive.evalOne_alpha, TorusPrimitive.evalOne_beta]

theorem contDiffAt_alpha_inChart (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ initialTorus S),
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (alpha S hdet ε κ δ)) y :=
  TorusPrimitive.contDiffAt_alpha_inChart S hdet _ (contMDiffOn_H S hdet ε κ hδ)

/-- The actual exterior derivative equals the already accepted global two-form
at every torus point. The H smoothness premise has been discharged. -/
theorem exteriorDerivative_alpha (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (alpha S hdet ε κ δ) p =
      GlobalTwoForm.omega S hdet p :=
  TorusPrimitive.exteriorDerivative_alpha S hdet _ (contMDiffOn_H S hdet ε κ hδ) p hp

end ClusterSkeleton.TorusCorrection
