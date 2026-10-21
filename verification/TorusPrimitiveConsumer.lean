import ClusterSkeleton.TorusPrimitive
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open ClusterSkeleton FsFltz.Geometry

namespace TorusPrimitiveConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

theorem exact_beta (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalOne (TorusPrimitive.beta S hdet) p v =
      ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im :=
  TorusPrimitive.evalOne_beta S hdet p v

theorem beta_smooth :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d)),
      y ∈ (chartAt (Model (2*d)) a).target →
      (chartAt (Model (2*d)) a).symm y ∈ initialTorus S →
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (TorusPrimitive.beta S hdet)) y :=
  TorusPrimitive.contDiffAt_beta_inChart S hdet

theorem beta_derivative (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (TorusPrimitive.beta S hdet) p = GlobalTwoForm.omega S hdet p :=
  TorusPrimitive.exteriorDerivative_beta S hdet p hp

theorem correction_smooth (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ (a : S.Point) (y : Model (2*d)),
      y ∈ (chartAt (Model (2*d)) a).target →
      (chartAt (Model (2*d)) a).symm y ∈ initialTorus S →
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (TorusPrimitive.alpha S hdet H)) y :=
  TorusPrimitive.contDiffAt_alpha_inChart S hdet H

theorem correction_derivative (H : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ H (initialTorus S) →
    ∀ p : S.Point, p ∈ initialTorus S →
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (TorusPrimitive.alpha S hdet H) p = GlobalTwoForm.omega S hdet p :=
  TorusPrimitive.exteriorDerivative_alpha S hdet H

theorem zero_correction : TorusPrimitive.alpha S hdet (fun _ => 0) =
    TorusPrimitive.beta S hdet := TorusPrimitive.alpha_zero S hdet

theorem zero_correction_derivative (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (TorusPrimitive.alpha S hdet (fun _ => 0)) p = GlobalTwoForm.omega S hdet p := by
  rw [zero_correction]
  exact beta_derivative S hdet p hp

/-- An ordinary nonconstant H, with no primitive or derivative identity as data. -/
def coordinateH (j : Fin d) (p : S.Point) : ℝ := (p.a j).re

theorem coordinateH_smooth (j : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (coordinateH S j) (initialTorus S) := by
  letI := SmoothAtlas.charts S hdet
  exact ((Complex.reCLM.comp (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ)).contMDiff.comp
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))).contMDiffOn

theorem coordinateH_nonconstant (j : Fin d) :
    ∃ p q : S.Point, p ∈ initialTorus S ∧ q ∈ initialTorus S ∧
      coordinateH S j p ≠ coordinateH S j q := by
  refine ⟨S.unitPoint, pointOfCoordinateTorus S (fun _ => ⟨2, by norm_num⟩),
    (by intro i; simp), pointOfCoordinateTorus_mem S _, ?_⟩
  norm_num [coordinateH]

theorem nonconstant_correction_derivative (j : Fin d) (p : S.Point)
    (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (TorusPrimitive.alpha S hdet (coordinateH S j)) p = GlobalTwoForm.omega S hdet p :=
  correction_derivative S hdet _ (coordinateH_smooth S hdet j) p hp

theorem log_tangent (p : S.Point) (hp : p ∈ initialTorus S)
    (w : Fin d → ℂ) (j : Fin d) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential j p
      ((TorusNondegeneracy.smoothAtlas_logarithmicTangentEquiv S hdet p hp).symm w) /
        p.a j = w j := by
  simpa only [TorusNondegeneracy.smoothAtlas_logarithmicTangentEquiv_apply] using
    congrArg (fun z => z j)
    ((TorusNondegeneracy.smoothAtlas_logarithmicTangentEquiv S hdet p hp).apply_symm_apply w)

def a2Point : Examples.a2Seed.Point :=
  pointOfCoordinateTorus Examples.a2Seed
    (fun _ => ⟨(Real.exp 1 : ℂ), by exact_mod_cast (Real.exp_ne_zero 1)⟩)

theorem a2Point_torus : a2Point ∈ initialTorus Examples.a2Seed :=
  pointOfCoordinateTorus_mem _ _

def a2AngularVector :=
  (TorusNondegeneracy.smoothAtlas_logarithmicTangentEquiv Examples.a2Seed
    Examples.a2Seed_unimodular a2Point a2Point_torus).symm ![0, Complex.I]

def a2RadialVector :=
  (TorusNondegeneracy.smoothAtlas_logarithmicTangentEquiv Examples.a2Seed
    Examples.a2Seed_unimodular a2Point a2Point_torus).symm ![1, 0]

/-- Actual nonzero beta evaluation detects sign, factor, and inverse-matrix errors. -/
theorem a2_beta_value :
    SmoothManifold.evalOne (TorusPrimitive.beta Examples.a2Seed Examples.a2Seed_unimodular)
      a2Point a2AngularVector = 1 := by
  rw [exact_beta]
  simp only [a2AngularVector, log_tangent]
  norm_num [a2Point, Examples.a2Seed, Examples.a2Matrix, Fin.sum_univ_two,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1), Real.log_exp, Complex.norm_exp]

/-- Independent exact derivative normalization at an actual torus point. -/
theorem a2_derivative_value :
    SmoothManifold.evalTwo
      ((SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.exteriorDerivative
        (TorusPrimitive.beta Examples.a2Seed Examples.a2Seed_unimodular))
      a2Point a2RadialVector a2AngularVector = 1 := by
  rw [SmoothManifold.evalTwo, beta_derivative _ _ _ a2Point_torus]
  change SmoothManifold.evalTwo (GlobalTwoForm.omega _ _) _ _ _ = _
  rw [GlobalTwoForm.omega_torus _ _ _ a2Point_torus]
  simp only [SmoothPresentation.logarithmicImaginaryValue, a2RadialVector,
    a2AngularVector, log_tangent]
  norm_num [Examples.a2Seed, Examples.a2Matrix, Fin.sum_univ_two]

def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem emptySeed_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem empty_inhabited : Nonempty emptySeed.Point := ⟨emptySeed.unitPoint⟩

theorem empty_beta_zero : TorusPrimitive.beta emptySeed emptySeed_unimodular = 0 := by
  funext p
  ext v
  simp [TorusPrimitive.beta, covectorForm]

theorem empty_derivative :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.exteriorDerivative
      (TorusPrimitive.alpha emptySeed emptySeed_unimodular (fun _ => 0)) emptySeed.unitPoint =
        GlobalTwoForm.omega emptySeed emptySeed_unimodular emptySeed.unitPoint :=
  zero_correction_derivative _ _ _ (by intro i; exact Fin.elim0 i)

end TorusPrimitiveConsumer

-- Full native per-root coverage of this module and this consumer, including
-- private/generated declarations. Inherited results are carried separately
-- through the complete source-equal 671-root accepted manifest.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mod := `ClusterSkeleton.TorusPrimitive
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  for name in supplements do
    unless env.contains name do throwError "Missing generated root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut moduleCount : Nat := 0
  let mut otherCount : Nat := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => env.header.moduleNames[i]! == mod
    let named := name.toString.startsWith "ClusterSkeleton.TorusPrimitive." ||
      name.toString.startsWith "_private.ClusterSkeleton.TorusPrimitive."
    if defining || named || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if defining || named then moduleCount := moduleCount + 1
      else otherCount := otherCount + 1
  if moduleCount == 0 || otherCount == 0 then throwError "Empty audit selection"
  logInfo m!"AUDITED {mod}: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
