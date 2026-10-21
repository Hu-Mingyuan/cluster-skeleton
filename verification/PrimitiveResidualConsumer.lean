import ClusterSkeleton.PrimitiveResidual
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Topology BigOperators
open Set FsFltz.Geometry ClusterSkeleton ClusterSkeleton.PrimitiveResidual
namespace PrimitiveResidualConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- No nonvanishing premise: arbitrary actual point and tangent direction. -/
theorem exact_split (I : Finset (Fin d)) (hI : S.Independent I) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalOne (TorusPrimitive.beta S hdet) p v =
      SmoothManifold.evalOne (PrimitiveResidual.residual S hdet I) p v +
      ∑ i ∈ I, (Real.log ‖p.a i‖ * tau S hdet i p v -
        logRow S i p * TorusPrimitive.angleCovector S hdet i p v) := by
  rw [beta_decomposition S hdet I hI]
  simp [SmoothManifold.evalOne, covectorForm]

/-- Arbitrary native charts, including all simultaneous zero directions. -/
theorem residual_smooth (I : Finset (Fin d)) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d)),
      y ∈ (chartAt (Model (2*d)) a).target →
      (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I →
      ContDiffAt ℝ ∞
        ((SmoothAtlas.presentation S hdet).manifold.formInChart a (PrimitiveResidual.residual S hdet I)) y :=
  contDiffAt_residual_inChart S hdet I

/-- Actual native differential, evaluated in an arbitrary tangent direction. -/
theorem angular_bridge (i : S.Mutable) (p : S.Point) (hp : p ∈ initialTorus S)
    (hs : 1 - p.a i * normalizedPartner p i ∈ Complex.slitPlane)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    (∑ j : Fin d, (S.B i j : ℝ) *
      ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im) =
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (fun q => (Complex.log (1 - q.a i * normalizedPartner q i)).im) p v := by
  have h := congrArg (fun f => f v) (tau_eq_nodeAngle_differential S hdet i p hp hs)
  simpa [tau, TorusPrimitive.angleCovector_apply] using h

theorem empty_residual : PrimitiveResidual.residual S hdet ∅ = TorusPrimitive.beta S hdet := by
  funext p
  ext v
  simp [PrimitiveResidual.residual, TorusPrimitive.beta]

/-- Two independent mutable nodes and two variable frozen coordinates. -/
def fourMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0; -1, 0, 0, 1; 0, 0, 0, 1; 0, -1, -1, 0]

def fourSeed : Seed 4 where
  B := fourMatrix
  mutable := {0, 2}
  skew := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [fourMatrix]
  acyclic := by
    have hz : ∀ i ∈ ({0,2} : Finset (Fin 4)), ∀ j ∈ ({0,2} : Finset (Fin 4)),
        fourMatrix i j = 0 := by
      intro i hi j hj
      fin_cases i <;> fin_cases j <;> simp_all [fourMatrix]
    refine ⟨fun i => Acc.intro i ?_⟩
    intro j hj
    have h := hz j j.property i i.property
    rw [h] at hj
    exact (lt_irrefl _ hj).elim

theorem four_unimodular : fourSeed.Unimodular := by
  norm_num [Seed.Unimodular, fourSeed, fourMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rfl

theorem two_independent : fourSeed.Independent {0,2} := by
  constructor
  · exact Finset.Subset.refl _
  · intro i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all [fourSeed, fourMatrix]

/-- An actual simultaneous zero stratum; no empty-carrier argument. -/
def boundaryPoint : fourSeed.Point :=
  ⟨(![0,-1,0,-1], fun _ => 0), by
    constructor
    · rintro ⟨i, hi⟩
      change i ∈ ({0,2} : Finset (Fin 4)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [fourSeed, fourMatrix, Seed.positiveMonomial,
        Seed.negativeMonomial, Fin.prod_univ_succ]
    · intro f hf
      fin_cases f <;> simp_all [fourSeed]⟩

theorem boundary_locus : boundaryPoint ∈ candidateChartLocus fourSeed {0,2} := by
  intro j hj
  fin_cases j <;> simp_all [boundaryPoint, Seed.Point.a]

theorem boundary_two_zeros : boundaryPoint.a 0 = 0 ∧ boundaryPoint.a 2 = 0 := by
  constructor <;> rfl

theorem smooth_at_actual_boundary :
    letI := SmoothAtlas.charts fourSeed four_unimodular
    ContDiffAt ℝ ∞
      ((SmoothAtlas.presentation fourSeed four_unimodular).manifold.formInChart
        boundaryPoint (PrimitiveResidual.residual fourSeed four_unimodular {0,2}))
      ((chartAt (Model 8) boundaryPoint) boundaryPoint) := by
  letI := SmoothAtlas.charts fourSeed four_unimodular
  apply contDiffAt_residual_inChart
  · exact (chartAt (Model 8) boundaryPoint).map_source (mem_chart_source _ _)
  · rw [(chartAt (Model 8) boundaryPoint).left_inv (mem_chart_source _ _)]
    exact boundary_locus

/-- Frozen values s and t are arbitrary nonzero variables, not constants. -/
def variableFrozenPoint (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) : fourSeed.Point :=
  ⟨(![1,s,1,t], fun i => if (i : Fin 4) = 0 then s + 1 else t + 1), by
    constructor
    · rintro ⟨i, hi⟩
      change i ∈ ({0,2} : Finset (Fin 4)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [fourSeed, fourMatrix, Seed.positiveMonomial,
        Seed.negativeMonomial, Fin.prod_univ_succ]
    · intro f hf
      fin_cases f <;> simp_all [fourSeed]⟩

theorem variableFrozen_torus (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    variableFrozenPoint s t hs ht ∈ initialTorus fourSeed := by
  intro j
  fin_cases j <;> simp [variableFrozenPoint, Seed.Point.a, hs, ht]

theorem frozen_values (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    (variableFrozenPoint s t hs ht).a 1 = s ∧
    (variableFrozenPoint s t hs ht).a 3 = t := ⟨rfl,rfl⟩

theorem frozen_row (p : fourSeed.Point)
    (v : (SmoothAtlas.presentation fourSeed four_unimodular).manifold.Tangent p) :
    tau fourSeed four_unimodular 0 p v =
      ((SmoothAtlas.presentation fourSeed four_unimodular).coordinateDifferential 1 p v /
        p.a 1).im := by
  simp [tau, fourSeed, fourMatrix, Fin.sum_univ_succ]
  exact TorusPrimitive.angleCovector_apply _ _ _ _ _

/-- The logarithm hypothesis has actual nonempty torus instances. -/
theorem slit_at_variableFrozen (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0)
    (hslit : -s ∈ Complex.slitPlane) :
    1 - (variableFrozenPoint s t hs ht).a 0 *
      normalizedPartner (variableFrozenPoint s t hs ht) ⟨0, by decide⟩ ∈ Complex.slitPlane := by
  rw [node_argument fourSeed ⟨0, by simp [fourSeed]⟩ _ (variableFrozen_torus s t hs ht)]
  simpa [variableFrozenPoint, Seed.Point.a, fourSeed, fourMatrix, Fin.prod_univ_succ] using hslit

/-- The surviving complementary frozen block is nontrivial. -/
theorem frozen_residual (p : fourSeed.Point)
    (v : (SmoothAtlas.presentation fourSeed four_unimodular).manifold.Tangent p) :
    SmoothManifold.evalOne (PrimitiveResidual.residual fourSeed four_unimodular {0,2}) p v =
      Real.log ‖p.a 1‖ * TorusPrimitive.angleCovector fourSeed four_unimodular 3 p v -
      Real.log ‖p.a 3‖ * TorusPrimitive.angleCovector fourSeed four_unimodular 1 p v := by
  have hc : ({0,2} : Finset (Fin 4))ᶜ = {1,3} := by decide
  simp [PrimitiveResidual.residual, hc, SmoothManifold.evalOne, covectorForm,
    fourSeed, fourMatrix, sub_eq_add_neg]

theorem simultaneous_split (p : fourSeed.Point)
    (v : (SmoothAtlas.presentation fourSeed four_unimodular).manifold.Tangent p) :
    SmoothManifold.evalOne (TorusPrimitive.beta fourSeed four_unimodular) p v =
      SmoothManifold.evalOne (PrimitiveResidual.residual fourSeed four_unimodular {0,2}) p v +
      ∑ i ∈ ({0,2} : Finset (Fin 4)),
        (Real.log ‖p.a i‖ * tau fourSeed four_unimodular i p v -
        logRow fourSeed i p * TorusPrimitive.angleCovector fourSeed four_unimodular i p v) :=
  exact_split fourSeed four_unimodular {0,2} two_independent p v

end PrimitiveResidualConsumer

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.PrimitiveResidual.tau,
        `ClusterSkeleton.PrimitiveResidual.logRow,
        `ClusterSkeleton.PrimitiveResidual.residual] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mod := `ClusterSkeleton.PrimitiveResidual
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
    let named := name.toString.startsWith "ClusterSkeleton.PrimitiveResidual." ||
      name.toString.startsWith "_private.ClusterSkeleton.PrimitiveResidual."
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
