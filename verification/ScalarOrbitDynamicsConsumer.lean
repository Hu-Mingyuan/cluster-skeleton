import ClusterSkeleton.ScalarOrbitDynamics
import ClusterSkeleton.GlobalSymplectic
import Lean.Util.CollectAxioms

noncomputable section
open ClusterSkeleton ClusterSkeleton.PrimitiveCutoffs ClusterSkeleton.ScalarOrbitDynamics
open Set Filter
open scoped Topology

namespace ScalarOrbitDynamicsConsumer

/-- An actual negative solution using the genuine radial function and allowed parameters. -/
theorem negative_solution : RadialEquation 1 3 (fun t => -Real.exp t) (fun _ => 0) := by
  intro t _
  convert (Real.hasDerivAt_exp t).neg using 1 <;> first | rfl | simp

theorem negative_escape :
    (∀ t : ℝ, 0 ≤ t → -Real.exp t ≤ -1 - t) ∧
    Tendsto (fun t => -Real.exp t) atTop atBot ∧
    Tendsto (fun t => Real.exp (-Real.exp t)) atTop (𝓝 0) := by
  have hr : radial 1 3 (-1) = 0 := radial_eq_zero (by norm_num) (by norm_num)
  refine ⟨?_, radial_tendsto_atBot (by norm_num) (by norm_num) negative_solution
    (by intros; norm_num) (by simp), radial_exp_tendsto_zero
    (by norm_num) (by norm_num) negative_solution (by intros; norm_num) (by simp)⟩
  intro t ht
  have h := radial_affine_bound (by norm_num) (by norm_num) negative_solution
    (by intros; norm_num) (by simp) ht
  simpa [hr, sub_eq_add_neg] using h

/-- A solution in the genuine nonzero affine tail of the accepted radial cutoff. -/
theorem negative_tail_solution :
    RadialEquation 1 3 (fun t => -4 - 3 * t) (fun _ => 1) := by
  intro t ht
  have hr : radial 1 3 (-4 - 3 * t) = (-4 - 3 * t) + 3 :=
    radial_tail (by norm_num) (by dsimp [radialLength]; linarith)
  convert (hasDerivAt_const t (-4 : ℝ)).sub ((hasDerivAt_id t).const_mul 3) using 1
  · rfl
  · simp only [hr]
    ring

theorem negative_tail_escape : Tendsto (fun t : ℝ => -4 - 3 * t) atTop atBot :=
  radial_tendsto_atBot (by norm_num) (by norm_num) negative_tail_solution
    (by intros; norm_num) (by norm_num)

/-- The coefficient is nonconstant and obeys the source upper bound on forward time. -/
theorem nonconstant_coefficient :
    (∀ t : ℝ, 0 ≤ t → -t ≤ 1) ∧ (fun t : ℝ => -t) 0 ≠ (fun t => -t) 1 := by
  constructor
  · intro t ht; linarith
  · norm_num

theorem zero_solution : RadialEquation 1 3 (fun _ => 0) (fun t => -t) := by
  intro t _
  have hr : radial 1 3 0 = 0 := radial_eq_zero (by norm_num) (by norm_num)
  simpa [hr] using hasDerivAt_const t (0 : ℝ)

theorem zero_rigidity {A : ℝ → ℝ} (h : RadialEquation 1 3 A (fun t => -t))
    (h0 : A 0 = 0) {t : ℝ} (ht : 0 ≤ t) : A t = 0 :=
  radial_zero (by norm_num) (by norm_num) h h0 ht

theorem positive_solution : RadialEquation 1 3 (fun t => 2 * Real.exp t) (fun t => -t) := by
  intro t _
  have hr : radial 1 3 (2 * Real.exp t) = 0 :=
    radial_eq_zero (by norm_num) (by linarith [Real.exp_pos t])
  simpa [hr] using (Real.hasDerivAt_exp t).const_mul 2

theorem positive_rigidity {A : ℝ → ℝ} (h : RadialEquation 1 3 A (fun t => -t))
    (h0 : A 0 = 2) {t : ℝ} (ht : 0 ≤ t) : A t = 2 * Real.exp t := by
  simpa [h0] using radial_positive (by norm_num) (by norm_num) h (by linarith) ht

/-- Both vertices are frozen, but the full integer matrix is skew and determinant one. -/
def frozenSeed : Seed 2 where
  B := !![0, 1; -1, 0]
  mutable := ∅
  skew := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  acyclic := ⟨fun (i : {i : Fin 2 // i ∈ (∅ : Finset (Fin 2))}) =>
    False.elim (Finset.notMem_empty i.1 i.2)⟩

theorem frozenSeed_unimodular : frozenSeed.Unimodular := by
  norm_num [Seed.Unimodular, frozenSeed, Matrix.det_fin_two]

/-- A free nonzero complex frozen variable, with the literal inherited point topology. -/
def variableFrozenPoint (z : ℂ) (hz : z ≠ 0) : frozenSeed.Point :=
  ⟨(![z, 1], fun i => False.elim (by simpa [frozenSeed] using i.property)), by
    constructor
    · intro i; exact False.elim (by simpa [frozenSeed] using i.property)
    · intro f _
      fin_cases f <;> simp [hz]⟩

theorem variableFrozenPoint_coordinate (z : ℂ) (hz : z ≠ 0) :
    (variableFrozenPoint z hz).a 0 = z := rfl

theorem variable_frozen_trapped_obstruction (flow : Flow ℝ frozenSeed.Point)
    (hODE : ∀ p t, HasDerivAt (fun s => Real.log ‖(flow s p).a 0‖)
      (Real.log ‖(flow t p).a 0‖) t)
    (z : ℂ) (hz : z ≠ 0) (hp : variableFrozenPoint z hz ∈ trappedSet flow) : ‖z‖ = 1 :=
  trapped_frozen_norm_eq_one flow 0 (by simp [frozenSeed]) hODE hp

theorem nonunit_point_not_trapped (flow : Flow ℝ frozenSeed.Point)
    (hODE : ∀ p t, HasDerivAt (fun s => Real.log ‖(flow s p).a 0‖)
      (Real.log ‖(flow t p).a 0‖) t) :
    variableFrozenPoint 2 (by norm_num) ∉ trappedSet flow := by
  intro hp
  have h := variable_frozen_trapped_obstruction flow hODE 2 (by norm_num) hp
  norm_num at h

end ScalarOrbitDynamicsConsumer

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.ScalarOrbitDynamics.RadialEquation,
        `ScalarOrbitDynamicsConsumer.frozenSeed, `ScalarOrbitDynamicsConsumer.variableFrozenPoint,
        `ClusterSkeleton.NodeTwoForm.boundaryLog] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let modules := #[`ClusterSkeleton.PrimitiveCutoffs, `ClusterSkeleton.ScalarOrbitDynamics,
    `ClusterSkeleton.Seed, `ClusterSkeleton.TrappedSet]
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  for mod in modules do
    unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  for name in supplements do
    unless env.contains name do throwError "Missing generated root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut moduleCount : Nat := 0
  let mut otherCount : Nat := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => modules.contains env.header.moduleNames[i]!
    let named := modules.any fun mod =>
      name.toString.startsWith (mod.toString ++ ".") ||
      name.toString.startsWith ("_private." ++ mod.toString ++ ".")
    if defining || named || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if defining || named then moduleCount := moduleCount + 1
      else otherCount := otherCount + 1
  if moduleCount == 0 || otherCount == 0 then throwError "Empty audit selection"
  logInfo m!"AUDITED combined modules: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
