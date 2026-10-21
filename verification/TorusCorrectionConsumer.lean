import ClusterSkeleton.TorusCorrection
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open ClusterSkeleton FsFltz.Geometry Set Filter

namespace TorusCorrectionConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- All allowed parameters; no assumed smoothness of H. -/
theorem arbitrary_parameters {ε κ δ : ℝ} (_hε : 0 < ε)
    (_hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (TorusCorrection.H S ε κ δ) (initialTorus S) ∧
    ∀ p : S.Point, p ∈ initialTorus S →
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (TorusCorrection.alpha S hdet ε κ δ) p = GlobalTwoForm.omega S hdet p :=
  ⟨TorusCorrection.contMDiffOn_H S hdet ε κ hδ,
    TorusCorrection.exteriorDerivative_alpha S hdet ε κ hδ⟩

theorem formula (ε κ δ : ℝ) (p : S.Point) (hp : p ∈ initialTorus S) :
    TorusCorrection.H S ε κ δ p = ∑ i ∈ S.mutable,
      PrimitiveCutoffs.radial ε κ (Real.log ‖p.a i‖) *
      (∏ j ∈ S.mutable.filter (fun j => S.B i j ≠ 0),
        DominanceCutoff.chi ε (Real.log ‖p.a i‖ - Real.log ‖p.a j‖)) *
      PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖) *
      PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter p i)) :=
  TorusCorrection.manuscript_formula S ε κ δ p hp

theorem smooth_coefficients (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d)),
      y ∈ (chartAt (Model (2*d)) a).target →
      (chartAt (Model (2*d)) a).symm y ∈ initialTorus S →
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (TorusCorrection.alpha S hdet ε κ δ)) y :=
  TorusCorrection.contDiffAt_alpha_inChart S hdet ε κ hδ

theorem representatives (δ t : ℝ) (k : ℤ) :
    PrimitiveCutoffs.vartheta δ (t + k * (2 * Real.pi)) = PrimitiveCutoffs.vartheta δ t :=
  PrimitiveCutoffs.vartheta_representative_independent δ t k

/-- A smooth representative centered ON the principal argument cut. -/
theorem cut_lift :
    ContDiffAt ℝ ∞ (TorusCorrection.localAngle (-1)) (-1) ∧
    TorusCorrection.localAngle (-1) (-1) = Real.pi := by
  refine ⟨TorusCorrection.localAngle_contDiffAt (by norm_num), ?_⟩
  simpa only [Complex.arg_neg_one] using
    (TorusCorrection.localAngle_self (b := (-1 : ℂ)) (by norm_num))

theorem cut_smooth {δ : ℝ} (hδ : 0 < δ) :
    ContDiffAt ℝ ∞ (fun z : ℂ => PrimitiveCutoffs.vartheta δ (Complex.arg z)) (-1) :=
  TorusCorrection.vartheta_arg_contDiffAt hδ (by norm_num)

theorem empty_mutable (ε κ δ : ℝ) (hM : S.mutable = ∅) :
    TorusCorrection.H S ε κ δ = fun _ => 0 := TorusCorrection.H_empty_mutable S ε κ δ hM

def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem emptySeed_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem dimension_zero (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    TorusCorrection.H emptySeed ε κ δ emptySeed.unitPoint = 0 ∧
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.exteriorDerivative
      (TorusCorrection.alpha emptySeed emptySeed_unimodular ε κ δ) emptySeed.unitPoint =
      GlobalTwoForm.omega emptySeed emptySeed_unimodular emptySeed.unitPoint := by
  refine ⟨by simp [TorusCorrection.H, emptySeed], ?_⟩
  exact TorusCorrection.exteriorDerivative_alpha _ _ ε κ hδ _ (fun i => Fin.elim0 i)

/-- Same unimodular full matrix, but coordinate 1 is a variable frozen coordinate. -/
def frozenSeed : Seed 2 where
  B := Examples.a2Matrix
  mutable := {0}
  skew := Examples.a2Seed.skew
  acyclic := by
    refine ⟨?_⟩
    intro i
    apply Acc.intro
    intro j h
    have hi : i.val = 0 := Finset.mem_singleton.mp i.property
    have hj : j.val = 0 := Finset.mem_singleton.mp j.property
    simpa [hi, hj, Examples.a2Matrix] using h

theorem frozenSeed_unimodular : frozenSeed.Unimodular := by
  norm_num [Seed.Unimodular, frozenSeed, Examples.a2Matrix, Matrix.det_fin_two]

def phase : ℝ := Real.pi / 8

def nonzeroPoint : frozenSeed.Point :=
  pointOfCoordinateTorus frozenSeed (fun j =>
    if j = 0 then ⟨(Real.exp (-5) : ℂ), by exact_mod_cast Real.exp_ne_zero (-5)⟩
    else ⟨-Complex.exp ((phase : ℂ) * Complex.I), neg_ne_zero.mpr (Complex.exp_ne_zero _)⟩)

theorem nonzeroPoint_torus : nonzeroPoint ∈ initialTorus frozenSeed :=
  pointOfCoordinateTorus_mem _ _

theorem frozen_row (p : frozenSeed.Point) :
    TorusCorrection.rowLog frozenSeed p 0 = Real.log ‖p.a 1‖ := by
  simp [TorusCorrection.rowLog, TorusCorrection.A, frozenSeed, Examples.a2Matrix, Fin.sum_univ_two]

theorem nonzeroPoint_coordinates :
    nonzeroPoint.a 0 = (Real.exp (-5) : ℂ) ∧
    nonzeroPoint.a 1 = -Complex.exp ((phase : ℂ) * Complex.I) := by
  simp [nonzeroPoint]

theorem nonzeroPoint_log :
    TorusCorrection.A frozenSeed nonzeroPoint 0 = -5 ∧
    TorusCorrection.A frozenSeed nonzeroPoint 1 = 0 := by
  simp [TorusCorrection.A, nonzeroPoint_coordinates.1, nonzeroPoint_coordinates.2,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-5)), Real.log_exp,
    Complex.norm_exp]

theorem nonzeroPoint_character : exchangeCharacter nonzeroPoint 0 = nonzeroPoint.a 1 := by
  simp [exchangeCharacter_eq_zpow_product, frozenSeed, Examples.a2Matrix, Fin.prod_univ_two]

theorem nonzeroPoint_angle : Complex.arg (-exchangeCharacter nonzeroPoint 0) = phase := by
  rw [nonzeroPoint_character, nonzeroPoint_coordinates.2, neg_neg, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> dsimp [phase] <;> linarith [Real.pi_pos]

theorem nonzero_correction : TorusCorrection.H frozenSeed 1 3 (Real.pi / 2) nonzeroPoint =
    -2 * phase := by
  have hr : PrimitiveCutoffs.radial 1 3 (-5) = -2 := by
    convert PrimitiveCutoffs.radial_tail (ε := 1) (κ := 3) (A := -5) (by norm_num)
      (by norm_num [PrimitiveCutoffs.radialLength]) using 1 <;> norm_num
  have hv : PrimitiveCutoffs.vartheta (Real.pi / 2) phase = phase := by
    apply PrimitiveCutoffs.vartheta_eq_self (by positivity)
    norm_num [phase, PrimitiveCutoffs.angularRadius, abs_of_pos Real.pi_pos, abs_div, div_div]
  have hdom : DominanceCutoff.dominance frozenSeed 1 0 (TorusCorrection.A frozenSeed nonzeroPoint) = 1 := by
    apply DominanceCutoff.dominance_of_no_neighbors
    simp [DominanceCutoff.mutableNeighbors, frozenSeed, Examples.a2Matrix]
  have hrow : TorusCorrection.rowLog frozenSeed nonzeroPoint 0 = 0 := by
    rw [frozen_row]
    exact nonzeroPoint_log.2
  simp only [TorusCorrection.H, frozenSeed, Finset.sum_singleton]
  change PrimitiveCutoffs.radial 1 3 (TorusCorrection.A frozenSeed nonzeroPoint 0) *
    DominanceCutoff.dominance frozenSeed 1 0 (TorusCorrection.A frozenSeed nonzeroPoint) *
    PrimitiveCutoffs.rho (TorusCorrection.rowLog frozenSeed nonzeroPoint 0) *
    PrimitiveCutoffs.vartheta (Real.pi / 2) (Complex.arg (-exchangeCharacter nonzeroPoint 0)) = _
  rw [nonzeroPoint_log.1, hr, hdom, hrow, PrimitiveCutoffs.rho_eq_one (by norm_num),
    nonzeroPoint_angle, hv]
  ring

theorem actual_nonzero_correction :
    nonzeroPoint ∈ initialTorus frozenSeed ∧
    TorusCorrection.H frozenSeed 1 3 (Real.pi / 2) nonzeroPoint ≠ 0 := by
  refine ⟨nonzeroPoint_torus, ?_⟩
  rw [nonzero_correction]
  exact mul_ne_zero (by norm_num) (by dsimp [phase]; positivity)

/-- Frozen coordinates vary in the actual carrier; the full row detects that variation. -/
theorem frozen_row_varies : ∃ p q : frozenSeed.Point,
    p ∈ initialTorus frozenSeed ∧ q ∈ initialTorus frozenSeed ∧
    TorusCorrection.rowLog frozenSeed p 0 ≠ TorusCorrection.rowLog frozenSeed q 0 := by
  refine ⟨frozenSeed.unitPoint, pointOfCoordinateTorus frozenSeed
    (fun _ => ⟨(Real.exp 1 : ℂ), by exact_mod_cast Real.exp_ne_zero 1⟩),
    (by intro i; simp), pointOfCoordinateTorus_mem _ _, ?_⟩
  simp [frozen_row, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos 1), Real.log_exp, Complex.norm_exp]

theorem nonzero_parameters : (0 : ℝ) < 1 ∧ 2 * (1 : ℝ) + 1 ≤ 3 ∧
    0 < Real.pi / 2 ∧ Real.pi / 2 < Real.pi := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> linarith [Real.pi_pos]

theorem nonzero_point_derivative :
    (SmoothAtlas.presentation frozenSeed frozenSeed_unimodular).manifold.exteriorDerivative
      (TorusCorrection.alpha frozenSeed frozenSeed_unimodular 1 3 (Real.pi / 2)) nonzeroPoint =
      GlobalTwoForm.omega frozenSeed frozenSeed_unimodular nonzeroPoint :=
  TorusCorrection.exteriorDerivative_alpha _ _ _ _ (by positivity) _ nonzeroPoint_torus

end TorusCorrectionConsumer

-- Native per-root audit of the exact combined new/borrowed scalar closure.
-- Full unchanged inherited evidence is source-checked and carried in the delivery.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mods := #[`ClusterSkeleton.PrimitiveCutoffs, `ClusterSkeleton.DominanceCutoff,
    `ClusterSkeleton.TorusPrimitive, `ClusterSkeleton.TorusCorrection]
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  for mod in mods do
    unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  for name in supplements do
    unless env.contains name do throwError "Missing generated root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut moduleCount : Nat := 0
  let mut otherCount : Nat := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => mods.contains env.header.moduleNames[i]!
    let named := mods.any fun mod => name.toString.startsWith (mod.toString ++ ".") ||
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
