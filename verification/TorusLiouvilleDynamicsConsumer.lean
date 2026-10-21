import ClusterSkeleton.TorusLiouvilleDynamics
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open ClusterSkeleton FsFltz.Geometry Set Filter TorusLiouvilleDynamics

namespace TorusLiouvilleDynamicsConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Arbitrary actual native tangent, with every allowed parameter quantified. -/
theorem native_contraction {ε κ δ : ℝ} (_hε : 0 < ε)
    (_hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p
      ((SmoothAtlas.presentation S hdet).manifold.liouvilleVector
        (TorusCorrection.alpha S hdet ε κ δ) p) v =
      SmoothManifold.evalOne (TorusCorrection.alpha S hdet ε κ δ) p v :=
  contraction S hdet ε κ hδ p hp v

theorem source_radial {ε κ δ : ℝ} (_hε : 0 < ε)
    (_hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) (hi : i ∈ S.mutable) :
    (((SmoothAtlas.presentation S hdet).coordinateDifferential i p
        ((SmoothAtlas.presentation S hdet).manifold.liouvilleVector
          (TorusCorrection.alpha S hdet ε κ δ) p)) / p.a i).re =
      Real.log ‖p.a i‖ - PrimitiveCutoffs.radial ε κ (Real.log ‖p.a i‖) *
        (∏ j ∈ S.mutable.filter (fun j => S.B i j ≠ 0),
          DominanceCutoff.chi ε (Real.log ‖p.a i‖ - Real.log ‖p.a j‖)) *
        PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) :=
  mutable_radial_equation S hdet ε κ hδ p hp i hi

theorem source_angular {ε κ δ : ℝ} (_hε : 0 < ε)
    (_hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (∑ j : Fin d, (S.B i j : ℝ) * (logarithmicComponents S hdet ε κ δ p j).im) =
      deriv (fun t : ℝ => logarithmicHamiltonian S ε κ δ p
        (t • (Pi.single i 1 : Fin d → ℂ))) 0 :=
  angular_equation_partial_deriv S hdet ε κ hδ p hp i

theorem growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : S.Point, p ∈ initialTorus S →
      (∑ j : Fin d, (|(logarithmicComponents S hdet ε κ δ p j).re| +
        |(logarithmicComponents S hdet ε κ δ p j).im|)) ≤
      C * (1 + ∑ j : Fin d, |TorusCorrection.A S p j|) :=
  logarithmic_linear_growth S hdet hε hκ hδ

theorem signs {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (0 < TorusCorrection.A S p i →
      (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i) ∧
    (TorusCorrection.A S p i < 0 →
      (logarithmicComponents S hdet ε κ δ p i).re ≤
        TorusCorrection.A S p i - PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) ∧
      TorusCorrection.A S p i - PrimitiveCutoffs.radial ε κ (TorusCorrection.A S p i) < 0) ∧
    (TorusCorrection.A S p i = 0 → (logarithmicComponents S hdet ε κ δ p i).re = 0) := by
  have hk : 2 * ε < κ := by linarith
  exact ⟨fun h => radial_eq_of_nonneg S hdet hε hk hδ p hp i h.le,
    radial_negative_bound S hdet hε hk hδ p hp i,
    radial_zero S hdet hε hk hδ p hp i⟩

theorem empty_mutable_components (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hM : S.mutable = ∅) (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (logarithmicComponents S hdet ε κ δ p i).re = TorusCorrection.A S p i ∧
    (logarithmicComponents S hdet ε κ δ p i).im = 0 := by
  refine ⟨frozen_radial_equation S hdet ε κ hδ p hp i (by simp [hM]), ?_⟩
  obtain ⟨N, _, hb⟩ := full_matrix_inverse_bound S hdet
  have hh := hb (fun j => (logarithmicComponents S hdet ε κ δ p j).im) 0 (by
    intro j
    rw [angular_equation S hdet ε κ hδ p hp j,
      differential_H_radial S hdet ε κ hδ p hp j]
    simp [hM])
  simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero] at hh
  have hsingle := Finset.single_le_sum
    (fun j _ => abs_nonneg (logarithmicComponents S hdet ε κ δ p j).im) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hsingle.trans hh) (abs_nonneg _))

/-- The examples below reproduce accepted carrier data; they do not use peer sources. -/
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

def phase : ℝ := Real.pi / 16

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
    linarith [Real.pi_pos]
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


theorem nonzero_native_radial :
    (logarithmicComponents frozenSeed frozenSeed_unimodular 1 3 (Real.pi / 2)
      nonzeroPoint 0).re = -3 ∧
    (logarithmicComponents frozenSeed frozenSeed_unimodular 1 3 (Real.pi / 2)
      nonzeroPoint 0).re ≠ TorusCorrection.A frozenSeed nonzeroPoint 0 := by
  have hr : PrimitiveCutoffs.radial 1 3 (-5) = -2 := by
    convert PrimitiveCutoffs.radial_tail (ε := 1) (κ := 3) (A := -5) (by norm_num)
      (by norm_num [PrimitiveCutoffs.radialLength]) using 1 <;> norm_num
  have he : PrimitiveCutoffs.vartheta (Real.pi / 2) =ᶠ[𝓝 phase] fun t => t := by
    have ht : |phase| < PrimitiveCutoffs.angularRadius (Real.pi / 2) / 2 := by
      norm_num [phase, PrimitiveCutoffs.angularRadius, abs_of_pos Real.pi_pos,
        abs_div, div_div]
      linarith [Real.pi_pos]
    filter_upwards [continuous_abs.continuousAt.eventually_lt_const ht] with t ht
    exact PrimitiveCutoffs.vartheta_eq_self (by positivity) ht.le
  have hv : deriv (PrimitiveCutoffs.vartheta (Real.pi / 2)) phase = 1 := by
    rw [he.deriv_eq]
    simp
  have hdom : DominanceCutoff.dominance frozenSeed 1 0 (TorusCorrection.A frozenSeed nonzeroPoint) = 1 := by
    apply DominanceCutoff.dominance_of_no_neighbors
    simp [DominanceCutoff.mutableNeighbors, frozenSeed, Examples.a2Matrix]
  have hrow : TorusCorrection.rowLog frozenSeed nonzeroPoint 0 = 0 := by
    rw [frozen_row]
    exact nonzeroPoint_log.2
  have hz := mutable_radial_equation frozenSeed frozenSeed_unimodular 1 3
    (show 0 < Real.pi / 2 by positivity) nonzeroPoint nonzeroPoint_torus 0
      (by simp [frozenSeed])
  rw [nonzeroPoint_log.1, hr, hdom, hrow, PrimitiveCutoffs.rho_eq_one (by norm_num),
    nonzeroPoint_angle, hv] at hz
  constructor
  · linarith
  · rw [nonzeroPoint_log.1]
    linarith

theorem frozen_native_variable (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : frozenSeed.Point) (hp : p ∈ initialTorus frozenSeed) :
    (logarithmicComponents frozenSeed frozenSeed_unimodular ε κ δ p 1).re =
      Real.log ‖p.a 1‖ :=
  frozen_radial_equation frozenSeed frozenSeed_unimodular ε κ hδ p hp 1
    (by simp [frozenSeed])

theorem mixed_full_row_angular (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : frozenSeed.Point) (hp : p ∈ initialTorus frozenSeed) :
    (logarithmicComponents frozenSeed frozenSeed_unimodular ε κ δ p 1).im =
      deriv (fun t : ℝ => logarithmicHamiltonian frozenSeed ε κ δ p
        (t • (Pi.single 0 1 : Fin 2 → ℂ))) 0 := by
  simpa [frozenSeed, Examples.a2Matrix, Fin.sum_univ_two] using
    angular_equation_partial_deriv frozenSeed frozenSeed_unimodular ε κ hδ p hp 0

theorem zero_dimension_field (ε κ δ : ℝ) :
    Z emptySeed emptySeed_unimodular ε κ δ emptySeed.unitPoint = 0 := by
  apply (TorusNondegeneracy.logarithmicTangentEquiv emptySeed
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular) emptySeed.unitPoint
      (fun i => Fin.elim0 i)).injective
  ext i
  exact Fin.elim0 i

theorem cut_native_differential {δ : ℝ} (hδ : 0 < δ) :
    HasFDerivAt (fun z : ℂ => PrimitiveCutoffs.vartheta δ (Complex.arg z))
      (deriv (PrimitiveCutoffs.vartheta δ) Real.pi •
        Complex.imCLM.comp ((-1 : ℂ)⁻¹ • (1 : ℂ →L[ℝ] ℂ))) (-1) := by
  simpa only [Complex.arg_neg_one] using
    hasFDerivAt_vartheta_arg hδ (b := (-1 : ℂ)) (by norm_num)

theorem cut_actual_point (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Complex.arg (-exchangeCharacter frozenSeed.unitPoint 0) = Real.pi ∧
    (∑ j : Fin 2, (frozenSeed.B 0 j : ℝ) *
      (logarithmicComponents frozenSeed frozenSeed_unimodular ε κ δ frozenSeed.unitPoint j).im) =
      deriv (fun t : ℝ => logarithmicHamiltonian frozenSeed ε κ δ frozenSeed.unitPoint
        (t • (Pi.single 0 1 : Fin 2 → ℂ))) 0 := by
  refine ⟨?_, angular_equation_partial_deriv frozenSeed frozenSeed_unimodular ε κ hδ
    frozenSeed.unitPoint (by intro i; simp) 0⟩
  simp [exchangeCharacter_eq_zpow_product]

theorem derivative_independent (δ t : ℝ) (k : ℤ) :
    deriv (PrimitiveCutoffs.vartheta δ) (t + k * (2 * Real.pi)) =
      deriv (PrimitiveCutoffs.vartheta δ) t := vartheta_deriv_representative δ t k

end TorusLiouvilleDynamicsConsumer

-- Fresh native per-root transitive audit of every imported project module,
-- every local/generated/private consumer declaration, and all nine supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.TorusLiouvilleDynamics.Z,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicComponents,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.angularTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.amplitude,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialCorrection,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicHamiltonian,
        `TorusLiouvilleDynamicsConsumer.emptySeed,
        `TorusLiouvilleDynamicsConsumer.frozenSeed,
        `TorusLiouvilleDynamicsConsumer.phase,
        `TorusLiouvilleDynamicsConsumer.nonzeroPoint] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mods := env.header.moduleNames.filter fun m =>
    m.toString.startsWith "ClusterSkeleton." || m.toString.startsWith "FsFltz."
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  unless mods.contains `ClusterSkeleton.TorusLiouvilleDynamics do
    throwError "Missing native dynamics module"
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
  logInfo m!"AUDITED project modules: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
