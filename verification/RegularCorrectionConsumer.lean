import ClusterSkeleton.RegularCorrection
import ClusterSkeleton.Examples.A2

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry
namespace ClusterSkeleton.RegularCorrectionConsumer
open RegularCorrection PrimitiveLocalization
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

theorem boundary_smooth (I : Finset (Fin d)) (hI : S.Independent I)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (regularH S I ε κ δ)
      (candidateChartLocus S I) := contMDiffOn_regularH S hdet I hI ε κ hδ

theorem all_charts (I : Finset (Fin d)) (hI : S.Independent I)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d)), y ∈ (chartAt (Model (2*d)) a).target →
      (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I →
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (regularForm S hdet I ε κ δ)) y := regularForm_smooth S hdet I hI ε κ hδ

theorem arbitrary_tangents {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    (p q : S.Point) (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold (TorusCorrection.H S ε κ δ) q v =
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => singularH p.zeroSet κ r + regularH S p.zeroSet ε κ δ r) q v :=
  congrArg (fun L => L v) (differential_H_split hdet hε hκ hδ hq ht)

/-- Three independent mutable vertices paired with three variable frozen ones. -/
def tripleSeed : Seed 6 where
  B := !![0,1,0,0,0,0; -1,0,0,0,0,0; 0,0,0,1,0,0;
    0,0,-1,0,0,0; 0,0,0,0,0,1; 0,0,0,0,-1,0]
  mutable := {0,2,4}
  skew := by decide
  acyclic := by
    refine ⟨fun i => Acc.intro i fun j h => ?_⟩
    have hi := i.property
    have hj := j.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
      simp [hi, hj] at h

theorem triple_unimodular : tripleSeed.Unimodular := by
  norm_num [Seed.Unimodular, tripleSeed, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]

/-- A two-zero stratum with a variable surviving radius and frozen phase. -/
def boundaryPoint (x t : ℝ) : tripleSeed.Point :=
  ⟨(![0, -1, 0, -1, (Real.exp x : ℂ), -Complex.exp ((t : ℂ) * Complex.I)],
    fun j => if (j : Fin 6) = 4 then
      (1 - Complex.exp ((t : ℂ) * Complex.I)) / (Real.exp x : ℂ) else 0), by
    constructor
    · intro j
      have hj := j.property
      simp only [tripleSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj | hj
      · simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, tripleSeed, Fin.prod_univ_succ]
      · simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, tripleSeed, Fin.prod_univ_succ]
      · simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, tripleSeed, Fin.prod_univ_succ,
          (show (Real.exp x : ℂ) ≠ 0 by exact_mod_cast Real.exp_ne_zero x)]
        field_simp [Complex.exp_ne_zero] <;> ring
    · intro f hf
      fin_cases f <;> simp_all [tripleSeed, Real.exp_ne_zero, Complex.exp_ne_zero]⟩

theorem boundary_zeroSet (x t : ℝ) : (boundaryPoint x t).zeroSet = {0,2} := by
  ext i
  fin_cases i <;> simp [Seed.Point.mem_zeroSet, boundaryPoint, Seed.Point.a, tripleSeed,
    (show (Real.exp x : ℂ) ≠ 0 by exact_mod_cast Real.exp_ne_zero x)]

theorem two_zero_independent : tripleSeed.Independent {0,2} := by
  norm_num [Seed.Independent, tripleSeed, Finset.subset_iff]

theorem boundary_in_locus (x t : ℝ) : boundaryPoint x t ∈ candidateChartLocus tripleSeed {0,2} := by
  rw [← boundary_zeroSet x t]
  exact mem_zero_locus _

def survivor : tripleSeed.Mutable := ⟨4, by decide⟩

theorem surviving_triple : surviving tripleSeed {0,2} = {survivor} := by
  ext j
  obtain ⟨j,hj⟩ := j
  fin_cases j <;> simp_all [surviving, tripleSeed, survivor]

theorem boundary_row (x t : ℝ) : PrimitiveLocalization.rowLog (boundaryPoint x t) 4 = 0 := by
  simp [PrimitiveLocalization.rowLog, DominanceCutoff.logNorms, boundaryPoint, Seed.Point.a,
    tripleSeed, Fin.sum_univ_succ, Complex.norm_exp]

theorem boundary_character (x t : ℝ) : exchangeCharacter (boundaryPoint x t) 4 =
    -Complex.exp ((t : ℂ) * Complex.I) := by
  simp [exchangeCharacter_eq_zpow_product, boundaryPoint, Seed.Point.a, tripleSeed, Fin.prod_univ_succ]

theorem boundary_regular (x t : ℝ) :
    regularH tripleSeed {0,2} 1 3 (Real.pi / 2) (boundaryPoint x t) =
    PrimitiveCutoffs.radial 1 3 x * PrimitiveCutoffs.vartheta (Real.pi / 2)
      (Complex.arg (Complex.exp ((t : ℂ) * Complex.I))) := by
  have hd : DominanceCutoff.mutableNeighbors tripleSeed 4 = ∅ := by decide
  simp only [regularH, surviving_triple, Finset.sum_singleton, correction, survivor]
  rw [DominanceCutoff.dominance_of_no_neighbors _ _ _ _ hd]
  change PrimitiveCutoffs.radial 1 3 (Real.log ‖(Real.exp x : ℂ)‖) * 1 *
    PrimitiveCutoffs.rho (PrimitiveLocalization.rowLog (boundaryPoint x t) 4) *
    PrimitiveCutoffs.vartheta (Real.pi / 2) (angle (boundaryPoint x t) 4) = _
  rw [boundary_row, PrimitiveCutoffs.rho_eq_one (by norm_num)]
  simp [angle, boundary_character, Complex.log_im, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos x), Real.log_exp]

theorem phase_value :
    regularH tripleSeed {0,2} 1 3 (Real.pi / 2) (boundaryPoint (-5) (Real.pi / 8)) =
      -2 * (Real.pi / 8) := by
  rw [boundary_regular]
  have hr : PrimitiveCutoffs.radial 1 3 (-5) = -2 := by
    convert PrimitiveCutoffs.radial_tail (ε := 1) (κ := 3) (A := -5) (by norm_num)
      (by norm_num [PrimitiveCutoffs.radialLength]) using 1 <;> norm_num
  rw [hr, Complex.arg_exp_mul_I]
  have ht : toIocMod Real.two_pi_pos (-(Real.pi)) (Real.pi / 8) = Real.pi / 8 := by
    apply (toIocMod_eq_self Real.two_pi_pos).mpr
    constructor <;> linarith [Real.pi_pos]
  rw [ht]
  congr 1
  apply PrimitiveCutoffs.vartheta_eq_self (by positivity)
  norm_num [PrimitiveCutoffs.angularRadius, abs_of_pos Real.pi_pos, abs_div, div_div]

theorem zero_phase_value :
    regularH tripleSeed {0,2} 1 3 (Real.pi / 2) (boundaryPoint (-5) 0) = 0 := by
  rw [boundary_regular]
  simp [PrimitiveCutoffs.vartheta]

/-- Two genuine boundary points on the same simultaneous stratum distinguish regularH. -/
theorem surviving_nonconstant :
    ∃ p q : tripleSeed.Point, p.zeroSet = {0,2} ∧ q.zeroSet = {0,2} ∧
      p.a 5 ≠ q.a 5 ∧
      regularH tripleSeed {0,2} 1 3 (Real.pi / 2) p ≠
        regularH tripleSeed {0,2} 1 3 (Real.pi / 2) q := by
  refine ⟨boundaryPoint (-5) (Real.pi / 8), boundaryPoint (-5) 0,
    boundary_zeroSet _ _, boundary_zeroSet _ _, ?_, ?_⟩
  · intro h
    have hc : exchangeCharacter (boundaryPoint (-5) (Real.pi / 8)) 4 =
        exchangeCharacter (boundaryPoint (-5) 0) 4 := by
      rw [boundary_character, boundary_character]
      exact h
    have hv := congrArg (fun z : ℂ => PrimitiveCutoffs.radial 1 3 (-5) *
      PrimitiveCutoffs.vartheta (Real.pi / 2) (Complex.arg (-z))) hc
    have he : regularH tripleSeed {0,2} 1 3 (Real.pi / 2) (boundaryPoint (-5) (Real.pi / 8)) =
        regularH tripleSeed {0,2} 1 3 (Real.pi / 2) (boundaryPoint (-5) 0) := by
      simpa [boundary_regular, boundary_character] using hv
    rw [phase_value, zero_phase_value] at he
    linarith [Real.pi_pos]
  · rw [phase_value, zero_phase_value]
    exact mul_ne_zero (by norm_num) (by positivity)

theorem empty_I (ε κ δ : ℝ) : regularH S ∅ ε κ δ = TorusCorrection.H S ε κ δ :=
  regularH_empty ε κ δ

theorem empty_surviving (ε κ δ : ℝ) :
    regularH tripleSeed {0,2,4} ε κ δ = fun _ => 0 := by
  apply regularH_no_survivors
  ext j
  obtain ⟨j,hj⟩ := j
  fin_cases j <;> simp_all [surviving, tripleSeed]

theorem simultaneous_boundary_smooth (x t ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts tripleSeed triple_unimodular
    ContMDiffAt 𝓘(ℝ, Model 12) 𝓘(ℝ, ℝ) ∞ (regularH tripleSeed {0,2} ε κ δ)
      (boundaryPoint x t) := by
  letI := SmoothAtlas.charts tripleSeed triple_unimodular
  exact (contMDiffOn_regularH tripleSeed triple_unimodular {0,2}
    two_zero_independent ε κ hδ).contMDiffAt
      ((isOpen_candidateChartLocus tripleSeed {0,2}).mem_nhds (boundary_in_locus x t))

theorem simultaneous_germ (x t : ℝ) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    (neighborhood ε κ δ (boundaryPoint x t) ∩ initialTorus tripleSeed).Nonempty ∧
    ∀ q ∈ neighborhood ε κ δ (boundaryPoint x t) ∩ initialTorus tripleSeed,
      TorusCorrection.H tripleSeed ε κ δ =ᶠ[𝓝 q]
        fun r => singularH {0,2} κ r + regularH tripleSeed {0,2} ε κ δ r := by
  refine ⟨?_, ?_⟩
  · exact (dense_initialTorus tripleSeed triple_unimodular).inter_open_nonempty _
      (isOpen_neighborhood ε κ δ _) ⟨_, mem_neighborhood ε κ hδ _⟩
  · intro q hq
    simpa only [boundary_zeroSet] using H_eventuallyEq hε hκ hδ hq.1 hq.2

end ClusterSkeleton.RegularCorrectionConsumer


-- Native per-root audit of the exact combined new/borrowed scalar closure.
-- Full unchanged inherited evidence is source-checked and carried in the delivery.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.RegularCorrection.surviving,
        `ClusterSkeleton.RegularCorrection.regularH,
        `ClusterSkeleton.RegularCorrection.regularForm,
        `ClusterSkeleton.RegularCorrection.singularH] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mods := #[`ClusterSkeleton.PrimitiveCutoffs, `ClusterSkeleton.DominanceCutoff,
    `ClusterSkeleton.TorusPrimitive, `ClusterSkeleton.TorusCorrection,
    `ClusterSkeleton.PrimitiveLocalization, `ClusterSkeleton.RegularCorrection]
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
