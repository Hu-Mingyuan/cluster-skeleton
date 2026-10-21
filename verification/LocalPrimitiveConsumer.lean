import ClusterSkeleton.LocalPrimitive
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry ClusterSkeleton
namespace LocalPrimitiveConsumer
open RegularCorrection PrimitiveLocalization
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Constructed coverage and every-chart smoothness, without supplied neighborhoods. -/
theorem actual_cover {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    (∀ p, IsOpen (LocalPrimitive.neighborhood S ε κ δ p)) ∧
    (∀ q : S.Point, ∃ p, q ∈ LocalPrimitive.neighborhood S ε κ δ p) ∧
    (∀ p, LocalFormGluing.LocallySmooth (SmoothAtlas.presentation S hdet).manifold
      (LocalPrimitive.neighborhood S ε κ δ p) (LocalPrimitive.eta S hdet ε κ δ p)) ∧
    (∀ p q, q ∈ LocalPrimitive.neighborhood S ε κ δ p → q ∈ initialTorus S →
      LocalPrimitive.eta S hdet ε κ δ p q = TorusCorrection.alpha S hdet ε κ δ q) :=
  LocalPrimitive.local_cover S hdet hε hκ hδ hδπ

/-- Evaluation on arbitrary native tangents, with every full-matrix contribution. -/
theorem arbitrary_tangent {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (ht : q ∈ initialTorus S) (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    SmoothManifold.evalOne (LocalPrimitive.eta S hdet ε κ δ p) q v =
      (∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖q.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j q v / q.a j).im) -
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) q v :=
  LocalPrimitive.evalOne_eta S hdet hε hκ hδ p q hq ht v

-- Reused explicit six-coordinate family from the accepted regular-correction consumer.
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


/-- The two vanishing coordinates have zero normalized partners as well. -/
theorem zero_normalized_partners (x t : ℝ) (i : tripleSeed.Mutable)
    (hi : (i : Fin 6) ∈ (boundaryPoint x t).zeroSet) :
    normalizedPartner (boundaryPoint x t) i = 0 := by
  rw [boundary_zeroSet] at hi
  rcases i with ⟨i,him⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;>
    simp [normalizedPartner, boundaryPoint, Seed.Point.b]

/-- The constructed neighborhood contains the actual simultaneous-zero point. -/
theorem simultaneous_domain (x t ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    boundaryPoint x t ∈ LocalPrimitive.neighborhood tripleSeed ε κ δ (boundaryPoint x t) :=
  LocalPrimitive.mem_neighborhood tripleSeed ε κ hδ _

/-- All chart centers are allowed, including charts not centered at the stratum point. -/
theorem simultaneous_all_charts (x t ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts tripleSeed triple_unimodular
    ∀ (a : tripleSeed.Point) (y : Model 12),
      y ∈ (chartAt (Model 12) a).target →
      (chartAt (Model 12) a).symm y ∈
        LocalPrimitive.neighborhood tripleSeed ε κ δ (boundaryPoint x t) →
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.formInChart a
        (LocalPrimitive.eta tripleSeed triple_unimodular ε κ δ (boundaryPoint x t))) y :=
  LocalPrimitive.locallySmooth_eta tripleSeed triple_unimodular ε κ hδ _

/-- The surviving differential remains in the local form at the two-zero stratum. -/
theorem simultaneous_value (x t ε κ δ : ℝ)
    (v : (SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.Tangent (boundaryPoint x t)) :
    SmoothManifold.evalOne
      (LocalPrimitive.eta tripleSeed triple_unimodular ε κ δ (boundaryPoint x t))
        (boundaryPoint x t) v =
      SmoothManifold.evalOne (PrimitiveResidual.residual tripleSeed triple_unimodular {0,2})
        (boundaryPoint x t) v -
      differentialCovector (SmoothAtlas.presentation tripleSeed triple_unimodular).manifold
        (regularH tripleSeed {0,2} ε κ δ) (boundaryPoint x t) v := by
  have h := LocalPrimitive.eta_zero_partners tripleSeed triple_unimodular ε κ δ
    (boundaryPoint x t) (zero_normalized_partners x t)
  simpa [SmoothManifold.evalOne, regularForm, covectorForm, boundary_zeroSet] using
    congrArg (fun f => f (fun _ => v)) h

/-- The torus agreement is exercised on a nonempty part of each boundary neighborhood. -/
theorem simultaneous_torus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (x t : ℝ) :
    (LocalPrimitive.neighborhood tripleSeed ε κ δ (boundaryPoint x t) ∩ initialTorus tripleSeed).Nonempty ∧
    ∀ q ∈ LocalPrimitive.neighborhood tripleSeed ε κ δ (boundaryPoint x t) ∩ initialTorus tripleSeed,
      LocalPrimitive.eta tripleSeed triple_unimodular ε κ δ (boundaryPoint x t) q =
        TorusCorrection.alpha tripleSeed triple_unimodular ε κ δ q := by
  refine ⟨?_, fun q hq => LocalPrimitive.eta_eq_torus tripleSeed triple_unimodular
    hε hκ hδ _ q hq.1 hq.2⟩
  exact (dense_initialTorus tripleSeed triple_unimodular).inter_open_nonempty _
    (LocalPrimitive.isOpen_neighborhood tripleSeed ε κ δ _) ⟨_, simultaneous_domain x t ε κ hδ⟩

/-- Empty I removes the singular block and leaves exactly beta-dH everywhere. -/
theorem empty_I (ε κ δ : ℝ) (p : S.Point) (hp : p.zeroSet = ∅) :
    LocalPrimitive.eta S hdet ε κ δ p = TorusCorrection.alpha S hdet ε κ δ := by
  have hr : PrimitiveResidual.residual S hdet ∅ = TorusPrimitive.beta S hdet := by
    funext q
    ext v
    simp [PrimitiveResidual.residual, TorusPrimitive.beta, covectorForm]
  have hb : NativeNodePrimitive.block S hdet κ p.zeroSet p.zeroSet_independent = 0 := by
    funext q
    ext v
    simp only [NativeNodePrimitive.block, covectorForm]
    change (∑ i : p.zeroSet, NativeNodePrimitive.lambda S hdet κ
      ⟨i.val, p.zeroSet_independent.1 i.property⟩ q) (v 0) = 0
    rw [ContinuousLinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact (Finset.notMem_empty i.val ((Finset.ext_iff.mp hp i.val).mp i.property)).elim
  simp only [LocalPrimitive.eta, hb, hp, add_zero,
    RegularCorrection.regularForm, RegularCorrection.regularH_empty, hr]
  rfl

/-- An inhabited dimension-zero instance, not an empty-carrier test. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew := by intro i; exact Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem empty_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem empty_point_neighborhood (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    emptySeed.unitPoint ∈ LocalPrimitive.neighborhood emptySeed ε κ δ emptySeed.unitPoint :=
  LocalPrimitive.mem_neighborhood emptySeed ε κ hδ _

theorem dimension_zero (ε κ δ : ℝ) :
    LocalPrimitive.eta emptySeed empty_unimodular ε κ δ emptySeed.unitPoint = 0 := by
  rw [empty_I emptySeed empty_unimodular ε κ δ _ (by ext i; exact Fin.elim0 i)]
  change TorusPrimitive.alpha emptySeed empty_unimodular (TorusCorrection.H emptySeed ε κ δ) = 0
  rw [TorusCorrection.H_empty_mutable emptySeed ε κ δ rfl, TorusPrimitive.alpha_zero]
  funext q
  ext v
  simp [TorusPrimitive.beta, covectorForm]

end LocalPrimitiveConsumer

-- Native transitive audit of the entire imported project closure, including
-- all private/generated roots and explicit attribution-sensitive supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.LocalPrimitive.neighborhood,
        `ClusterSkeleton.LocalPrimitive.eta,
        `ClusterSkeleton.RegularCorrection.surviving,
        `ClusterSkeleton.RegularCorrection.regularH,
        `ClusterSkeleton.RegularCorrection.regularForm,
        `ClusterSkeleton.RegularCorrection.singularH,
        `ClusterSkeleton.LocalFormGluing.LocallySmooth,
        `ClusterSkeleton.LocalFormGluing.glue,
        `ClusterSkeleton.NativeNodePrimitive.nodeMap,
        `ClusterSkeleton.NativeNodePrimitive.locus,
        `ClusterSkeleton.NativeNodePrimitive.nodeDifferential,
        `ClusterSkeleton.NativeNodePrimitive.lambda,
        `ClusterSkeleton.NativeNodePrimitive.block,
        `ClusterSkeleton.PrimitiveResidual.tau,
        `ClusterSkeleton.PrimitiveResidual.logRow,
        `ClusterSkeleton.PrimitiveResidual.residual,
        `ClusterSkeleton.PrimitiveLocalization.rowLog,
        `ClusterSkeleton.PrimitiveLocalization.angle,
        `ClusterSkeleton.PrimitiveLocalization.nodeLog,
        `ClusterSkeleton.PrimitiveLocalization.correction,
        `ClusterSkeleton.PrimitiveLocalization.affineCorrection,
        `ClusterSkeleton.PrimitiveLocalization.region,
        `ClusterSkeleton.PrimitiveLocalization.neighborhood,
        `ClusterSkeleton.NodePrimitiveCancellation.L,
        `ClusterSkeleton.NodePrimitiveCancellation.A,
        `ClusterSkeleton.NodePrimitiveCancellation.S,
        `ClusterSkeleton.NodePrimitiveCancellation.T,
        `ClusterSkeleton.NodePrimitiveCancellation.du,
        `ClusterSkeleton.NodePrimitiveCancellation.dL,
        `ClusterSkeleton.NodePrimitiveCancellation.dtheta,
        `ClusterSkeleton.NodePrimitiveCancellation.lambda,
        `ClusterSkeleton.NodePrimitiveCancellation.oneForm] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize equations for {name}"
  let env ← getEnv
  let mut report : Array String := #[]
  for mod in env.header.moduleNames do report := report.push s!"IMPORT {mod}"
  let required := #[`ClusterSkeleton.LocalPrimitive, `ClusterSkeleton.RegularCorrection,
    `ClusterSkeleton.LocalFormGluing, `ClusterSkeleton.NativeNodePrimitive, `ClusterSkeleton.PrimitiveResidual,
    `ClusterSkeleton.TorusPrimitive, `ClusterSkeleton.NodePrimitiveCancellation,
    `ClusterSkeleton.PrimitiveLocalization, `ClusterSkeleton.PrimitiveCutoffs,
    `ClusterSkeleton.DominanceCutoff]
  for mod in required do
    unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  let mods := env.header.moduleNames.filter fun m => m.toString.startsWith "ClusterSkeleton."
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  for name in supplements do
    unless env.contains name do throwError "Missing supplement {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut count := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => mods.contains env.header.moduleNames[i]!
    let named := name.toString.startsWith "ClusterSkeleton." ||
      name.toString.startsWith "_private.ClusterSkeleton."
    if defining || named || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      let origin := match idx with
        | some i => env.header.moduleNames[i]!.toString
        | none => "<consumer>"
      report := report.push s!"AUDITMODULE {name}: {origin}"
      report := report.push s!"AUDIT {name}: {axs}"
      logInfo m!"AUDIT {name}: {axs}"
      count := count + 1
  if count == 0 then throwError "Empty audit selection"
  report := report.push s!"AUDITED native combined/imported/local/supplement roots: {count}"
  let dir ← IO.getEnv "TMPDIR"
  let path := System.FilePath.mk (dir.getD "/tmp") / "local-primitive-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
