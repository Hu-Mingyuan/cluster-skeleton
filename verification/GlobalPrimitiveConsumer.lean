import ClusterSkeleton.GlobalPrimitive
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry ClusterSkeleton
namespace GlobalPrimitiveConsumer
open RegularCorrection PrimitiveLocalization
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Every member of the constructed cover, with an arbitrary point in it. -/
theorem arbitrary_restriction {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) :
    GlobalPrimitive.alpha S hdet ε κ hδ q = LocalPrimitive.eta S hdet ε κ δ p q :=
  GlobalPrimitive.alpha_eq_eta S hdet hε hκ hδ p q hq

theorem smooth {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm
      (GlobalPrimitive.alpha S hdet ε κ hδ) :=
  GlobalPrimitive.isSmoothForm_alpha S hdet hε hκ hδ

/-- Full matrix evaluation on any native tangent, including all frozen columns. -/
theorem arbitrary_torus_tangent {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (q : S.Point) (ht : q ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    SmoothManifold.evalOne (GlobalPrimitive.alpha S hdet ε κ hδ) q v =
      (∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖q.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j q v / q.a j).im) -
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) q v :=
  GlobalPrimitive.evalOne_alpha S hdet hε hκ hδ q ht v

/-- Equality of the actual derivative as a whole native form. -/
theorem whole_derivative {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (GlobalPrimitive.alpha S hdet ε κ hδ) = GlobalTwoForm.omega S hdet :=
  GlobalPrimitive.exteriorDerivative_alpha S hdet hε hκ hδ

/-- Kernel triviality at an arbitrary exchange point, with no torus premise. -/
theorem derivative_kernel {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (hv : ∀ w, SmoothManifold.evalTwo
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (GlobalPrimitive.alpha S hdet ε κ hδ)) p v w = 0) : v = 0 :=
  GlobalPrimitive.nondegenerate_exteriorDerivative_alpha S hdet hε hκ hδ p v hv

/-- Arbitrary subordinate choices produce the same form. -/
theorem selection_independent {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (select : S.Point → S.Point)
    (hs : ∀ q, q ∈ LocalPrimitive.neighborhood S ε κ δ (select q)) :
    GlobalPrimitive.alpha S hdet ε κ hδ = fun q => LocalPrimitive.eta S hdet ε κ δ (select q) q :=
  GlobalPrimitive.alpha_eq_selection S hdet hε hκ hδ select hs

/-- A competing globally smooth torus expression is uniquely determined. -/
theorem torus_uniqueness {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (theta : (SmoothAtlas.presentation S hdet).manifold.Form 1)
    (hs : (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta)
    (ht : ∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p) :
    theta = GlobalPrimitive.alpha S hdet ε κ hδ :=
  GlobalPrimitive.eq_alpha_of_torus S hdet hε hκ hδ hs ht

/-- Existential packaging supplies both admissible parameters and the native form. -/
theorem concrete_existence :
    ∃ (ε κ δ : ℝ) (theta : (SmoothAtlas.presentation S hdet).manifold.Form 1),
      0 < ε ∧ 2*ε+1 ≤ κ ∧ 0 < δ ∧ δ < Real.pi ∧
      (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta ∧
      (∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p) ∧
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta = GlobalTwoForm.omega S hdet ∧
      (∀ p, (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
        ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta) p) :=
  GlobalPrimitive.exists_global_primitive S hdet

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

/-- An inhabited dimension-zero instance, not an empty-carrier test. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew := by intro i; exact Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem empty_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

/-- The actual global form retains the surviving correction at the two-zero stratum. -/
theorem simultaneous_value (x t : ℝ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    (v : (SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.Tangent (boundaryPoint x t)) :
    SmoothManifold.evalOne (GlobalPrimitive.alpha tripleSeed triple_unimodular ε κ hδ)
      (boundaryPoint x t) v =
      SmoothManifold.evalOne (PrimitiveResidual.residual tripleSeed triple_unimodular {0,2})
        (boundaryPoint x t) v -
      differentialCovector (SmoothAtlas.presentation tripleSeed triple_unimodular).manifold
        (regularH tripleSeed {0,2} ε κ δ) (boundaryPoint x t) v := by
  have hl := GlobalPrimitive.alpha_eq_eta tripleSeed triple_unimodular hε hκ hδ
    (boundaryPoint x t) (boundaryPoint x t)
    (LocalPrimitive.mem_neighborhood tripleSeed ε κ hδ _)
  have hz := LocalPrimitive.eta_zero_partners tripleSeed triple_unimodular ε κ δ
    (boundaryPoint x t) (zero_normalized_partners x t)
  have h := hl.trans hz
  simpa [SmoothManifold.evalOne, regularForm, covectorForm, boundary_zeroSet] using
    congrArg (fun f => f (fun _ => v)) h

/-- Whole-form derivative identity evaluated at a simultaneous-zero point. -/
theorem simultaneous_derivative (x t : ℝ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    (v w : (SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.Tangent (boundaryPoint x t)) :
    SmoothManifold.evalTwo
      ((SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.exteriorDerivative
        (GlobalPrimitive.alpha tripleSeed triple_unimodular ε κ hδ)) (boundaryPoint x t) v w =
    SmoothManifold.evalTwo (GlobalTwoForm.omega tripleSeed triple_unimodular) (boundaryPoint x t) v w := by
  rw [GlobalPrimitive.exteriorDerivative_alpha tripleSeed triple_unimodular hε hκ hδ]

theorem simultaneous_nondegenerate (x t : ℝ) :
    (SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.Nondegenerate
      ((SmoothAtlas.presentation tripleSeed triple_unimodular).manifold.exteriorDerivative
        (GlobalPrimitive.alpha tripleSeed triple_unimodular 1 3
          (show 0 < Real.pi / 2 by positivity))) (boundaryPoint x t) :=
  GlobalPrimitive.nondegenerate_exteriorDerivative_alpha tripleSeed triple_unimodular
    (by norm_num) (by norm_num) (by positivity) _

/-- Empty mutable set leaves the full frozen torus and its native beta. -/
theorem empty_mutable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (hM : S.mutable = ∅) :
    GlobalPrimitive.alpha S hdet ε κ hδ = TorusPrimitive.beta S hdet := by
  have ht (p : S.Point) : p ∈ initialTorus S := by
    intro i
    exact p.frozen_ne_zero i (by simp [hM])
  have he : GlobalPrimitive.alpha S hdet ε κ hδ = TorusCorrection.alpha S hdet ε κ δ :=
    funext (fun p => GlobalPrimitive.alpha_eq_torus S hdet hε hκ hδ p (ht p))
  rw [he]
  change TorusPrimitive.alpha S hdet (TorusCorrection.H S ε κ δ) = _
  rw [TorusCorrection.H_empty_mutable S ε κ δ hM, TorusPrimitive.alpha_zero]

/-- Empty zero-index cover member is exercised at every torus center. -/
theorem empty_zero_index {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) :
    p.zeroSet = ∅ ∧ ∀ q ∈ LocalPrimitive.neighborhood S ε κ δ p,
      GlobalPrimitive.alpha S hdet ε κ hδ q = LocalPrimitive.eta S hdet ε κ δ p q := by
  refine ⟨?_, fun q hq => GlobalPrimitive.alpha_eq_eta S hdet hε hκ hδ p q hq⟩
  ext i
  simp [Seed.Point.mem_zeroSet, hp i]

theorem dimension_zero_inhabited : Nonempty emptySeed.Point := ⟨emptySeed.unitPoint⟩

theorem dimension_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    GlobalPrimitive.alpha emptySeed empty_unimodular ε κ hδ = 0 := by
  rw [empty_mutable emptySeed empty_unimodular hε hκ hδ rfl]
  funext q
  ext v
  simp [TorusPrimitive.beta, covectorForm]

theorem dimension_zero_derivative :
    (SmoothAtlas.presentation emptySeed empty_unimodular).manifold.exteriorDerivative
      (GlobalPrimitive.alpha emptySeed empty_unimodular 1 3
        (show 0 < Real.pi / 2 by positivity)) = GlobalTwoForm.omega emptySeed empty_unimodular :=
  GlobalPrimitive.exteriorDerivative_alpha emptySeed empty_unimodular
    (by norm_num) (by norm_num) (by positivity)

theorem dimension_zero_nondegenerate :
    (SmoothAtlas.presentation emptySeed empty_unimodular).manifold.Nondegenerate
      ((SmoothAtlas.presentation emptySeed empty_unimodular).manifold.exteriorDerivative
        (GlobalPrimitive.alpha emptySeed empty_unimodular 1 3
          (show 0 < Real.pi / 2 by positivity))) emptySeed.unitPoint :=
  GlobalPrimitive.nondegenerate_exteriorDerivative_alpha emptySeed empty_unimodular
    (by norm_num) (by norm_num) (by positivity) _

end GlobalPrimitiveConsumer

-- Native transitive audit of the entire imported project closure, including
-- all private/generated roots and explicit attribution-sensitive supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`GlobalPrimitiveConsumer.tripleSeed, `GlobalPrimitiveConsumer.boundaryPoint,
        `GlobalPrimitiveConsumer.survivor, `GlobalPrimitiveConsumer.emptySeed,
        `ClusterSkeleton.GlobalPrimitive.alpha,
        `ClusterSkeleton.Seed.Independent,
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
  let required := #[`ClusterSkeleton.GlobalPrimitive, `ClusterSkeleton.GlobalSymplectic,
    `ClusterSkeleton.LocalPrimitive, `ClusterSkeleton.RegularCorrection,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "global-primitive-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
