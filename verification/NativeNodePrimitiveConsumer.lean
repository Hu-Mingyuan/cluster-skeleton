import ClusterSkeleton.NativeNodePrimitive
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Topology BigOperators
open Set FsFltz.Geometry ClusterSkeleton ClusterSkeleton.NativeNodePrimitive
namespace NativeNodePrimitiveConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

theorem open_domain (I : Finset (Fin d)) (hI : S.Independent I) :
    IsOpen (locus S I) := isOpen_locus S I hI

theorem smooth_every_chart (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d)),
      y ∈ (chartAt (Model (2*d)) a).target →
      (chartAt (Model (2*d)) a).symm y ∈ locus S I →
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (block S hdet κ I hI)) y := contDiffAt_block_inChart S hdet κ I hI

theorem arbitrary_boundary_tangent (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I)
    (q : S.Point) (hq : q ∈ candidateChartLocus S I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (ha : q.a i = 0)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    lambda S hdet κ i q v = (1+κ) *
      (normalizedPartner q i * (SmoothAtlas.presentation S hdet).coordinateDifferential i q v).im :=
  lambda_boundary S hdet κ hI i hi q hq ha v

theorem empty_block (κ : ℝ) (hI : S.Independent ∅) :
    block S hdet κ ∅ hI = 0 := block_empty S hdet κ hI

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

/-- Frozen values are arbitrary nonzero variables throughout this actual family. -/
def family (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) : fourSeed.Point :=
  ⟨(![(s + 1) / Complex.I, s, (t + 1) / Complex.I, t], fun _ => Complex.I), by
    constructor
    · rintro ⟨i, hi⟩
      change i ∈ ({0,2} : Finset (Fin 4)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [fourSeed, fourMatrix, Seed.positiveMonomial,
        Seed.negativeMonomial, Fin.prod_univ_succ, mul_assoc]
    · intro f hf
      fin_cases f <;> simp_all [fourSeed]⟩

theorem family_frozen (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    (family s t hs ht).a 1 = s ∧ (family s t hs ht).a 3 = t := by
  constructor <;> rfl

theorem family_locus (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    family s t hs ht ∈ candidateChartLocus fourSeed {0,2} := by
  intro j hj
  fin_cases j <;> simp_all [family, Seed.Point.a]

def boundary : fourSeed.Point := family (-1) (-1) (by norm_num) (by norm_num)

theorem boundary_zeros : boundary.a 0 = 0 ∧ boundary.a 2 = 0 := by
  simp [boundary, family, Seed.Point.a]

theorem boundary_partner (i : fourSeed.Mutable) : normalizedPartner boundary i = Complex.I := by
  rcases i with ⟨i,hi⟩
  change i ∈ ({0,2} : Finset (Fin 4)) at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;>
    simp [normalizedPartner, boundary, family, Seed.Point.a, Seed.Point.b,
      fourSeed, fourMatrix, Seed.negativeMonomial, Fin.prod_univ_succ]

theorem boundary_domain : boundary ∈ locus fourSeed {0,2} := by
  refine ⟨family_locus _ _ _ _, ?_⟩
  intro i hi
  have hz : boundary.a i = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · simpa [h] using boundary_zeros.1
    · simpa [h] using boundary_zeros.2
  change (boundary.a i, normalizedPartner boundary i) ∈ nodeLogDomain
  rw [hz]
  exact zero_mem_nodeLogDomain _

/-- Every native tangent direction at both simultaneous zeros is covered. -/
theorem simultaneous_boundary (κ : ℝ) (i : fourSeed.Mutable)
    (v : (SmoothAtlas.presentation fourSeed four_unimodular).manifold.Tangent boundary) :
    lambda fourSeed four_unimodular κ i boundary v = (1+κ) *
      (Complex.I * (SmoothAtlas.presentation fourSeed four_unimodular).coordinateDifferential i boundary v).im := by
  have hi : (i : Fin 4) ∈ ({0,2} : Finset (Fin 4)) := i.property
  have hz : boundary.a i = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · simpa [h] using boundary_zeros.1
    · simpa [h] using boundary_zeros.2
  rw [lambda_boundary fourSeed four_unimodular κ two_independent i hi boundary
    boundary_domain.1 hz v, boundary_partner]

/-- Existing native chart directions, with each node first component one. -/
def transverse (p : fourSeed.Point) :
    (SmoothAtlas.presentation fourSeed four_unimodular).manifold.Tangent p :=
  IndependentNodeChart.modelEquiv fourSeed (SmoothAtlas.chosenIndex fourSeed p).val
    four_unimodular (SmoothAtlas.chosenIndex fourSeed p).property
    (fun _ => (1,0), fun _ => 0)

/-- The prescribed tangent image is proved from the accepted chart formula. -/
theorem transverse_node (p : fourSeed.Point) (i : fourSeed.Mutable) (hz : p.a i = 0) :
    nodeDifferential fourSeed four_unimodular i p (transverse p) = (1,0) := by
  letI := SmoothAtlas.charts fourSeed four_unimodular
  letI := SmoothAtlas.smooth fourSeed four_unimodular
  let K := SmoothAtlas.chosenIndex fourSeed p
  have hi : (i : Fin 4) ∈ K.val := by
    by_contra hn
    exact SmoothAtlas.chosenIndex_mem fourSeed p i hn hz
  let e := IndependentNodeChart.modelEquiv fourSeed K.val four_unimodular K.property
  let F : Model 8 →L[ℝ] (ℂ × ℂ) :=
    ((ContinuousLinearMap.proj ⟨i.val, hi⟩).comp
      (ContinuousLinearMap.fst ℝ _ _)).comp e.symm.toContinuousLinearMap
  have he : F ∘ extChartAt 𝓘(ℝ, Model 8) p = nodeMap fourSeed i := by
    funext q
    change ((e.symm (e (IndependentNodeChart.ambientForward fourSeed K.val
      four_unimodular K.property q.val))).1 ⟨i.val, hi⟩) = _
    rw [e.symm_apply_apply]
    rfl
  have hc := mfderiv_comp p F.differentiableAt.mdifferentiableAt
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, Model 8)) (mem_chart_source _ _))
  rw [he, mfderiv_eq_fderiv, F.fderiv, mfderiv_extChartAt_self,
    ContinuousLinearMap.comp_id] at hc
  change (mfderiv 𝓘(ℝ, Model 8) 𝓘(ℝ, ℂ × ℂ) (nodeMap fourSeed i) p) (e _) = _
  rw [hc]
  change ((e.symm (e _)).1 ⟨i.val, hi⟩) = _
  rw [e.symm_apply_apply]

theorem positive_boundary_sign :
    lambda fourSeed four_unimodular 1 ⟨0, by decide⟩ boundary (transverse boundary) = 2 := by
  change NodePrimitiveCancellation.lambda 1 (nodeMap fourSeed ⟨0, by decide⟩ boundary)
    (nodeDifferential fourSeed four_unimodular ⟨0, by decide⟩ boundary (transverse boundary)) = 2
  rw [transverse_node boundary _ boundary_zeros.1]
  change NodePrimitiveCancellation.lambda 1 (boundary.a 0, normalizedPartner boundary _) (1,0) = 2
  rw [boundary_zeros.1, boundary_partner]
  exact NodePrimitiveCancellation.numerical_sign

/-- Arbitrary torus tangent directions test the complete native cancellation. -/
theorem torus_tangent (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I)
    (q : S.Point) (hq : q ∈ locus S I) (ht : q ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    SmoothManifold.evalOne (block S hdet κ I hI) q v =
      ∑ i : I, (Real.log ‖q.a i.val‖ * PrimitiveResidual.tau S hdet i.val q v -
        PrimitiveResidual.logRow S i.val q * TorusPrimitive.angleCovector S hdet i.val q v -
        differentialCovector (SmoothAtlas.presentation S hdet).manifold
          (fun r => (Real.log ‖r.a i.val‖ + κ) *
            (PrimitiveLocalization.nodeLog r ⟨i.val, hI.1 i.property⟩).im) q v) := by
  have h := congrArg (fun f => f (fun _ => v)) (block_torus S hdet κ I hI q hq ht)
  simpa [SmoothManifold.evalOne, covectorForm] using h

/-- Zero normalized partner is explicitly included for every native tangent. -/
theorem zero_partner (κ : ℝ) (I : Finset (Fin d)) (hI : S.Independent I)
    (q : S.Point) (hq : q ∈ candidateChartLocus S I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (ha : q.a i = 0)
    (hb : normalizedPartner q i = 0)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    lambda S hdet κ i q v = 0 := by
  rw [lambda_boundary S hdet κ hI i hi q hq ha v, hb]
  simp

/-- Both simultaneous zeros are inside the coefficient smoothness domain. -/
theorem smooth_boundary (κ : ℝ) :
    letI := SmoothAtlas.charts fourSeed four_unimodular
    ContDiffAt ℝ ∞ ((SmoothAtlas.presentation fourSeed four_unimodular).manifold.formInChart
      boundary (block fourSeed four_unimodular κ {0,2} two_independent))
      ((chartAt (Model 8) boundary) boundary) := by
  letI := SmoothAtlas.charts fourSeed four_unimodular
  apply contDiffAt_block_inChart
  · exact (chartAt (Model 8) boundary).map_source (mem_chart_source _ _)
  · rw [(chartAt (Model 8) boundary).left_inv (mem_chart_source _ _)]
    exact boundary_domain

/-- Empty I imposes precisely the actual initial torus, with no node restriction. -/
theorem empty_domain : locus S ∅ = initialTorus S := by
  ext q
  simp [locus, candidateChartLocus, initialTorus]

/-- An actual simultaneous zero point with zero normalized partners. -/
def zeroBoundary : fourSeed.Point :=
  ⟨(![0,-1,0,-1], fun _ => 0), by
    constructor
    · rintro ⟨i, hi⟩
      change i ∈ ({0,2} : Finset (Fin 4)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [fourSeed, fourMatrix, Seed.positiveMonomial,
        Seed.negativeMonomial, Fin.prod_univ_succ]
    · intro f hf
      fin_cases f <;> simp_all [fourSeed]⟩

theorem zeroBoundary_locus : zeroBoundary ∈ candidateChartLocus fourSeed {0,2} := by
  intro j hj
  fin_cases j <;> simp_all [zeroBoundary, Seed.Point.a]

theorem zeroBoundary_evaluation (κ : ℝ)
    (v : (SmoothAtlas.presentation fourSeed four_unimodular).manifold.Tangent zeroBoundary) :
    lambda fourSeed four_unimodular κ ⟨0, by decide⟩ zeroBoundary v = 0 := by
  apply zero_partner fourSeed four_unimodular κ {0,2} two_independent zeroBoundary
    zeroBoundary_locus ⟨0, by decide⟩ (by decide) rfl
  simp [normalizedPartner, zeroBoundary, Seed.Point.b]

/-- The frozen columns in the singular logarithmic row remain variable. -/
theorem variable_frozen_row (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    PrimitiveResidual.logRow fourSeed 0 (family s t hs ht) = Real.log ‖s‖ := by
  simp [PrimitiveResidual.logRow, fourSeed, fourMatrix, family, Seed.Point.a, Fin.sum_univ_succ]

end NativeNodePrimitiveConsumer

-- Native transitive audit of the entire imported project closure, including
-- all private/generated roots and explicit attribution-sensitive supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
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
  let required := #[`ClusterSkeleton.NativeNodePrimitive, `ClusterSkeleton.PrimitiveResidual,
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
      logInfo m!"AUDIT {name}: {axs}"
      count := count + 1
  if count == 0 then throwError "Empty audit selection"
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
