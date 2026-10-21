import ClusterSkeleton.BoundaryTangency
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry BoundaryTangency

namespace BoundaryTangencyConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Literal native derivatives, on the required open set and full admissible regime. -/
theorem generic_local_native {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ)
      (fun r : S.Point => Complex.log (1 - r.a i * normalizedPartner r i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) = Complex.log (1 - q.a i * normalizedPartner q i) ∧
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ)
      (fun r : S.Point => r.a i * normalizedPartner r i) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
        (q.a i * normalizedPartner q i - 1) * Complex.log (1 - q.a i * normalizedPartner q i) ∧
    (q.a i ≠ 0 → (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun r => Real.log ‖r.a i‖) q (GlobalLiouvilleField.Z S hdet ε κ hδ q) = -κ) :=
  ⟨nodeLog_drift S hdet hε hκ hδ p q hq i hi,
    nodeProduct_drift S hdet hε hκ hδ p q hq i hi,
    deep_radius S hdet hε hκ hδ p q hq i hi⟩

theorem local_smoothness {ε κ δ : ℝ} (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞
      (fun r => Complex.log (1 - r.a i * normalizedPartner r i)) q ∧
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞
      (fun r => r.a i * normalizedPartner r i) q :=
  ⟨nodeLog_smooth S hdet p i hi q hq,
    nodeProduct_smooth S hdet p.zeroSet_independent i hi q hq.2.1⟩

theorem arbitrary_point_native_tangency {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : Fin d) (ha : p.a i = 0) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) (fun r : S.Point => r.a i) p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 :=
  coordinate_tangent S hdet hε hκ hδ p i ha

/-- The continuous approximation really fixes the complete original coordinate vector. -/
theorem same_stratum_approximation (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (i : S.Mutable) (ha : p.a i = 0) :
    Continuous (boundaryPerturb S p i ha) ∧ boundaryPerturb S p i ha 0 = p ∧
    (∀ t, (boundaryPerturb S p i ha t).a = p.a ∧
      (boundaryPerturb S p i ha t).zeroSet = p.zeroSet ∧
      normalizedPartner (boundaryPerturb S p i ha t) i = normalizedPartner p i + t) ∧
    (∀ᶠ t in 𝓝 (0 : ℂ), boundaryPerturb S p i ha t ∈ LocalPrimitive.neighborhood S ε κ δ p) :=
  ⟨continuous_boundaryPerturb S p i ha, boundaryPerturb_zero S p i ha,
    fun t => ⟨rfl, rfl, boundaryPerturb_partner S p i ha t⟩,
    boundaryPerturb_eventually_mem S ε κ hδ p i ha⟩

def boundaryPoint (w : ℂ) : Examples.a2Seed.Point :=
  ⟨(![0,-1], fun j => if (j : Fin 2) = 0 then w else -1), by
    constructor
    · intro j
      rcases j with ⟨j,hj⟩
      fin_cases j <;> norm_num [Seed.positiveMonomial, Seed.negativeMonomial,
        Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]
    · intro j hj
      simp [Examples.a2Seed] at hj⟩

theorem boundary_coordinates (w : ℂ) :
    (boundaryPoint w).a 0 = 0 ∧ (boundaryPoint w).a 1 = -1 ∧
      (boundaryPoint w).b ⟨0, by simp [Examples.a2Seed]⟩ = w := by
  simp [boundaryPoint, Seed.Point.a, Seed.Point.b]


def pairSeed : Seed 4 where
  B := !![0,1,0,0; -1,0,0,0; 0,0,0,1; 0,0,-1,0]
  mutable := {0,2}
  skew := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  acyclic := by
    refine ⟨fun i => Acc.intro i fun j h => ?_⟩
    have hi := i.property
    have hj := j.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> simp [hi, hj] at h

theorem pair_unimodular : pairSeed.Unimodular := by
  norm_num [Seed.Unimodular, pairSeed, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]


def frozenSeed : Seed 2 where
  B := Examples.a2Matrix
  mutable := ∅
  skew := Examples.a2Seed.skew
  acyclic := ⟨fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

theorem frozen_unimodular : frozenSeed.Unimodular := Examples.a2Seed_unimodular

def frozenPoint (t : ℝ) : frozenSeed.Point :=
  pointOfCoordinateTorus frozenSeed (fun j =>
    if j = 0 then ⟨(Real.exp t : ℂ), by exact_mod_cast Real.exp_ne_zero t⟩ else ⟨1, one_ne_zero⟩)


def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem empty_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty


theorem a2_arbitrary_partner (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    normalizedPartner (boundaryPoint w) ⟨0, by simp [Examples.a2Seed]⟩ = w ∧
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).coordinateDifferential 0
      (boundaryPoint w) (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular
        ε κ hδ (boundaryPoint w)) = 0 := by
  constructor
  · simp [normalizedPartner, boundaryPoint, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]
  · exact coordinate_tangent _ _ hε hκ hδ _ 0 (boundary_coordinates w).1

theorem a2_zero_partner {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    normalizedPartner (boundaryPoint 0) ⟨0, by simp [Examples.a2Seed]⟩ = 0 ∧
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).coordinateDifferential 0
      (boundaryPoint 0) (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular
        ε κ hδ (boundaryPoint 0)) = 0 := a2_arbitrary_partner 0 hε hκ hδ

/-- Two simultaneous zeros, with both complex partners completely free. -/
def doubleBoundary (u v : ℂ) : pairSeed.Point :=
  ⟨(![0,-1,0,-1], fun j => if (j : Fin 4) = 0 then u else v), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem simultaneous_zero_tangencies (u v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation pairSeed pair_unimodular).coordinateDifferential 0 (doubleBoundary u v)
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (doubleBoundary u v)) = 0 ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).coordinateDifferential 2 (doubleBoundary u v)
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (doubleBoundary u v)) = 0 :=
  ⟨coordinate_tangent _ _ hε hκ hδ _ _ rfl, coordinate_tangent _ _ hε hκ hδ _ _ rfl⟩

theorem double_zero_partners :
    normalizedPartner (doubleBoundary 0 0) ⟨0, by simp [pairSeed]⟩ = 0 ∧
    normalizedPartner (doubleBoundary 0 0) ⟨2, by simp [pairSeed]⟩ = 0 := by
  simp [normalizedPartner, doubleBoundary, Seed.Point.b]

/-- Selected nonzero radius with a different mutable coordinate still zero. -/
def selectedBoundary (z v : ℂ) : pairSeed.Point :=
  ⟨(![z,-1,0,-1], fun j => if (j : Fin 4) = 0 then 0 else v), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem selected_with_other_zero (z v : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    (hq : selectedBoundary z v ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary 0 v)) :
    selectedBoundary z v ∉ initialTorus pairSeed ∧
    GlobalLiouvilleField.L pairSeed pair_unimodular ε κ hδ (selectedBoundary z v) 0 = -κ := by
  refine ⟨fun h => h 2 rfl, ?_⟩
  exact deep_radius pairSeed pair_unimodular hε hκ hδ _ _ hq
    ⟨0, by simp [pairSeed]⟩ (by simp [Seed.Point.mem_zeroSet, pairSeed, doubleBoundary, Seed.Point.a]) hz

theorem continuous_selectedBoundary (v : ℂ) : Continuous (fun z => selectedBoundary z v) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    fin_cases j <;> fun_prop
  · exact continuous_const

/-- Nonvacuous selected deep-radius examples arbitrarily near the double-zero center. -/
theorem selected_deep_radius_eventually (v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ selectedBoundary z v ∉ initialTorus pairSeed ∧
      GlobalLiouvilleField.L pairSeed pair_unimodular ε κ hδ (selectedBoundary z v) 0 = -κ := by
  have hc : Tendsto (fun z => selectedBoundary z v) (𝓝 0) (𝓝 (doubleBoundary 0 v)) :=
    (continuous_selectedBoundary v).continuousAt
  have hm := hc.eventually ((LocalPrimitive.isOpen_neighborhood pairSeed ε κ δ
    (doubleBoundary 0 v)).mem_nhds (LocalPrimitive.mem_neighborhood pairSeed ε κ hδ _))
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
  exact ⟨hn, selected_with_other_zero z v hn hε hκ hδ hz⟩

def variableFrozenBoundary (w z : ℂ) (hz : z ≠ 0) : pairSeed.Point :=
  ⟨(![0,-1,1,z], fun j => if (j : Fin 4) = 0 then w else z + 1), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem variable_frozen_tangency (w z : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (variableFrozenBoundary w z hz).a 3 = z ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).coordinateDifferential 0
      (variableFrozenBoundary w z hz) (GlobalLiouvilleField.Z pairSeed pair_unimodular
        ε κ hδ (variableFrozenBoundary w z hz)) = 0 ∧
    GlobalLiouvilleField.L pairSeed pair_unimodular ε κ hδ (variableFrozenBoundary w z hz) 3 =
      Real.log ‖z‖ :=
  ⟨rfl, coordinate_tangent _ _ hε hκ hδ _ _ rfl,
    GlobalLiouvilleField.frozen_radial_equation _ _ hε hκ hδ _ _ (by simp [pairSeed])⟩

theorem empty_mutable_has_no_zero (hM : S.mutable = ∅) (p : S.Point) : p.zeroSet = ∅ := by
  ext i
  simp [hM]

theorem frozen_variable (t : ℝ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (frozenPoint t).zeroSet = ∅ ∧
    GlobalLiouvilleField.L frozenSeed frozen_unimodular ε κ hδ (frozenPoint t) 0 = t := by
  refine ⟨empty_mutable_has_no_zero frozenSeed rfl _, ?_⟩
  rw [GlobalLiouvilleField.frozen_radial_equation _ _ hε hκ hδ _ _ (by simp [frozenSeed])]
  simp [GlobalLiouvilleField.A, frozenPoint, Real.log_exp]

theorem inhabited_dimension_zero (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty emptySeed.Point ∧ emptySeed.unitPoint.zeroSet = ∅ ∧
    GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ emptySeed.unitPoint = 0 := by
  refine ⟨⟨emptySeed.unitPoint⟩, empty_mutable_has_no_zero emptySeed rfl _, ?_⟩
  apply PiLp.ext
  intro i
  exact Fin.elim0 i

end BoundaryTangencyConsumer

-- Native transitive audit of the entire imported project closure, including
-- all private/generated roots and explicit attribution-sensitive supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`BoundaryTangencyConsumer.boundaryPoint, `BoundaryTangencyConsumer.frozenSeed,
        `BoundaryTangencyConsumer.frozenPoint, `BoundaryTangencyConsumer.emptySeed,
        `BoundaryTangencyConsumer.pairSeed, `BoundaryTangencyConsumer.doubleBoundary,
        `BoundaryTangencyConsumer.selectedBoundary, `BoundaryTangencyConsumer.variableFrozenBoundary,
        `ClusterSkeleton.BoundaryTangency.nodeProduct, `ClusterSkeleton.BoundaryTangency.drift,
        `ClusterSkeleton.BoundaryTangency.boundaryPerturb,
        `ClusterSkeleton.GlobalLiouvilleField.Z,
        `ClusterSkeleton.GlobalLiouvilleField.logarithmicComponents,
        `ClusterSkeleton.GlobalLiouvilleField.A, `ClusterSkeleton.GlobalLiouvilleField.L,
        `ClusterSkeleton.GlobalLiouvilleField.nonzeroLocus,
        `ClusterSkeleton.TorusLiouvilleDynamics.Z,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicComponents,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.angularTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.amplitude,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialCorrection,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicHamiltonian,
        `ClusterSkeleton.GlobalPrimitive.alpha,
        `ClusterSkeleton.PrimitiveCutoffs.angularRadius,
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
  let required := #[`ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
    `ClusterSkeleton.TorusLiouvilleDynamics, `FsFltz.Geometry.SmoothLiouville,
    `FsFltz.Geometry.VectorFieldBridge, `ClusterSkeleton.GlobalPrimitive, `ClusterSkeleton.GlobalSymplectic,
    `ClusterSkeleton.LocalPrimitive, `ClusterSkeleton.RegularCorrection,
    `ClusterSkeleton.LocalFormGluing, `ClusterSkeleton.NativeNodePrimitive, `ClusterSkeleton.PrimitiveResidual,
    `ClusterSkeleton.TorusPrimitive, `ClusterSkeleton.NodePrimitiveCancellation,
    `ClusterSkeleton.PrimitiveLocalization, `ClusterSkeleton.PrimitiveCutoffs,
    `ClusterSkeleton.DominanceCutoff]
  for mod in required do
    unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  let mods := env.header.moduleNames.filter fun m => m.toString.startsWith "ClusterSkeleton." || m.toString.startsWith "FsFltz."
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
      name.toString.startsWith "_private.ClusterSkeleton." ||
      name.toString.startsWith "FsFltz." || name.toString.startsWith "_private.FsFltz."
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "boundary-tangency-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
