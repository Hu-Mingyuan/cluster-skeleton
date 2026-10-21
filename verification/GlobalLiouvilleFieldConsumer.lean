import ClusterSkeleton.GlobalLiouvilleField
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry GlobalLiouvilleField

namespace GlobalLiouvilleFieldConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Full admissible regime and arbitrary native tangent at every exchange point. -/
theorem global_contractions {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothVectorField (Z S hdet ε κ hδ) ∧
    SmoothManifold.evalTwo
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (GlobalPrimitive.alpha S hdet ε κ hδ)) p (Z S hdet ε κ hδ p) v =
      SmoothManifold.evalOne (GlobalPrimitive.alpha S hdet ε κ hδ) p v ∧
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p (Z S hdet ε κ hδ p) v =
      SmoothManifold.evalOne (GlobalPrimitive.alpha S hdet ε κ hδ) p v :=
  ⟨isSmoothVectorField_Z S hdet hε hκ hδ,
    contraction_exteriorDerivative S hdet hε hκ hδ p v,
    contraction_omega S hdet hε hκ hδ p v⟩

theorem torus_identification {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.liouvilleVector
      (GlobalPrimitive.alpha S hdet ε κ hδ) p = TorusLiouvilleDynamics.Z S hdet ε κ δ p :=
  Z_eq_torus S hdet hε hκ hδ p hp

theorem literal_mutable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) (hi : i ∈ S.mutable) :
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun q => Real.log ‖q.a i‖) p (Z S hdet ε κ hδ p) =
      Real.log ‖p.a i‖ - PrimitiveCutoffs.radial ε κ (Real.log ‖p.a i‖) *
        (∏ j ∈ S.mutable.filter (fun j => S.B i j ≠ 0),
          DominanceCutoff.chi ε (Real.log ‖p.a i‖ - Real.log ‖p.a j‖)) *
        PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * Real.log ‖p.a j‖) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) :=
  mutable_radial_equation S hdet hε hκ hδ p hp i hi

theorem genuine_partial_derivative {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) (i : Fin d) :
    (∑ j : Fin d, (S.B i j : ℝ) *
      ((SmoothAtlas.presentation S hdet).coordinateDifferential j p
        (Z S hdet ε κ hδ p) / p.a j).im) =
      deriv (fun t : ℝ => TorusLiouvilleDynamics.logarithmicHamiltonian S ε κ δ p
        (t • (Pi.single i 1 : Fin d → ℂ))) 0 :=
  angular_equation_partial_deriv S hdet hε hκ hδ p hp i

theorem uniform_torus_growth {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : S.Point, p ∈ initialTorus S →
      (∑ j : Fin d, (|(logarithmicComponents S hdet ε κ hδ p j).re| +
        |(logarithmicComponents S hdet ε κ hδ p j).im|)) ≤
        C * (1 + ∑ j : Fin d, |Real.log ‖p.a j‖|) :=
  logarithmic_linear_growth S hdet hε hκ hδ

/-- No nonvanishing assumption is made about any coordinate other than j. -/
theorem selected_nonzero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (j : Fin d) (hj : p.a j ≠ 0) :
    L S hdet ε κ hδ p j =
      ((SmoothAtlas.presentation S hdet).coordinateDifferential j p (Z S hdet ε κ hδ p) / p.a j).re ∧
    ContinuousAt (fun q => L S hdet ε κ hδ q j) p ∧
    (0 ≤ A S p j → L S hdet ε κ hδ p j = A S p j) ∧
    (A S p j < 0 → L S hdet ε κ hδ p j ≤ A S p j - PrimitiveCutoffs.radial ε κ (A S p j) ∧
      A S p j - PrimitiveCutoffs.radial ε κ (A S p j) < 0) :=
  ⟨L_eq_logarithmicComponents S hdet ε κ hδ p j hj,
    continuousAt_L S hdet hε hκ hδ p j hj,
    L_eq_A_of_nonneg S hdet hε hκ hδ p j hj,
    L_negative_bound S hdet hε hκ hδ p j hj⟩

/-- Arbitrary actual frozen variable, including points outside the initial torus. -/
theorem frozen_everywhere {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (j : Fin d) (hj : j ∉ S.mutable) :
    L S hdet ε κ hδ p j = Real.log ‖p.a j‖ :=
  frozen_radial_equation S hdet hε hκ hδ p j hj

/-- A genuine exchange boundary with an arbitrary complex partner. -/
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

theorem boundary_not_torus (w : ℂ) : boundaryPoint w ∉ initialTorus Examples.a2Seed := by
  intro h
  exact h 0 (boundary_coordinates w).1

theorem boundary_selected_radial (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    L Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ (boundaryPoint w) 1 = 0 := by
  have ha : A Examples.a2Seed (boundaryPoint w) 1 = 0 := by
    simp [A, (boundary_coordinates w).2.1]
  rw [L_eq_A_of_nonneg _ _ hε hκ hδ _ _ (by rw [(boundary_coordinates w).2.1]; norm_num)
    (by rw [ha]), ha]

theorem boundary_contraction (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    (v : (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.Tangent
      (boundaryPoint w)) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega Examples.a2Seed Examples.a2Seed_unimodular)
      (boundaryPoint w) (Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ (boundaryPoint w)) v =
    SmoothManifold.evalOne (GlobalPrimitive.alpha Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ)
      (boundaryPoint w) v :=
  contraction_omega _ _ hε hκ hδ _ v

/-- A full determinant-one matrix with both coordinates frozen and variable. -/
def frozenSeed : Seed 2 where
  B := Examples.a2Matrix
  mutable := ∅
  skew := Examples.a2Seed.skew
  acyclic := ⟨fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

theorem frozen_unimodular : frozenSeed.Unimodular := Examples.a2Seed_unimodular

def frozenPoint (t : ℝ) : frozenSeed.Point :=
  pointOfCoordinateTorus frozenSeed (fun j =>
    if j = 0 then ⟨(Real.exp t : ℂ), by exact_mod_cast Real.exp_ne_zero t⟩ else ⟨1, one_ne_zero⟩)

theorem frozen_radial_varies (t : ℝ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    L frozenSeed frozen_unimodular ε κ hδ (frozenPoint t) 0 = t := by
  rw [frozen_radial_equation _ _ hε hκ hδ _ _ (by simp [frozenSeed])]
  simp [A, frozenPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos t), Real.log_exp]

theorem empty_mutable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (hM : S.mutable = ∅) (p : S.Point) (j : Fin d) :
    L S hdet ε κ hδ p j = A S p j :=
  frozen_radial_equation S hdet hε hκ hδ p j (by simp [hM])

def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem empty_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem dimension_zero_inhabited : Nonempty emptySeed.Point := ⟨emptySeed.unitPoint⟩

theorem dimension_zero_field (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Z emptySeed empty_unimodular ε κ hδ emptySeed.unitPoint = 0 := by
  apply PiLp.ext
  intro i
  exact Fin.elim0 i

/-- Two independent mutable coordinates; the selected radius varies on a genuine boundary. -/
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

def varyingBoundary (w : ℂ) (t : ℝ) : pairSeed.Point :=
  ⟨(![0,-1,(Real.exp t : ℂ),1],
    fun j => if (j : Fin 4) = 0 then w else 2 / (Real.exp t : ℂ)), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj
      · simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
      · simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ,
          (show (Real.exp t : ℂ) ≠ 0 by exact_mod_cast Real.exp_ne_zero t)]
        field_simp [Complex.exp_ne_zero] <;> ring
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem varyingBoundary_geometry (w : ℂ) (t : ℝ) :
    (varyingBoundary w t).a 0 = 0 ∧ (varyingBoundary w t).a 2 ≠ 0 ∧
      A pairSeed (varyingBoundary w t) 2 = t := by
  simp [varyingBoundary, Seed.Point.a, A, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos t), Real.log_exp,
    (show (Real.exp t : ℂ) ≠ 0 by exact_mod_cast Real.exp_ne_zero t)]

theorem negative_boundary_bound (w : ℂ) (t : ℝ) (ht : t < 0)
    {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    varyingBoundary w t ∉ initialTorus pairSeed ∧
    L pairSeed pair_unimodular ε κ hδ (varyingBoundary w t) 2 ≤
      t - PrimitiveCutoffs.radial ε κ t ∧ t - PrimitiveCutoffs.radial ε κ t < 0 := by
  have hg := varyingBoundary_geometry w t
  refine ⟨fun h => h 0 hg.1, ?_⟩
  have h := L_negative_bound pairSeed pair_unimodular hε hκ hδ
    (varyingBoundary w t) 2 hg.2.1 (by rw [hg.2.2]; exact ht)
  simpa only [hg.2.2] using h

theorem nonnegative_boundary_exact (w : ℂ) (t : ℝ) (ht : 0 ≤ t)
    {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    L pairSeed pair_unimodular ε κ hδ (varyingBoundary w t) 2 = t := by
  have hg := varyingBoundary_geometry w t
  simpa only [hg.2.2] using L_eq_A_of_nonneg pairSeed pair_unimodular hε hκ hδ
    (varyingBoundary w t) 2 hg.2.1 (by rw [hg.2.2]; exact ht)


end GlobalLiouvilleFieldConsumer

-- Native transitive audit of the entire imported project closure, including
-- all private/generated roots and explicit attribution-sensitive supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`GlobalLiouvilleFieldConsumer.boundaryPoint, `GlobalLiouvilleFieldConsumer.frozenSeed,
        `GlobalLiouvilleFieldConsumer.frozenPoint, `GlobalLiouvilleFieldConsumer.emptySeed,
        `GlobalLiouvilleFieldConsumer.pairSeed, `GlobalLiouvilleFieldConsumer.varyingBoundary,
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
  let required := #[`ClusterSkeleton.GlobalLiouvilleField,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "global-liouville-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
