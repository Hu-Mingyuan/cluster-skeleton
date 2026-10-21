import ClusterSkeleton.CapAngularTangency
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

/-! Source-matched consumers of pointwise cap tangency. Every curve uses the
exact native field; cap membership is required only at the selected time. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.CapAngularTangency

namespace CapAngularTangencyConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

theorem selected_nonzero_all_strata {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (hp : p ∈ coordinateCap S) (j : Fin d) (hj : p.a j ≠ 0) :
    LocalAngularDynamics.angularRhs S ε κ δ p p j = 0 ∧
    LocalAngularDynamics.nu S ε κ δ p p = 0 ∧
    (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im = 0 :=
  ⟨angularRhs_eq_zero S hε (by linarith) δ hp j,
    nu_eq_zero S hε (by linarith) δ hp,
    logarithmicComponents_im_eq_zero S hdet hε hκ hδ hp j hj⟩

theorem variable_frozen_coordinate {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (hp : p ∈ coordinateCap S) (f : Fin d) (hf : f ∉ S.mutable) :
    p.a f ≠ 0 ∧ ‖p.a f‖ = 1 ∧
    (SmoothAtlas.presentation S hdet).coordinateDifferential f p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 :=
  ⟨p.frozen_ne_zero f hf, hp.1 f hf,
    coordinate_drift_eq_zero_of_unit S hdet hε hκ hδ hp f (hp.1 f hf)⟩

theorem mutable_boundary_without_partner_premise {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (hp : p ∈ coordinateCap S) (i : S.Mutable) (hi : ‖p.a i‖ = 1) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential i p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 :=
  coordinate_drift_eq_zero_of_unit S hdet hε hκ hδ hp i hi

theorem arbitrary_open_curve_at_cap_time {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → S.Point} {J : Set ℝ} {t₀ : ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsOpen J) (ht₀ : t₀ ∈ J) (hp : γ t₀ ∈ coordinateCap S)
    (j : Fin d) (hj : ‖(γ t₀).a j‖ = 1) :
    HasDerivWithinAt (fun u => (γ u).a j) 0 J t₀ ∧
      HasDerivAt (fun u => (γ u).a j) 0 t₀ := by
  have hd := coordinate_hasDerivWithinAt_zero S hdet hε hκ hδ hγ ht₀ hp j hj
  exact ⟨hd, hd.hasDerivAt (hJ.mem_nhds ht₀)⟩

/-- The carrier is still the literal exchange subtype with its induced topology. -/
theorem literal_carrier (p : S.Point) :
    Continuous (fun q : S.Point => q.val) ∧
    ∀ i : S.Mutable, p.a i*p.b i = S.positiveMonomial p.a i+S.negativeMonomial p.a i :=
  ⟨continuous_subtype_val, p.exchange⟩

theorem initial_torus_cap {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (hp : p ∈ coordinateCap S) (ht : p ∈ initialTorus S) :
    ∀ j, (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im = 0 :=
  fun j => logarithmicComponents_im_eq_zero S hdet hε hκ hδ hp j (ht j)

theorem unit_point_native_drift {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (j : Fin d) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential j S.unitPoint
      (GlobalLiouvilleField.Z S hdet ε κ hδ S.unitPoint) = 0 :=
  coordinate_drift_eq_zero_of_unit S hdet hε hκ hδ
    (unitPoint_mem_coordinateCap S) j (by simp)

theorem empty_mutable_native_drift (hM : S.mutable = ∅) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ coordinateCap S) :
    ∀ j, (SmoothAtlas.presentation S hdet).coordinateDifferential j p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 :=
  fun j => coordinate_drift_eq_zero_of_unit S hdet hε hκ hδ hp j
    (hp.1 j (by simp [hM]))

section Interior

/-- A literal A₂ cap family crossing the zero stratum, with a unit mutable
boundary coordinate whose partner is generally nonzero. -/
def interiorPoint (z : ℂ) : Examples.a2Seed.Point :=
  ⟨(![z,-1], fun i => if (i : Fin 2) = 0 then 0 else -(z+1)), by
    constructor
    · intro i
      rcases i with ⟨i,hi⟩
      fin_cases i <;> simp [Seed.positiveMonomial, Seed.negativeMonomial,
        Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two, add_comm]
    · intro i hi
      simp [Examples.a2Seed] at hi⟩

theorem interiorPoint_mem (z : ℂ) (hz : ‖z‖ ≤ 1) :
    interiorPoint z ∈ coordinateCap Examples.a2Seed := by
  constructor
  · intro i hi
    simp [Examples.a2Seed] at hi
  · intro i
    rcases i with ⟨i, hi⟩
    fin_cases i <;> simp [interiorPoint, Seed.Point.a, Seed.Point.b, hz]

theorem strict_nonzero_character (z : ℂ) (hz : z ≠ 0) (hr : ‖z‖ < 1) :
    (interiorPoint z).a 0 ≠ 0 ∧
    exchangeCharacter (interiorPoint z) 0 = -1 := by
  refine ⟨hz, ?_⟩
  exact exchangeCharacter_eq_neg_one_of_interior Examples.a2Seed
    (interiorPoint_mem z hr.le) ⟨0, by simp [Examples.a2Seed]⟩ hr

theorem strict_zero_character :
    (interiorPoint 0).a 0 = 0 ∧ exchangeCharacter (interiorPoint 0) 0 = -1 := by
  refine ⟨rfl, ?_⟩
  exact exchangeCharacter_eq_neg_one_of_interior Examples.a2Seed
    (interiorPoint_mem 0 (by norm_num)) ⟨0, by simp [Examples.a2Seed]⟩ (by norm_num [interiorPoint, Seed.Point.a])

/-- The boundary partner here is -1, not an extra zero-partner hypothesis. -/
theorem nonzero_boundary_partner_native_drift {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (interiorPoint 0).b ⟨1, by simp [Examples.a2Seed]⟩ = -1 ∧
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).coordinateDifferential
      1 (interiorPoint 0)
      (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ (interiorPoint 0)) = 0 := by
  refine ⟨by simp [interiorPoint, Seed.Point.b], ?_⟩
  exact coordinate_drift_eq_zero_of_unit Examples.a2Seed Examples.a2Seed_unimodular hε hκ hδ
    (interiorPoint_mem 0 (by norm_num)) 1 (by simp [interiorPoint, Seed.Point.a])

/-- Shifted time 7 in the open interval (5,9); the initial original coordinate
may be zero or nonzero. No claim is made that the curve stays in the cap. -/
theorem shifted_open_curve {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (γ : ℝ → Examples.a2Seed.Point)
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ioo 5 9))
    (hinit : γ 7 = interiorPoint z) :
    HasDerivWithinAt (fun u => (γ u).a 1) 0 (Ioo 5 9) 7 ∧
      HasDerivAt (fun u => (γ u).a 1) 0 7 := by
  apply arbitrary_open_curve_at_cap_time Examples.a2Seed Examples.a2Seed_unimodular
    hε hκ hδ hγ isOpen_Ioo (by norm_num)
  · rw [hinit]
    exact interiorPoint_mem z hz
  · simp [hinit, interiorPoint, Seed.Point.a]
end Interior

section Simultaneous

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

def simultaneousPoint : pairSeed.Point :=
  ⟨(![0,-1,0,-1], fun _ => 0), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem simultaneousPoint_mem : simultaneousPoint ∈ coordinateCap pairSeed := by
  constructor
  · intro j hj
    fin_cases j <;> simp_all [simultaneousPoint, Seed.Point.a, pairSeed]
  · intro j
    have hj := j.property
    simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj <;> simp [simultaneousPoint, Seed.Point.a, Seed.Point.b, hj]

theorem simultaneous_zero_native {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    simultaneousPoint.a 0 = 0 ∧ simultaneousPoint.a 2 = 0 ∧
    simultaneousPoint.a 1 ≠ 0 ∧
    exchangeCharacter simultaneousPoint 0 = -1 ∧ exchangeCharacter simultaneousPoint 2 = -1 ∧
    LocalAngularDynamics.nu pairSeed ε κ δ simultaneousPoint simultaneousPoint = 0 ∧
    (GlobalLiouvilleField.logarithmicComponents pairSeed pair_unimodular ε κ hδ simultaneousPoint 1).im = 0 := by
  refine ⟨rfl, rfl, by simp [simultaneousPoint, Seed.Point.a], ?_, ?_,
    nu_eq_zero pairSeed hε (by linarith) δ simultaneousPoint_mem,
    logarithmicComponents_im_eq_zero pairSeed pair_unimodular hε hκ hδ simultaneousPoint_mem 1
      (by simp [simultaneousPoint, Seed.Point.a])⟩
  · exact exchangeCharacter_eq_neg_one_of_interior pairSeed simultaneousPoint_mem
      ⟨0, by simp [pairSeed]⟩ (by simp [simultaneousPoint, Seed.Point.a])
  · exact exchangeCharacter_eq_neg_one_of_interior pairSeed simultaneousPoint_mem
      ⟨2, by simp [pairSeed]⟩ (by simp [simultaneousPoint, Seed.Point.a])
end Simultaneous

section Frozen

def frozenSeed : Seed 2 where
  B := Examples.a2Matrix
  mutable := ∅
  skew := Examples.a2Seed.skew
  acyclic := ⟨fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

theorem frozen_unimodular : frozenSeed.Unimodular := Examples.a2Seed_unimodular

def frozenPoint (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) : frozenSeed.Point :=
  pointOfCoordinateTorus frozenSeed fun j =>
    if j = 0 then ⟨z, by intro h; simp [h] at hz⟩ else ⟨w, by intro h; simp [h] at hw⟩

theorem independent_frozen_units {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    (frozenPoint z w hz hw).a 0 = z ∧ (frozenPoint z w hz hw).a 1 = w ∧
    frozenPoint z w hz hw ∈ coordinateCap frozenSeed ∧
    ∀ j : Fin 2,
      (SmoothAtlas.presentation frozenSeed frozen_unimodular).coordinateDifferential j (frozenPoint z w hz hw)
        (GlobalLiouvilleField.Z frozenSeed frozen_unimodular ε κ hδ (frozenPoint z w hz hw)) = 0 := by
  have hp : frozenPoint z w hz hw ∈ coordinateCap frozenSeed := by
    constructor
    · intro j _
      fin_cases j <;> simp [frozenPoint, hz, hw]
    · intro j
      exact False.elim (Finset.notMem_empty j.val j.property)
  refine ⟨by simp [frozenPoint], by simp [frozenPoint], hp, ?_⟩
  exact empty_mutable_native_drift frozenSeed frozen_unimodular rfl hε hκ hδ _ hp
end Frozen

section DimensionZero

def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem empty_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem dimension_zero {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : emptySeed.Point) :
    p ∈ coordinateCap emptySeed ∧ LocalAngularDynamics.nu emptySeed ε κ δ p p = 0 ∧
    GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ p = 0 := by
  have hp : p ∈ coordinateCap emptySeed := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i.val⟩
  refine ⟨hp, nu_eq_zero emptySeed hε (by linarith) δ hp, ?_⟩
  apply PiLp.ext
  intro i
  exact Fin.elim0 i
end DimensionZero

end CapAngularTangencyConsumer

-- Native per-root audit; accepted traversal retained exactly.
section
set_option maxHeartbeats 800000

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let before ← getEnv
    for (name, info) in before.constants.toList do
      let idx := before.getModuleIdxFor? name
      let actualProject := idx.any fun i =>
        let s := before.header.moduleNames[i]!.toString
        s.startsWith "ClusterSkeleton." || s.startsWith "FsFltz."
      if actualProject || idx.isNone then
        match info with
        | .defnInfo _ =>
          let _ ← Lean.Meta.getEqnsFor? name
          pure ()
        | _ => pure ()
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut report : Array String := #[]
  for mod in env.header.moduleNames do
    report := report.push s!"IMPORT {mod}"
    let nativePath ← Lean.findOLean mod
    report := report.push s!"NATIVEPATH {mod}: {nativePath}"
  let required := #[`ClusterSkeleton.CapAngularTangency,
    `ClusterSkeleton.AllStrataGrowth, `ClusterSkeleton.CapIndependence,
    `FsFltz.Geometry.SmoothLiouville, `FsFltz.Geometry.VectorFieldBridge]
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "cap-angular-tangency125-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"

end
