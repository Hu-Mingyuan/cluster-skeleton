import ClusterSkeleton.InteriorPartnerPropagation
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

/-! Source-matched consumers of strict-interior propagation. Only one initial
cap membership is supplied; other original coordinates can vanish. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.InteriorPartnerPropagation

namespace InteriorPartnerPropagationConsumer

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

def simultaneousPoint (z : ℂ) : pairSeed.Point :=
  ⟨(![z,-1,0,-1], fun _ => 0), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem simultaneousPoint_mem (z : ℂ) (hz : ‖z‖ ≤ 1) : simultaneousPoint z ∈ coordinateCap pairSeed := by
  constructor
  · intro j hj
    fin_cases j <;> simp_all [simultaneousPoint, Seed.Point.a, pairSeed]
  · intro j
    have hj := j.property
    simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj <;> simp [simultaneousPoint, Seed.Point.a, Seed.Point.b, hj, hz]



section Generic
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ t₀ η : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
  (hδ : 0 < δ) (hη : 0 < η) {γ : ℝ → S.Point}
  (hγ : letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀-η)))
  (hp : γ t₀ ∈ coordinateCap S) (i : S.Mutable)
  (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1)

include hε hκ hδ hη hγ hp hi hr

/-- All full-row neighbor premises come from the single cap premise. -/
theorem all_neighbors_from_initial_cap {t : ℝ} (ht : 0 ≤ t) :
    (∀ j, S.B i j ≠ 0 → ‖(γ (t₀+t)).a j‖ = 1) ∧
    exchangeCharacter (γ (t₀+t)) i = -1 ∧
    normalizedPartner (γ (t₀+t)) i = 0 ∧ (γ (t₀+t)).b i = 0 :=
  ⟨neighbors_unit_forward S hdet hε hκ hδ hη hγ hp i hr ht,
    propagate S hdet hε hκ hδ hη hγ hp i hi hr ht⟩

/-- The same theorem applies while a different original coordinate stays zero. -/
theorem selected_with_other_zero (j : Fin d) (hj : (γ t₀).a j = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (γ (t₀+t)).a i ≠ 0 ∧ (γ (t₀+t)).a j = 0 ∧
    exchangeCharacter (γ (t₀+t)) i = -1 ∧
    normalizedPartner (γ (t₀+t)) i = 0 ∧ (γ (t₀+t)).b i = 0 := by
  refine ⟨NativeRadialOrbit.coordinate_ne_zero S hdet hε hκ hδ hη hγ i hi (by linarith),
    ?_, propagate S hdet hε hκ hδ hη hγ hp i hi hr ht⟩
  exact (ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ
    isPreconnected_Ioi (show t₀ ∈ Ioi (t₀-η) by change t₀-η < t₀; linarith)
      (show t₀+t ∈ Ioi (t₀-η) by change t₀-η < t₀+t; linarith) j).mp hj

/-- The forward endpoint is present even at a shifted initial time. -/
theorem shifted_initial_endpoint :
    exchangeCharacter (γ t₀) i = -1 ∧
    normalizedPartner (γ t₀) i = 0 ∧ (γ t₀).b i = 0 := by
  simpa using propagate S hdet hε hκ hδ hη hγ hp i hi hr (le_refl (0 : ℝ))

omit hε hκ hδ hη hγ hp hi hr in
/-- The literal subtype topology and actual exchange equations are retained. -/
theorem literal_carrier (p : S.Point) :
    Continuous (fun q : S.Point => q.val) ∧
    ∀ j : S.Mutable, p.a j*p.b j = S.positiveMonomial p.a j+S.negativeMonomial p.a j :=
  ⟨continuous_subtype_val, p.exchange⟩

/-- No deep-radius or cutoff-one hypothesis is needed in the shallow collar. -/
theorem shallow_collar {t : ℝ} (ht : 0 ≤ t)
    (hcollar : -2*ε < GlobalLiouvilleField.A S (γ t₀) i) :
    PrimitiveCutoffs.radial ε κ (GlobalLiouvilleField.A S (γ t₀) i) = 0 ∧
    exchangeCharacter (γ (t₀+t)) i = -1 ∧
    normalizedPartner (γ (t₀+t)) i = 0 ∧ (γ (t₀+t)).b i = 0 :=
  ⟨PrimitiveCutoffs.radial_eq_zero (by linarith) hcollar.le,
    propagate S hdet hε hκ hδ hη hγ hp i hi hr ht⟩
end Generic

/-- A nonzero A₂ disk coordinate coexists with a boundary coordinate having a
nonzero partner; only the selected strict-interior partner is propagated. -/
theorem a2_family_forward {ε κ δ t₀ η : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (hη : 0 < η) (z : ℂ) (hz : z ≠ 0) (hr : ‖z‖ < 1)
    {γ : ℝ → Examples.a2Seed.Point}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ioi (t₀-η)))
    (hinit : γ t₀ = interiorPoint z) {t : ℝ} (ht : 0 ≤ t) :
    (γ t₀).b ⟨1, by simp [Examples.a2Seed]⟩ ≠ 0 ∧
    exchangeCharacter (γ (t₀+t)) 0 = -1 ∧
    normalizedPartner (γ (t₀+t)) ⟨0, by simp [Examples.a2Seed]⟩ = 0 ∧
    (γ (t₀+t)).b ⟨0, by simp [Examples.a2Seed]⟩ = 0 := by
  constructor
  · simp only [hinit, interiorPoint, Seed.Point.b]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, neg_ne_zero]
    intro he
    have heq : z = -1 := eq_neg_of_add_eq_zero_left he
    simpa [heq] using hr
  · exact propagate Examples.a2Seed Examples.a2Seed_unimodular hε hκ hδ hη hγ
      (by rw [hinit]; exact interiorPoint_mem z hr.le) ⟨0, by simp [Examples.a2Seed]⟩
      (by simpa [hinit, interiorPoint, Seed.Point.a] using hz)
      (by simpa [hinit, interiorPoint, Seed.Point.a] using hr) ht

/-- A concrete selected nonzero disk coordinate and a simultaneous zero original. -/
theorem simultaneous_family_forward {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η) (z : ℂ)
    (hz : z ≠ 0) (hr : ‖z‖ < 1) {γ : ℝ → pairSeed.Point}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ioi (t₀-η)))
    (hinit : γ t₀ = simultaneousPoint z) {t : ℝ} (ht : 0 ≤ t) :
    (γ (t₀+t)).a 0 ≠ 0 ∧ (γ (t₀+t)).a 2 = 0 ∧
    exchangeCharacter (γ (t₀+t)) 0 = -1 ∧
    normalizedPartner (γ (t₀+t)) ⟨0, by simp [pairSeed]⟩ = 0 ∧
    (γ (t₀+t)).b ⟨0, by simp [pairSeed]⟩ = 0 := by
  exact selected_with_other_zero pairSeed pair_unimodular hε hκ hδ hη hγ
    (by rw [hinit]; exact simultaneousPoint_mem z hr.le) ⟨0, by simp [pairSeed]⟩
    (by simpa [hinit, simultaneousPoint, Seed.Point.a] using hz)
    (by simpa [hinit, simultaneousPoint, Seed.Point.a] using hr) 2
    (by simp [hinit, simultaneousPoint, Seed.Point.a]) ht

/-- This unimodular matrix has three frozen columns in the selected mutable row. -/
def phaseSeed : Seed 4 where
  B := !![0,1,1,1; -1,0,0,0; -1,0,0,1; -1,0,-1,0]
  mutable := {0}
  skew := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  acyclic := by
    refine ⟨fun i => Acc.intro i fun j h => ?_⟩
    have hi : (i : Fin 4) = 0 := Finset.mem_singleton.mp i.property
    have hj : (j : Fin 4) = 0 := Finset.mem_singleton.mp j.property
    simp [hi,hj] at h

theorem phase_unimodular : phaseSeed.Unimodular := by
  norm_num [Seed.Unimodular, phaseSeed, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]

/-- The two parameters z,w are independent unit phases. The third frozen phase
is their inverse product with the exchange sign. None is specialized in the seed. -/
def phasePoint (r z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) : phaseSeed.Point := by
  have hnz : z ≠ 0 := by intro h; simp [h] at hz
  have hnw : w ≠ 0 := by intro h; simp [h] at hw
  refine ⟨(![r,-(z*w)⁻¹,z,w], fun _ => 0), ?_⟩
  constructor
  · intro i
    have hi : (i : Fin 4) = 0 := Finset.mem_singleton.mp i.property
    simp [hi, Seed.positiveMonomial, Seed.negativeMonomial, phaseSeed, Fin.prod_univ_succ,
      mul_inv_rev, hnz, hnw, mul_assoc, mul_left_comm, mul_comm]
    field_simp
    ring
  · intro j hj
    fin_cases j <;> simp_all [phaseSeed]

theorem phasePoint_mem (r z w : ℂ) (hr : ‖r‖ ≤ 1) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    phasePoint r z w hz hw ∈ coordinateCap phaseSeed := by
  constructor
  · intro j hj
    fin_cases j <;> simp_all [phasePoint, Seed.Point.a, phaseSeed, norm_mul]
  · intro j
    have hj : (j : Fin 4) = 0 := Finset.mem_singleton.mp j.property
    simp [phasePoint, Seed.Point.a, Seed.Point.b, hj, hr]

theorem independent_frozen_phases_forward {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η) (r z w : ℂ)
    (hr0 : r ≠ 0) (hr : ‖r‖ < 1) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    {γ : ℝ → phaseSeed.Point}
    (hγ : letI := SmoothAtlas.charts phaseSeed phase_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z phaseSeed phase_unimodular ε κ hδ) (Ioi (t₀-η)))
    (hinit : γ t₀ = phasePoint r z w hz hw) {t : ℝ} (ht : 0 ≤ t) :
    (γ t₀).a 2 = z ∧ (γ t₀).a 3 = w ∧
    (∀ j, phaseSeed.B 0 j ≠ 0 → ‖(γ (t₀+t)).a j‖ = 1) ∧
    exchangeCharacter (γ (t₀+t)) 0 = -1 ∧
    normalizedPartner (γ (t₀+t)) ⟨0, by simp [phaseSeed]⟩ = 0 ∧
    (γ (t₀+t)).b ⟨0, by simp [phaseSeed]⟩ = 0 := by
  refine ⟨by simp [hinit, phasePoint, Seed.Point.a], by simp [hinit, phasePoint, Seed.Point.a], ?_⟩
  exact all_neighbors_from_initial_cap phaseSeed phase_unimodular hε hκ hδ hη hγ
    (by rw [hinit]; exact phasePoint_mem r z w hr.le hz hw) ⟨0, by simp [phaseSeed]⟩
    (by simpa [hinit, phasePoint, Seed.Point.a] using hr0)
    (by simpa [hinit, phasePoint, Seed.Point.a] using hr) ht

/-- The shallow-collar premises are inhabited for every positive ε. -/
theorem shallow_family_initial {ε : ℝ} (hε : 0 < ε) :
    let p := interiorPoint (Real.exp (-ε) : ℂ)
    p ∈ coordinateCap Examples.a2Seed ∧ p.a 0 ≠ 0 ∧ ‖p.a 0‖ < 1 ∧
    -2*ε < GlobalLiouvilleField.A Examples.a2Seed p 0 := by
  have hn : ‖(Real.exp (-ε) : ℂ)‖ = Real.exp (-ε) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hr : ‖(Real.exp (-ε) : ℂ)‖ < 1 := by
    rw [hn, Real.exp_lt_one_iff]; linarith
  refine ⟨interiorPoint_mem _ hr.le, ?_, hr, ?_⟩
  · simpa [interiorPoint, Seed.Point.a] using
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-ε)))
  · change -2*ε < Real.log ‖(Real.exp (-ε) : ℂ)‖
    rw [hn, Real.log_exp]
    linarith

/-- A source-matched use of the full proposition, with no caller-supplied
character equation, neighbor condition, or later cap premise. -/
theorem exact_target {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    InteriorPartnerPropagationTarget S hdet := interiorPartnerPropagationTarget S hdet

end InteriorPartnerPropagationConsumer


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
  let required := #[`ClusterSkeleton.InteriorPartnerPropagation, `ClusterSkeleton.CapAngularTangency,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "interior-partner-propagation-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"

end
