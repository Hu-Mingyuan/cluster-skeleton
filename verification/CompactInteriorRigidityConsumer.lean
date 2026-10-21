import ClusterSkeleton.CompactInteriorRigidity
import ClusterSkeleton.CapForwardInvariance
import ClusterSkeleton.ZeroStratumEscape
import Lean.Util.CollectAxioms

/-! Consumers use compact forward closure, not initial or whole-curve cap membership.
The explicit families allow arbitrary partners at other simultaneous zero originals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.CompactInteriorRigidity

namespace CompactInteriorRigidityConsumer

section Generic
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ t₀ η : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
  (hδ : 0 < δ) (hη : 0 < η) {γ : ℝ → S.Point}
  (hγ : letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀-η)))
  (hK : IsCompact (closure (γ '' Ici t₀)))
include hε hκ hδ hη hγ hK

/-- The initial time is arbitrary, and the only orbit restriction is compactness. -/
theorem shifted_initial_endpoint (i : S.Mutable) (hi : (γ t₀).a i ≠ 0)
    (hr : ‖(γ t₀).a i‖ < 1) :
    normalizedPartner (γ t₀) i = 0 ∧ (γ t₀).b i = 0 :=
  initial_partners_zero S hdet hε hκ hδ hη hγ hK i hi hr

/-- Any set of other simultaneous initial zeros is allowed. -/
theorem selected_with_simultaneous_zeros (i : S.Mutable) (hi : (γ t₀).a i ≠ 0)
    (hr : ‖(γ t₀).a i‖ < 1) (J : Set S.Mutable)
    (hJ : ∀ j ∈ J, (γ t₀).a j = 0) :
    (∀ j ∈ J, (γ t₀).a j = 0) ∧
    normalizedPartner (γ t₀) i = 0 ∧ (γ t₀).b i = 0 :=
  ⟨hJ, initial_partners_zero S hdet hε hκ hδ hη hγ hK i hi hr⟩

/-- The initially vanishing radial cutoff is compatible with the same rigidity theorem. -/
theorem shallow_collar (i : S.Mutable) (hi : (γ t₀).a i ≠ 0)
    (hr : ‖(γ t₀).a i‖ < 1)
    (hc : -2*ε < GlobalLiouvilleField.A S (γ t₀) i) :
    PrimitiveCutoffs.radial ε κ (GlobalLiouvilleField.A S (γ t₀) i) = 0 ∧
    normalizedPartner (γ t₀) i = 0 ∧ (γ t₀).b i = 0 :=
  ⟨PrimitiveCutoffs.radial_eq_zero (by linarith) hc.le,
    initial_partners_zero S hdet hε hκ hδ hη hγ hK i hi hr⟩

/-- Neither mutable radial restrictions nor frozen unit norms are input hypotheses. -/
theorem radial_restrictions_from_compactness :
    (∀ j : Fin d, ‖(γ t₀).a j‖ ≤ 1) ∧
    (∀ f : Fin d, f ∉ S.mutable → ‖(γ t₀).a f‖ = 1) :=
  ⟨original_norm_le_one S hdet hε hκ hδ hη hγ hK,
    frozen_norm_eq_one S hdet hε hκ hδ hη hγ hK⟩

omit hε hκ hδ hη hγ hK in
/-- The literal subtype topology and actual exchange equations remain in use. -/
theorem literal_carrier (p : S.Point) :
    Continuous (fun q : S.Point => q.val) ∧
    ∀ i : S.Mutable, p.a i*p.b i = S.positiveMonomial p.a i+S.negativeMonomial p.a i :=
  ⟨continuous_subtype_val, p.exchange⟩

omit hε hκ hδ hη hγ hK in
/-- This consumer inhabits the unaltered target proposition. -/
theorem exact_target : CompactInteriorRigidityTarget S hdet :=
  compactInteriorRigidityTarget S hdet
end Generic

/-- Two mutable vertices, each coupled to a variable frozen vertex. -/
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

/-- The selected partner need not vanish in this literal input family; the other
original is zero and its partner v is arbitrary. -/
def simultaneousPoint (r z v : ℂ) (hr : r ≠ 0) (hz : z ≠ 0) : pairSeed.Point :=
  ⟨(![r,z,0,-1], fun i => if (i : Fin 4) = 0 then (z+1)/r else v), by
    constructor
    · intro i
      have hi := i.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi <;>
        simp [hi, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed,
          Fin.prod_univ_succ, hr, mul_div_cancel₀]
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

/-- Compactness forces the variable neighboring phase z to equal -1, despite an
arbitrary other zero-coordinate partner and an arbitrary shifted start time. -/
theorem simultaneous_family {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    (r z v : ℂ) (hr : r ≠ 0) (hz : z ≠ 0) (hrlt : ‖r‖ < 1)
    {γ : ℝ → pairSeed.Point}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ioi (t₀-η)))
    (hK : IsCompact (closure (γ '' Ici t₀)))
    (hinit : γ t₀ = simultaneousPoint r z v hr hz) :
    (γ t₀).a 0 ≠ 0 ∧ (γ t₀).a 2 = 0 ∧
    (γ t₀).b ⟨2, by simp [pairSeed]⟩ = v ∧
    normalizedPartner (γ t₀) ⟨0, by simp [pairSeed]⟩ = 0 ∧
    (γ t₀).b ⟨0, by simp [pairSeed]⟩ = 0 ∧ z = -1 := by
  have hp := initial_partners_zero pairSeed pair_unimodular hε hκ hδ hη hγ hK
    ⟨0, by simp [pairSeed]⟩ (by simpa [hinit, simultaneousPoint, Seed.Point.a] using hr)
    (by simpa [hinit, simultaneousPoint, Seed.Point.a] using hrlt)
  refine ⟨by simpa [hinit, simultaneousPoint, Seed.Point.a] using hr,
    by simp [hinit, simultaneousPoint, Seed.Point.a],
    by simp [hinit, simultaneousPoint, Seed.Point.b], hp.1, hp.2, ?_⟩
  have he : (z+1)/r = 0 := by simpa [hinit, simultaneousPoint, Seed.Point.b] using hp.2
  exact eq_neg_of_add_eq_zero_left ((div_eq_zero_iff.mp he).resolve_right hr)

/-- Three independently variable frozen phases occur in the selected row. -/
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

/-- No phase-product or partner-zero condition is built into this family. -/
def phasePoint (r u z w : ℂ) (hr : r ≠ 0) (hu : u ≠ 0) (hz : z ≠ 0)
    (hw : w ≠ 0) : phaseSeed.Point :=
  ⟨(![r,u,z,w], fun _ => (u*z*w+1)/r), by
    constructor
    · intro i
      have hi : (i : Fin 4) = 0 := Finset.mem_singleton.mp i.property
      simp [hi, Seed.positiveMonomial, Seed.negativeMonomial, phaseSeed,
        Fin.prod_univ_succ, hr, mul_div_cancel₀, mul_assoc]
    · intro j hj
      fin_cases j <;> simp_all [phaseSeed]⟩

/-- Unit phases are genuine variables. Compact native forward closure forces
an exchange relation on their product. -/
theorem variable_frozen_phases {ε κ δ t₀ η : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
    (r u z w : ℂ) (hr : r ≠ 0) (hu : u ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hrlt : ‖r‖ < 1) (hu1 : ‖u‖ = 1) (hz1 : ‖z‖ = 1) (hw1 : ‖w‖ = 1)
    {γ : ℝ → phaseSeed.Point}
    (hγ : letI := SmoothAtlas.charts phaseSeed phase_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z phaseSeed phase_unimodular ε κ hδ) (Ioi (t₀-η)))
    (hK : IsCompact (closure (γ '' Ici t₀)))
    (hinit : γ t₀ = phasePoint r u z w hr hu hz hw) :
    ‖u‖ = 1 ∧ ‖z‖ = 1 ∧ ‖w‖ = 1 ∧ u*z*w = -1 ∧
    normalizedPartner (γ t₀) ⟨0, by simp [phaseSeed]⟩ = 0 ∧
    (γ t₀).b ⟨0, by simp [phaseSeed]⟩ = 0 := by
  have hp := initial_partners_zero phaseSeed phase_unimodular hε hκ hδ hη hγ hK
    ⟨0, by simp [phaseSeed]⟩ (by simpa [hinit, phasePoint, Seed.Point.a] using hr)
    (by simpa [hinit, phasePoint, Seed.Point.a] using hrlt)
  refine ⟨hu1, hz1, hw1, ?_, hp⟩
  have he : (u*z*w+1)/r = 0 := by simpa [hinit, phasePoint, Seed.Point.b] using hp.2
  exact eq_neg_of_add_eq_zero_left ((div_eq_zero_iff.mp he).resolve_right hr)

/-- The strict-interior shallow collar is inhabited for each positive ε,
with another simultaneous original zero and an unrestricted partner v. -/
theorem shallow_family_initial {ε : ℝ} (hε : 0 < ε) (z v : ℂ) (hz : z ≠ 0) :
    let p := simultaneousPoint (Real.exp (-ε) : ℂ) z v
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hz
    p.a 0 ≠ 0 ∧ ‖p.a 0‖ < 1 ∧ p.a 2 = 0 ∧
    -2*ε < GlobalLiouvilleField.A pairSeed p 0 := by
  have hn : ‖(Real.exp (-ε) : ℂ)‖ = Real.exp (-ε) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨?_, ?_, rfl, ?_⟩
  · simpa [simultaneousPoint, Seed.Point.a] using
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-ε)))
  · change ‖(Real.exp (-ε) : ℂ)‖ < 1
    rw [hn, Real.exp_lt_one_iff]; linarith
  · change -2*ε < Real.log ‖(Real.exp (-ε) : ℂ)‖
    rw [hn, Real.log_exp]; linarith

end CompactInteriorRigidityConsumer

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
  let required := #[`ClusterSkeleton.CompactInteriorRigidity, `ClusterSkeleton.CapForwardInvariance, `ClusterSkeleton.ZeroStratumEscape,
    `ClusterSkeleton.InteriorPartnerPropagation, `ClusterSkeleton.CapAngularTangency,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "compact-interior-rigidity-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"

end
