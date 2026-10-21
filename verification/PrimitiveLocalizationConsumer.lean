import ClusterSkeleton
import ClusterSkeleton.GlobalSymplectic
import ClusterSkeleton.PrimitiveLocalization
import Lean.Util.CollectAxioms

noncomputable section
open Set Filter ClusterSkeleton
open ClusterSkeleton.PrimitiveLocalization ClusterSkeleton.PrimitiveCutoffs
open ClusterSkeleton.DominanceCutoff
open scoped Topology Manifold
open FsFltz.Geometry (Model)

namespace PrimitiveLocalizationConsumer
variable {d : ℕ} {S : Seed d}

/-- One neighborhood supplies the complete scalar and logarithmic contract. -/
theorem simultaneous_contract (p : S.Point) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    ∃ U : Set S.Point, IsOpen U ∧ p ∈ U ∧
      (∀ q ∈ U, ∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet →
        S.negativeMonomial q.a i ≠ 0 ∧
        -exchangeCharacter q i = 1 - q.a i * normalizedPartner q i ∧
        (q.a i, normalizedPartner q i) ∈ nodeLogDomain ∧
        -exchangeCharacter q i ∈ Complex.slitPlane ∧
        angle q i = (nodeLog q i).im ∧
        (q ∈ initialTorus S → rowLog q i = (nodeLog q i).re)) ∧
      (∀ q ∈ U ∩ initialTorus S, ∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet →
        dominance S ε i (logNorms S q) = 1 ∧ rho (rowLog q i) = 1 ∧
        vartheta δ (angle q i) = angle q i ∧
        radial ε κ (logNorms S q i) = logNorms S q i + κ ∧
        correction ε κ δ i =ᶠ[𝓝 q] affineCorrection κ i) ∧
      (∀ q ∈ U ∩ initialTorus S, ∀ j : S.Mutable,
        (∃ i ∈ p.zeroSet, S.B i j ≠ 0) →
          dominance S ε j (logNorms S q) = 0 ∧
          correction ε κ δ j =ᶠ[𝓝 q] fun _ => 0) := by
  refine ⟨neighborhood ε κ δ p, isOpen_neighborhood ε κ δ p,
    mem_neighborhood ε κ hδ p, ?_, ?_, ?_⟩
  · intro q hq i hi
    exact node_bridges hq i hi
  · intro q hq i hi
    obtain ⟨h1,h2,h3,h4⟩ := plateaus hε hκ hδ hq.1 hq.2 i hi
    exact ⟨h1,h2,h3,h4,correction_eventuallyEq hε hκ hδ hq.1 hq.2 i hi⟩
  · intro q hq j hj
    exact ⟨adjacent_dominance_zero hε hq.1 hq.2 j hj,
      adjacent_correction_eventuallyEq hε hq.1 hq.2 j hj⟩

/-- All vanishing indices and arbitrary native tangent directions on the same U. -/
theorem simultaneous_native_differentials (hdet : S.Unimodular) (p : S.Point)
    {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ∃ U : Set S.Point, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U ∩ initialTorus S,
      (∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet →
        ∀ v : TangentSpace 𝓘(ℝ, Model (2 * d)) q,
        mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (correction ε κ δ i) q v =
          mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (affineCorrection κ i) q v) ∧
      (∀ j : S.Mutable, (∃ i ∈ p.zeroSet, S.B i j ≠ 0) →
        ∀ v : TangentSpace 𝓘(ℝ, Model (2 * d)) q,
        mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (correction ε κ δ j) q v = 0) := by
  letI := SmoothAtlas.charts S hdet
  refine ⟨neighborhood ε κ δ p, isOpen_neighborhood ε κ δ p,
    mem_neighborhood ε κ hδ p, fun q hq => ⟨?_, ?_⟩⟩
  · intro i hi v
    rw [correction_mfderiv_eq hdet hε hκ hδ hq.1 hq.2 i hi]
    rfl
  · intro j hj v
    rw [adjacent_correction_mfderiv_eq_zero hdet hε hq.1 hq.2 j hj]
    rfl

theorem nonempty_torus_part (hdet : S.Unimodular) (p : S.Point)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (neighborhood ε κ δ p ∩ initialTorus S).Nonempty :=
  (dense_initialTorus S hdet).inter_open_nonempty _
    (isOpen_neighborhood ε κ δ p) ⟨p, mem_neighborhood ε κ hδ p⟩

/-- The zero-set may be empty in any dimension; no index is chosen from it. -/
theorem unit_zeroSet_empty (S : Seed d) : S.unitPoint.zeroSet = ∅ := by
  ext i
  simp [Seed.Point.mem_zeroSet]

theorem empty_zeroSet_contract (S : Seed d) (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IsOpen (neighborhood ε κ δ S.unitPoint) ∧
      S.unitPoint ∈ neighborhood ε κ δ S.unitPoint ∧ S.unitPoint.zeroSet = ∅ :=
  ⟨isOpen_neighborhood ε κ δ S.unitPoint, mem_neighborhood ε κ hδ S.unitPoint,
    unit_zeroSet_empty S⟩

open ClusterSkeleton.Examples

def boundaryPoint : a2Seed.Point :=
  ⟨(![0, -1], fun i => if i.val = 0 then 0 else -1), by
    constructor
    · intro i
      rcases i with ⟨i, hi⟩
      fin_cases i <;> norm_num [Seed.positiveMonomial, Seed.negativeMonomial,
        a2Seed, a2Matrix, Fin.prod_univ_two]
    · intro f hf
      simp [a2Seed] at hf⟩

theorem boundary_zeroSet : boundaryPoint.zeroSet = {0} := by
  ext i
  fin_cases i <;> simp [Seed.Point.mem_zeroSet, boundaryPoint, Seed.Point.a, a2Seed]

theorem boundary_not_torus : boundaryPoint ∉ initialTorus a2Seed := by
  intro h
  exact h 0 rfl

/-- A genuine boundary has a nonempty torus neighborhood carrying the correction germ. -/
theorem boundary_correction_germ {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    (neighborhood ε κ δ boundaryPoint ∩ initialTorus a2Seed).Nonempty ∧
      ∀ q ∈ neighborhood ε κ δ boundaryPoint ∩ initialTorus a2Seed,
        correction ε κ δ ⟨0, by simp [a2Seed]⟩ =ᶠ[𝓝 q]
          affineCorrection κ ⟨0, by simp [a2Seed]⟩ := by
  refine ⟨nonempty_torus_part a2Seed_unimodular boundaryPoint ε κ hδ, ?_⟩
  intro q hq
  exact correction_eventuallyEq hε hκ hδ hq.1 hq.2 _ (by simp [boundary_zeroSet])

/-- A full determinant-one matrix with two genuinely variable frozen coordinates. -/
def frozenSeed : Seed 2 where
  B := a2Matrix
  mutable := ∅
  skew := a2Seed.skew
  acyclic := ⟨fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

theorem frozen_unimodular : frozenSeed.Unimodular := a2Seed_unimodular

def frozenPoint (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) : frozenSeed.Point :=
  ⟨(![z, w], fun i => False.elim (by simpa [frozenSeed] using i.property)), by
    constructor
    · intro i
      exact False.elim (by simpa [frozenSeed] using i.property)
    · intro f _
      fin_cases f <;> simp [hz, hw]⟩

theorem arbitrary_frozen_coordinates (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (frozenPoint z w hz hw).a 0 = z ∧ (frozenPoint z w hz hw).a 1 = w ∧
    frozenPoint z w hz hw ∈ neighborhood ε κ δ (frozenPoint z w hz hw) ∧
    (neighborhood ε κ δ (frozenPoint z w hz hw) ∩ initialTorus frozenSeed).Nonempty :=
  ⟨rfl, rfl, mem_neighborhood ε κ hδ _, nonempty_torus_part frozen_unimodular _ ε κ hδ⟩

end PrimitiveLocalizationConsumer

-- Complete native per-root audit of the new combined import scope.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.PrimitiveLocalization.rowLog,
        `ClusterSkeleton.PrimitiveLocalization.angle,
        `ClusterSkeleton.PrimitiveLocalization.nodeLog,
        `ClusterSkeleton.PrimitiveLocalization.correction,
        `ClusterSkeleton.PrimitiveLocalization.affineCorrection,
        `ClusterSkeleton.PrimitiveLocalization.region,
        `ClusterSkeleton.PrimitiveLocalization.neighborhood] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mods := #[`ClusterSkeleton.PrimitiveLocalization,
    `ClusterSkeleton.PrimitiveCutoffs, `ClusterSkeleton.DominanceCutoff]
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
    let named := mods.any fun mod =>
      name.toString.startsWith (mod.toString ++ ".") ||
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
  logInfo m!"AUDITED localization/scalar/dominance modules: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
