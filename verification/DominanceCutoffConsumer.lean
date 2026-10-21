import ClusterSkeleton
import ClusterSkeleton.GlobalSymplectic
import ClusterSkeleton.DominanceCutoff
import Lean.Util.CollectAxioms

noncomputable section
open scoped ContDiff
open ClusterSkeleton ClusterSkeleton.DominanceCutoff

namespace DominanceCutoffConsumer

variable {d : ℕ} (S : Seed d) {ε : ℝ} (hε : 0 < ε)

theorem scalar_smooth : ContDiff ℝ ∞ (chi ε) := contDiff_chi ε

theorem scalar_range (x : ℝ) : chi ε x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨chi_nonneg ε x, chi_le_one ε x⟩

include hε in
theorem left_plateau (x : ℝ) (hx : x ≤ -ε) : chi ε x = 1 :=
  (chi_eq_one_iff hε).2 hx

include hε in
theorem right_plateau (x : ℝ) (hx : -ε / 2 ≤ x) : chi ε x = 0 :=
  (chi_eq_zero_iff hε).2 hx

theorem product_smooth (i : Fin d) : ContDiff ℝ ∞ (dominance S ε i) :=
  contDiff_dominance S ε i

theorem product_range (i : Fin d) (A : Fin d → ℝ) :
    dominance S ε i A ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨dominance_nonneg S ε i A, dominance_le_one S ε i A⟩

theorem empty_product (i : Fin d) (A : Fin d → ℝ)
    (h : ∀ j ∈ S.mutable, S.B i j = 0) : dominance S ε i A = 1 := by
  apply dominance_of_no_neighbors
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact ((mem_mutableNeighbors S i j).1 hj).2 (h j ((mem_mutableNeighbors S i j).1 hj).1)

include hε in
theorem no_adjacent_nonzero (i j : Fin d) (hi : i ∈ S.mutable) (hj : j ∈ S.mutable)
    (hij : S.B i j ≠ 0) (A : Fin d → ℝ) :
    ¬ (dominance S ε i A ≠ 0 ∧ dominance S ε j A ≠ 0) := by
  rintro ⟨h1, h2⟩
  exact (adjacent_exclusion S hε i j hi hj hij A).elim h1 h2

include hε in
theorem actual_localization (p : S.Point) :
    ∃ U : Set S.Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U ∩ initialTorus S,
        (∀ i ∈ p.zeroSet, dominance S ε i (logNorms S q) = 1) ∧
        (∀ j ∈ S.mutable, (∃ i ∈ p.zeroSet, S.B i j ≠ 0) →
          dominance S ε j (logNorms S q) = 0) := localization S hε p

/-- The empty-dimensional carrier is explicitly inhabited. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

def emptyPoint : emptySeed.Point := emptySeed.unitPoint

theorem empty_inhabited : Nonempty emptySeed.Point := ⟨emptyPoint⟩

theorem empty_neighborhood (ε : ℝ) :
    localizationNeighborhood emptySeed ε emptyPoint = Set.univ := by
  ext q
  simp only [localizationNeighborhood, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i
  exact Fin.elim0 i

include hε in
theorem empty_localization :
    ∃ U : Set emptySeed.Point, IsOpen U ∧ emptyPoint ∈ U ∧
      ∀ q ∈ U ∩ initialTorus emptySeed,
        (∀ i ∈ emptyPoint.zeroSet, dominance emptySeed ε i (logNorms emptySeed q) = 1) ∧
        (∀ j ∈ emptySeed.mutable, (∃ i ∈ emptyPoint.zeroSet, emptySeed.B i j ≠ 0) →
          dominance emptySeed ε j (logNorms emptySeed q) = 0) :=
  localization emptySeed hε emptyPoint

open ClusterSkeleton.Examples

/-- The same literal A2 boundary data as the accepted NodeNondegeneracyConsumer;
that standalone consumer is outside the Lake library, so the data are repeated. -/
def a2BoundaryPoint : a2Seed.Point :=
  ⟨(![0, -1], fun i => if i.val = 0 then 0 else -1), by
    constructor
    · intro i
      rcases i with ⟨i, hi⟩
      fin_cases i <;> norm_num [Seed.positiveMonomial, Seed.negativeMonomial,
        a2Seed, a2Matrix, Fin.prod_univ_two]
    · intro f hf
      simp [a2Seed] at hf⟩

theorem a2_boundary_zeroSet : a2BoundaryPoint.zeroSet = {0} := by
  ext i
  fin_cases i <;> simp [Seed.Point.mem_zeroSet, a2BoundaryPoint, Seed.Point.a, a2Seed]

theorem a2_boundary_not_torus : a2BoundaryPoint ∉ initialTorus a2Seed := by
  intro h
  exact h 0 rfl

include hε in
theorem a2_boundary_localization :
    ∃ U : Set a2Seed.Point, IsOpen U ∧ a2BoundaryPoint ∈ U ∧
      ∀ q ∈ U ∩ initialTorus a2Seed,
        dominance a2Seed ε 0 (logNorms a2Seed q) = 1 ∧
        dominance a2Seed ε 1 (logNorms a2Seed q) = 0 := by
  obtain ⟨U, ho, hp, h⟩ := localization a2Seed hε a2BoundaryPoint
  refine ⟨U, ho, hp, fun q hq => ?_⟩
  have hi : (0 : Fin 2) ∈ a2BoundaryPoint.zeroSet := by simp [a2_boundary_zeroSet]
  exact ⟨(h q hq).1 0 hi, (h q hq).2 1 (by simp [a2Seed])
    ⟨0, hi, by norm_num [a2Seed, a2Matrix]⟩⟩

/-- The torus part of the displayed boundary neighborhood is nonempty. -/
theorem a2_localized_torus_nonempty (ε : ℝ) :
    (localizationNeighborhood a2Seed ε a2BoundaryPoint ∩ initialTorus a2Seed).Nonempty :=
  (dense_initialTorus a2Seed a2Seed_unimodular).inter_open_nonempty _
    (isOpen_localizationNeighborhood a2Seed ε a2BoundaryPoint)
    ⟨a2BoundaryPoint, mem_localizationNeighborhood a2Seed ε a2BoundaryPoint⟩

end DominanceCutoffConsumer

-- Native per-root transitive audit, including private/generated declarations.
-- All inherited results are additionally carried in the complete delivery manifest.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mod := `ClusterSkeleton.DominanceCutoff
  unless env.header.moduleNames.contains mod do
    throwError "Missing defining module {mod}"
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
    unless env.contains name do
      throwError "Missing attribution-sensitive root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut moduleCount : Nat := 0
  let mut otherCount : Nat := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => env.header.moduleNames[i]! == mod
    if defining || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if defining then moduleCount := moduleCount + 1 else otherCount := otherCount + 1
  if moduleCount == 0 then throwError "No declarations audited for {mod}"
  logInfo m!"AUDITED {mod}: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
