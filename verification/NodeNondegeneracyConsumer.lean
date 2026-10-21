import ClusterSkeleton.NodeNondegeneracy
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
open ClusterSkeleton ClusterSkeleton.NodeTwoForm ClusterSkeleton.NodeNondegeneracy
open ClusterSkeleton.IndependentNodeChart FsFltz.Geometry
namespace NodeNondegeneracyConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The residual matrix is not supplied with a nondegeneracy certificate. -/
theorem residual (I : Finset (Fin d)) (hI : S.Independent I) :
    IsUnit (complementMatrix S I hdet hI) := complementMatrix_isUnit S I hdet hI

/-- The chart, zero set, and native tangent fiber are all the constructed ones. -/
theorem actual_point (p : S.Point)
    (a : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (ha : ∀ b, SmoothManifold.evalTwo
      (localForm S p.zeroSet hdet p.zeroSet_independent) p a b = 0) : a = 0 :=
  zeroSet_localForm_nondegenerate S hdet p a ha

/-- Empty independent set, on any seed, without a dimension restriction. -/
theorem empty_nodes (x : Vector S ∅) (hx : x ∈ domain S ∅)
    (a : Vector S ∅)
    (ha : ∀ b, realForm S ∅ hdet (by simp [Seed.Independent]) x ![a,b] = 0) : a = 0 :=
  realForm_boundary_nondegenerate S ∅ hdet (by simp [Seed.Independent]) x hx
    (by intro i; exact False.elim (Finset.notMem_empty i.val i.property)) a ha

/-- An inhabited zero-dimensional model. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem emptySeed_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem emptySeed_inhabited : Nonempty emptySeed.Point := ⟨emptySeed.unitPoint⟩

theorem dimension_zero
    (a : (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Tangent
      emptySeed.unitPoint)
    (ha : ∀ b, SmoothManifold.evalTwo
      (localForm emptySeed emptySeed.unitPoint.zeroSet emptySeed_unimodular
        emptySeed.unitPoint.zeroSet_independent) emptySeed.unitPoint a b = 0) : a = 0 :=
  actual_point emptySeed emptySeed_unimodular emptySeed.unitPoint a ha

open ClusterSkeleton.Examples

/-- The A₂ chart at a single vanishing coordinate has no residual free factors. -/
theorem a2_singleton_independent : a2Seed.Independent {0} := by
  simp [Seed.Independent, a2Seed, a2Matrix]

theorem a2_complement_card_zero : Fintype.card (Complement a2Seed {0}) = 0 := by
  have h := basis_cardinality a2Seed {0} a2Seed_unimodular a2_singleton_independent
  have hc : Fintype.card {j : Fin 2 // j ∉ ({0} : Finset (Fin 2))} = 1 := by decide
  simpa [hc] using h

/-- Both coordinates of the node vanish at this actual, nonempty boundary point. -/
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

theorem a2_boundary_partner_zero : a2BoundaryPoint.b ⟨0, by simp [a2Seed]⟩ = 0 := by
  simp [a2BoundaryPoint, Seed.Point.b]

theorem a2_boundary_nondegenerate
    (a : (SmoothAtlas.presentation a2Seed a2Seed_unimodular).manifold.Tangent a2BoundaryPoint)
    (ha : ∀ b, SmoothManifold.evalTwo
      (localForm a2Seed a2BoundaryPoint.zeroSet a2Seed_unimodular
        a2BoundaryPoint.zeroSet_independent) a2BoundaryPoint a b = 0) : a = 0 :=
  actual_point a2Seed a2Seed_unimodular a2BoundaryPoint a ha

end NodeNondegeneracyConsumer

-- One environment traversal, with native transitive axiom collection for EVERY
-- declaration in the defining module (including private/generated declarations)
-- and every declaration in this consumer. No global baseline audit is repeated.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut moduleCount : Nat := 0
  let mut consumerCount : Nat := 0
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let moduleRoot := match idx with
      | some i => env.header.moduleNames[i]! == `ClusterSkeleton.NodeNondegeneracy
      | none => false
    let namedRoot := name.toString.startsWith "ClusterSkeleton.NodeNondegeneracy." ||
      name.toString.startsWith "_private.ClusterSkeleton.NodeNondegeneracy."
    if moduleRoot || namedRoot || idx.isNone then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if moduleRoot || namedRoot then moduleCount := moduleCount + 1
      else consumerCount := consumerCount + 1
  if moduleCount == 0 || consumerCount == 0 then
    throwError "Missing module or consumer declarations: {moduleCount}, {consumerCount}"
  logInfo m!"AUDITED NodeNondegeneracy={moduleCount} consumer={consumerCount}"
