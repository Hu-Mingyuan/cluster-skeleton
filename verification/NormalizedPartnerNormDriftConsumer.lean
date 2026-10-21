import ClusterSkeleton.NormalizedPartnerNormDrift
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Manifold ContDiff Topology BigOperators ComplexConjugate
open Set Filter ClusterSkeleton FsFltz.Geometry NormalizedPartnerNormDrift

namespace NormalizedPartnerNormDriftConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The literal native derivative, with the full requested parameter regime. -/
theorem generic_native {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      (fun r : S.Point => Complex.normSq (normalizedPartner r i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
      2 * (conj (normalizedPartner q i) * (q.a i * normalizedPartner q i - 1) *
        nodeLogQuotient (q.a i, normalizedPartner q i)).re +
          2*κ*Complex.normSq (normalizedPartner q i) :=
  normSq_drift S hdet hε hκ hδ p q hq i hi

theorem arbitrary_zero_native {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (q : S.Point) (i : S.Mutable) (ha : q.a i = 0) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      (fun r : S.Point => Complex.normSq (normalizedPartner r i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
        2*(1+κ)*Complex.normSq (normalizedPartner q i) :=
  normSq_drift_zero S hdet hε hκ hδ q i ha

theorem genuine_curve_local {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p →
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2 * (conj (normalizedPartner (γ t) i) * ((γ t).a i * normalizedPartner (γ t) i - 1) *
        nodeLogQuotient ((γ t).a i, normalizedPartner (γ t) i)).re +
          2*κ*Complex.normSq (normalizedPartner (γ t) i)) s t :=
  normSq_hasDerivWithinAt S hdet hε hκ hδ p i hi

theorem genuine_curve_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (i : S.Mutable) {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    (γ t).a i = 0 →
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ t) i)) s t :=
  normSq_hasDerivWithinAt_zero S hdet hε hκ hδ i

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


theorem a2_partner (w : ℂ) :
    normalizedPartner (boundaryPoint w) ⟨0, by simp [Examples.a2Seed]⟩ = w := by
  simp [normalizedPartner, boundaryPoint, Seed.Point.a, Seed.Point.b,
    Seed.negativeMonomial, Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]

theorem a2_arbitrary_partner (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r ⟨0, by simp [Examples.a2Seed]⟩))
      (boundaryPoint w) (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular
        ε κ hδ (boundaryPoint w)) = 2*(1+κ)*Complex.normSq w := by
  simpa only [a2_partner] using normSq_drift_zero Examples.a2Seed Examples.a2Seed_unimodular
    hε hκ hδ (boundaryPoint w) ⟨0, by simp [Examples.a2Seed]⟩ rfl

theorem a2_zero_partner {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r ⟨0, by simp [Examples.a2Seed]⟩))
      (boundaryPoint 0) (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular
        ε κ hδ (boundaryPoint 0)) = 0 := by
  simpa using a2_arbitrary_partner 0 hε hκ hδ

theorem double_partners (u v : ℂ) :
    normalizedPartner (doubleBoundary u v) ⟨0, by simp [pairSeed]⟩ = u ∧
    normalizedPartner (doubleBoundary u v) ⟨2, by simp [pairSeed]⟩ = v := by
  simp [normalizedPartner, doubleBoundary, Seed.Point.a, Seed.Point.b,
    Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]

theorem simultaneous_zero_norms (u v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r ⟨0, by simp [pairSeed]⟩)) (doubleBoundary u v)
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (doubleBoundary u v)) =
        2*(1+κ)*Complex.normSq u ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r ⟨2, by simp [pairSeed]⟩)) (doubleBoundary u v)
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (doubleBoundary u v)) =
        2*(1+κ)*Complex.normSq v := by
  constructor
  · simpa only [(double_partners u v).1] using normSq_drift_zero pairSeed pair_unimodular
      hε hκ hδ (doubleBoundary u v) ⟨0, by simp [pairSeed]⟩ rfl
  · simpa only [(double_partners u v).2] using normSq_drift_zero pairSeed pair_unimodular
      hε hκ hδ (doubleBoundary u v) ⟨2, by simp [pairSeed]⟩ rfl

/-- A nonzero selected coordinate and partner, with the other mutable coordinate zero.
The frozen coordinate varies and never vanishes. -/
def mixedPoint (t : ℝ) (v : ℂ) : pairSeed.Point :=
  ⟨(![1-(Real.exp t : ℂ), -(Real.exp t : ℂ), 0, -1],
    fun j => if (j : Fin 4) = 0 then 1 else v), by
    constructor
    · intro j
      have hj := j.property
      simp only [pairSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
      ring
    · intro j hj
      fin_cases j <;> simp_all [pairSeed]⟩

theorem mixed_zero (v : ℂ) : mixedPoint 0 v = doubleBoundary 1 v := by
  apply Subtype.ext
  simp [mixedPoint, doubleBoundary]

theorem continuous_mixedPoint (v : ℂ) : Continuous (fun t => mixedPoint t v) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    fin_cases j <;> fun_prop
  · exact continuous_const

theorem mixed_coordinates (t : ℝ) (v : ℂ) (ht : t ≠ 0) :
    (mixedPoint t v).a 0 ≠ 0 ∧ (mixedPoint t v).a 2 = 0 ∧
    normalizedPartner (mixedPoint t v) ⟨0, by simp [pairSeed]⟩ = 1 := by
  refine ⟨?_, rfl, ?_⟩
  · change 1 - (Real.exp t : ℂ) ≠ 0
    intro h
    have he : Real.exp t = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
    exact ht (Real.exp_injective (he.trans Real.exp_zero.symm))
  · simp [normalizedPartner, mixedPoint, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]

/-- An actual punctured mixed-stratum family in the SAME open neighborhood.
Its partner is one, so the density consumer does not reduce to a zero norm. -/
theorem mixed_norm_drift_eventually (v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      mixedPoint t v ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary 1 v) ∧
      (mixedPoint t v).a 0 ≠ 0 ∧ (mixedPoint t v).a 2 = 0 ∧
      normalizedPartner (mixedPoint t v) ⟨0, by simp [pairSeed]⟩ = 1 ∧
      (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
        (fun r => Complex.normSq (normalizedPartner r ⟨0, by simp [pairSeed]⟩)) (mixedPoint t v)
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (mixedPoint t v)) =
          2 * (((mixedPoint t v).a 0 - 1) * nodeLogQuotient ((mixedPoint t v).a 0, 1)).re + 2*κ := by
  have hc : Tendsto (fun t => mixedPoint t v) (𝓝 0) (𝓝 (doubleBoundary 1 v)) := by
    simpa only [ContinuousAt, mixed_zero] using (continuous_mixedPoint v).continuousAt (x := 0)
  have hm := hc.eventually ((LocalPrimitive.isOpen_neighborhood pairSeed ε κ δ
    (doubleBoundary 1 v)).mem_nhds (LocalPrimitive.mem_neighborhood pairSeed ε κ hδ _))
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
  obtain ⟨ha, hz, hb⟩ := mixed_coordinates t v hn
  refine ⟨ht, ha, hz, hb, ?_⟩
  simpa only [hb, map_one, one_mul, mul_one, Complex.normSq_one] using
    normSq_drift pairSeed pair_unimodular hε hκ hδ (doubleBoundary 1 v) (mixedPoint t v) ht
      ⟨0, by simp [pairSeed]⟩ (by simp [Seed.Point.mem_zeroSet, pairSeed, doubleBoundary, Seed.Point.a])

theorem variable_frozen_norm (w z : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (variableFrozenBoundary w z hz).a 3 = z ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r ⟨0, by simp [pairSeed]⟩))
      (variableFrozenBoundary w z hz) (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ
        (variableFrozenBoundary w z hz)) = 2*(1+κ)*Complex.normSq w := by
  refine ⟨rfl, ?_⟩
  have hb : normalizedPartner (variableFrozenBoundary w z hz) ⟨0, by simp [pairSeed]⟩ = w := by
    simp [normalizedPartner, variableFrozenBoundary, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
  simpa only [hb] using normSq_drift_zero pairSeed pair_unimodular hε hκ hδ
    (variableFrozenBoundary w z hz) ⟨0, by simp [pairSeed]⟩ rfl

theorem empty_mutable (hM : S.mutable = ∅) (q : S.Point) :
    q.zeroSet = ∅ ∧ IsEmpty S.Mutable := by
  constructor
  · ext i
    simp [hM]
  · exact ⟨fun i => by simpa [hM] using i.property⟩

theorem frozen_only_family (t : ℝ) :
    (frozenPoint t).a 0 = (Real.exp t : ℂ) ∧
    (frozenPoint t).zeroSet = ∅ ∧ IsEmpty frozenSeed.Mutable := by
  refine ⟨?_, empty_mutable frozenSeed rfl (frozenPoint t)⟩
  simp [frozenPoint, pointOfCoordinateTorus, torusCoordinates, Seed.Point.a]

/-- An inhabited zero-dimensional exchange space has no mutable norm equations. -/
theorem dimension_zero (c : ℂ) (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    let q := pointOfCoordinateTorus emptySeed (fun j => Fin.elim0 j)
    q.zeroSet = ∅ ∧ IsEmpty emptySeed.Mutable ∧
    (SmoothAtlas.presentation emptySeed empty_unimodular).manifold.scalarDerivative
      (fun _ => Complex.normSq c) q (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ q) = 0 := by
  let q := pointOfCoordinateTorus emptySeed (fun j => Fin.elim0 j)
  refine ⟨(empty_mutable emptySeed rfl q).1, (empty_mutable emptySeed rfl q).2, ?_⟩
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  change mfderiv 𝓘(ℝ, Model (2*0)) 𝓘(ℝ, ℝ) (fun _ : emptySeed.Point => Complex.normSq c) q _ = 0
  rw [mfderiv_const]
  rfl

end NormalizedPartnerNormDriftConsumer

-- Native transitive audit of the entire imported project closure, including
-- all private/generated roots and explicit attribution-sensitive supplements.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`NormalizedPartnerNormDriftConsumer.boundaryPoint, `NormalizedPartnerNormDriftConsumer.frozenSeed,
        `NormalizedPartnerNormDriftConsumer.frozenPoint, `NormalizedPartnerNormDriftConsumer.emptySeed,
        `NormalizedPartnerNormDriftConsumer.pairSeed, `NormalizedPartnerNormDriftConsumer.doubleBoundary,
        `NormalizedPartnerNormDriftConsumer.mixedPoint, `NormalizedPartnerNormDriftConsumer.variableFrozenBoundary,
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
  let required := #[`ClusterSkeleton.NormalizedPartnerNormDrift, `ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "normalized-partner-norm-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
