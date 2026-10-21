import ClusterSkeleton.AllStrataGrowth
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

/-! This checking file follows byte-identical accepted proof ranges in the
private combined checker. Inherited audit-only commands are omitted; exact
ranges and EOF scope restoration are recorded in its manifest. The accepted
angular and native radial fixtures are referenced by their original names;
this file neither copies nor replaces those fixtures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.AllStrataGrowth

namespace AllStrataGrowthConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The four estimates retain the actual native logarithmic components and
the actual differential of the normalized partner. -/
def GrowthAt (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (C : ℝ) (p : S.Point) : Prop :=
  (∑ j ∈ p.zeroSetᶜ,
    |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re|) ≤
      C * R S p ∧
  (∑ j : Fin d, |LocalAngularDynamics.nu S ε κ δ p p j|) ≤ C * (1 + R S p) ∧
  (∑ j ∈ p.zeroSetᶜ,
    (|(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re| +
    |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im|)) ≤
      C * (1 + R S p) ∧
  ∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet →
    ‖BoundaryTangency.drift S hdet ε κ hδ (fun q => normalizedPartner q i) p‖ ≤
      C * (1 + R S p) * ‖normalizedPartner p i‖

/-- One constant works for every actual point and every zero stratum. -/
theorem uniform_native_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : S.Point, GrowthAt S hdet ε κ hδ C p :=
  AllStrataGrowth.uniform_growth S hdet hε hκ hδ

/-- A nonzero selected coordinate is controlled even when other coordinates
vanish. No torus premise occurs in this consequence. -/
theorem selected_coordinate {ε κ δ C : ℝ} (hδ : 0 < δ) (p : S.Point)
    (hp : GrowthAt S hdet ε κ hδ C p) (j : Fin d) (hj : p.a j ≠ 0) :
    |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re| ≤ C * R S p ∧
    (|(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).re| +
      |(GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p j).im|) ≤
        C * (1 + R S p) := by
  classical
  have hm : j ∈ p.zeroSetᶜ := by
    simp only [Finset.mem_compl, Seed.Point.mem_zeroSet]
    exact fun h => hj h.2
  exact ⟨(Finset.single_le_sum (fun k _ => abs_nonneg
      (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p k).re) hm).trans hp.1,
    (Finset.single_le_sum (fun k _ => add_nonneg
      (abs_nonneg (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p k).re)
      (abs_nonneg (GlobalLiouvilleField.logarithmicComponents S hdet ε κ hδ p k).im)) hm).trans
        hp.2.2.1⟩

/-- This identity only evaluates the masked size; it asserts no regularity
across strata for the totalized real logarithm. -/
theorem R_eq_log_norm_sum (p : S.Point) :
    R S p = ∑ j : Fin d, |Real.log ‖p.a j‖| := by
  classical
  unfold R
  apply Finset.sum_congr rfl
  intro j _
  unfold LocalAngularDynamics.maskedLogs
  split_ifs with hj
  · simp [(p.mem_zeroSet j).mp hj |>.2]
  · rfl

/-- The exchange carrier and its induced topology are unchanged. -/
theorem literal_carrier_and_frozen (p : S.Point) :
    Continuous (fun q : S.Point => q.val) ∧
    (∀ i : S.Mutable, p.a i*p.b i = S.positiveMonomial p.a i+S.negativeMonomial p.a i) ∧
    ∀ f : Fin d, f ∉ S.mutable → p.a f ≠ 0 :=
  ⟨continuous_subtype_val, p.exchange, p.frozen_ne_zero⟩

section Triple
open NativeRadialOrbitConsumer

theorem triple_size (x : ℝ) (u v : ℂ) :
    R tripleSeed (triplePoint x u v) = |x| := by
  rw [R_eq_log_norm_sum]
  simp [triplePoint, Seed.Point.a, Fin.sum_univ_succ, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos x), Real.log_exp]

theorem triple_partners (x : ℝ) (u v : ℂ) :
    normalizedPartner (triplePoint x u v) ⟨2, by simp [tripleSeed]⟩ = u ∧
    normalizedPartner (triplePoint x u v) ⟨4, by simp [tripleSeed]⟩ = v := by
  simp [normalizedPartner, triplePoint, Seed.Point.a, Seed.Point.b,
    Seed.negativeMonomial, tripleSeed, Fin.prod_univ_succ]

/-- A single constant covers two independently arbitrary zero-coordinate
partners, including zero, together with the surviving selected coordinate. -/
theorem triple_uniform_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (u v : ℂ),
      (triplePoint x u v).zeroSet = {2,4} ∧
      (triplePoint x u v).a 0 ≠ 0 ∧
      R tripleSeed (triplePoint x u v) = |x| ∧
      GrowthAt tripleSeed triple_unimodular ε κ hδ C (triplePoint x u v) ∧
      |(GlobalLiouvilleField.logarithmicComponents tripleSeed triple_unimodular ε κ hδ
        (triplePoint x u v) 0).re| ≤ C * |x| ∧
      ‖BoundaryTangency.drift tripleSeed triple_unimodular ε κ hδ
        (fun q => normalizedPartner q ⟨2, by simp [tripleSeed]⟩) (triplePoint x u v)‖ ≤
          C * (1 + |x|) * ‖u‖ ∧
      ‖BoundaryTangency.drift tripleSeed triple_unimodular ε κ hδ
        (fun q => normalizedPartner q ⟨4, by simp [tripleSeed]⟩) (triplePoint x u v)‖ ≤
          C * (1 + |x|) * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := uniform_native_growth tripleSeed triple_unimodular hε hκ hδ
  refine ⟨C, hC, fun x u v => ?_⟩
  have hp := hb (triplePoint x u v)
  refine ⟨triple_zeroSet x u v, triple_selected_nonzero x u v, triple_size x u v, hp, ?_, ?_, ?_⟩
  · simpa only [triple_size] using (selected_coordinate tripleSeed triple_unimodular hδ
      (triplePoint x u v) hp 0 (triple_selected_nonzero x u v)).1
  · simpa only [triple_size, (triple_partners x u v).1] using
      hp.2.2.2 ⟨2, by simp [tripleSeed]⟩ (by rw [triple_zeroSet]; simp)
  · simpa only [triple_size, (triple_partners x u v).2] using
      hp.2.2.2 ⟨4, by simp [tripleSeed]⟩ (by rw [triple_zeroSet]; simp)

/-- The homogeneous partner estimate really includes both partners equal to
zero; its native drift then vanishes. -/
theorem triple_zero_partners {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (x : ℝ) :
    BoundaryTangency.drift tripleSeed triple_unimodular ε κ hδ
      (fun q => normalizedPartner q ⟨2, by simp [tripleSeed]⟩) (triplePoint x 0 0) = 0 ∧
    BoundaryTangency.drift tripleSeed triple_unimodular ε κ hδ
      (fun q => normalizedPartner q ⟨4, by simp [tripleSeed]⟩) (triplePoint x 0 0) = 0 := by
  obtain ⟨C, _, hb⟩ := triple_uniform_growth hε hκ hδ
  have hp := hb x 0 0
  constructor
  · exact norm_eq_zero.mp (le_antisymm (by simpa using hp.2.2.2.2.2.1) (norm_nonneg _))
  · exact norm_eq_zero.mp (le_antisymm (by simpa using hp.2.2.2.2.2.2) (norm_nonneg _))

/-- On the honest open time domain (5,∞), with initial time 7, the same
constant controls every actual curve. Both zero coordinates persist, the
selected coordinate has ordinary real and complex logarithmic derivatives,
and both arbitrary normalized partners have their actual ordinary derivatives.
Each complex logarithm is centered at the current time. -/
theorem triple_open_time_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (u v : ℂ) (γ : ℝ → tripleSeed.Point),
      (letI := SmoothAtlas.charts tripleSeed triple_unimodular;
        IsMIntegralCurveOn (I := 𝓘(ℝ, Model 12)) γ
          (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) (Ioi 5)) →
      γ 7 = triplePoint x u v → ∀ t > 5,
      (γ t).zeroSet = {2,4} ∧
      R tripleSeed (γ t) =
        (∑ j : Fin 6, |LocalAngularDynamics.maskedLogs tripleSeed {2,4} (γ t) j|) ∧
      GrowthAt tripleSeed triple_unimodular ε κ hδ C (γ t) ∧
      HasDerivAt (fun s => GlobalLiouvilleField.A tripleSeed (γ s) 0)
        (GlobalLiouvilleField.logarithmicComponents tripleSeed triple_unimodular ε κ hδ
          (γ t) 0).re t ∧
      HasDerivAt (fun s => Complex.log ((γ s).a 0 / (γ t).a 0))
        (GlobalLiouvilleField.logarithmicComponents tripleSeed triple_unimodular ε κ hδ
          (γ t) 0) t ∧
      ∀ i : tripleSeed.Mutable, (i : Fin 6) ∈ ({2,4} : Finset (Fin 6)) →
        HasDerivAt (fun s => normalizedPartner (γ s) i)
          (BoundaryTangency.drift tripleSeed triple_unimodular ε κ hδ
            (fun q => normalizedPartner q i) (γ t)) t ∧
        ‖BoundaryTangency.drift tripleSeed triple_unimodular ε κ hδ
          (fun q => normalizedPartner q i) (γ t)‖ ≤
            C * (1 + R tripleSeed (γ t)) * ‖normalizedPartner (γ t) i‖ := by
  obtain ⟨C, hC, hb⟩ := integralCurve_growth tripleSeed triple_unimodular hε hκ hδ
  refine ⟨C, hC, fun x u v γ hγ hinit t ht => ?_⟩
  have h := hb γ (Ioi 5) 7 hγ isPreconnected_Ioi (by norm_num) t ht
  dsimp only at h
  rw [hinit, triple_zeroSet] at h
  have hR : R tripleSeed (γ t) =
      ∑ j : Fin 6, |LocalAngularDynamics.maskedLogs tripleSeed {2,4} (γ t) j| := by
    unfold R
    rw [h.1]
  have hp : GrowthAt tripleSeed triple_unimodular ε κ hδ C (γ t) := by
    unfold GrowthAt
    rw [h.1, hR]
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun i hi => (h.2.2.2.2.2 i hi).2⟩
  have hs := h.2.1 0 (by simp)
  refine ⟨h.1, hR, hp, ?_, hs.2.hasDerivAt (isOpen_Ioi.mem_nhds ht), ?_⟩
  · simpa [LocalAngularDynamics.maskedLogs, GlobalLiouvilleField.A] using
      hs.1.hasDerivAt (isOpen_Ioi.mem_nhds ht)
  · intro i hi
    exact ⟨(h.2.2.2.2.2 i hi).1.hasDerivAt (isOpen_Ioi.mem_nhds ht),
      by simpa only [hR] using (h.2.2.2.2.2 i hi).2⟩
end Triple

section Angular
open LocalAngularDynamicsConsumer

theorem a4_size (w : ℂ) (x t : ℝ) : R a4Seed (a4Boundary w x t) = |x| := by
  rw [R_eq_log_norm_sum]
  change (∑ j : Fin 4, |DominanceCutoff.logNorms a4Seed (a4Boundary w x t) j|) = |x|
  rw [a4_logs]
  simp [Fin.sum_univ_succ]

/-- The angular example has a proved nonzero surviving correction. The same
constant bounds its full native field and every arbitrary complex partner. -/
theorem a4_nonvacuous_uniform_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ,
      let p := a4Boundary w (-5) (Real.pi/8)
      p.zeroSet = {0} ∧ a4v2 ∈ RegularCorrection.surviving a4Seed p.zeroSet ∧
      PrimitiveLocalization.correction 1 3 (Real.pi/2) a4v2 p ≠ 0 ∧
      R a4Seed p = 5 ∧
      GrowthAt a4Seed a4_unimodular 1 3 (by positivity : 0 < Real.pi/2) C p ∧
      ‖BoundaryTangency.drift a4Seed a4_unimodular 1 3 (by positivity : 0 < Real.pi/2)
        (fun q => normalizedPartner q a4v0) p‖ ≤ C * 6 * ‖w‖ := by
  obtain ⟨C, hC, hb⟩ := uniform_native_growth a4Seed a4_unimodular
    (by norm_num : (0:ℝ)<1) (by norm_num : (2:ℝ)*1+1≤3) (by positivity : 0 < Real.pi/2)
  refine ⟨C, hC, fun w => ?_⟩
  have hf := a4_nonvacuous w
  have hp := hb (a4Boundary w (-5) (Real.pi/8))
  refine ⟨hf.1, hf.2.1, hf.2.2.2, by simpa using a4_size w (-5) (Real.pi/8), hp, ?_⟩
  have hi : (a4v0 : Fin 4) ∈ (a4Boundary w (-5) (Real.pi/8)).zeroSet := by
    rw [a4_zeroSet]
    exact Finset.mem_singleton_self 0
  simpa only [a4_size, a4_partner, show |(-5:ℝ)|=5 by norm_num,
    show (1:ℝ)+5=6 by norm_num] using
    hp.2.2.2 a4v0 hi

theorem variable_frozen_size (w z : ℂ) (hz : z ≠ 0) :
    R pairSeed (variableFrozenBoundary w z hz) = |Real.log ‖z‖| := by
  rw [R_eq_log_norm_sum]
  simp [variableFrozenBoundary, Seed.Point.a, Fin.sum_univ_succ]

/-- The frozen coordinate z remains independently arbitrary and nonzero;
the estimate is uniform both in z and in the zero-coordinate partner w. -/
theorem variable_frozen_uniform_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : ℂ) (hz : z ≠ 0),
      (variableFrozenBoundary w z hz).a 3 = z ∧
      R pairSeed (variableFrozenBoundary w z hz) = |Real.log ‖z‖| ∧
      GrowthAt pairSeed pair_unimodular ε κ hδ C (variableFrozenBoundary w z hz) ∧
      ‖BoundaryTangency.drift pairSeed pair_unimodular ε κ hδ
        (fun q => normalizedPartner q ⟨0, by simp [pairSeed]⟩)
        (variableFrozenBoundary w z hz)‖ ≤ C * (1 + |Real.log ‖z‖|) * ‖w‖ := by
  obtain ⟨C, hC, hb⟩ := uniform_native_growth pairSeed pair_unimodular hε hκ hδ
  refine ⟨C, hC, fun w z hz => ?_⟩
  have hp := hb (variableFrozenBoundary w z hz)
  refine ⟨rfl, variable_frozen_size w z hz, hp, ?_⟩
  have hpartner : normalizedPartner (variableFrozenBoundary w z hz)
      ⟨0, by simp [pairSeed]⟩ = w := by
    simp [normalizedPartner, variableFrozenBoundary, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
  simpa only [variable_frozen_size, hpartner] using hp.2.2.2
    ⟨0, by simp [pairSeed]⟩
    (by simp [Seed.Point.mem_zeroSet, pairSeed, variableFrozenBoundary, Seed.Point.a])
end Angular

/-- The ordinary initial torus is included without restricting its coordinates. -/
theorem torus_uniform_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : CoordinateTorus d,
      (pointOfCoordinateTorus S a).zeroSet = ∅ ∧
      R S (pointOfCoordinateTorus S a) = (∑ j : Fin d, |Real.log ‖(a j).val‖|) ∧
      GrowthAt S hdet ε κ hδ C (pointOfCoordinateTorus S a) := by
  obtain ⟨C, hC, hb⟩ := uniform_native_growth S hdet hε hκ hδ
  refine ⟨C, hC, fun a => ⟨?_, R_eq_log_norm_sum S _, hb _⟩⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact (a j).property ((Seed.Point.mem_zeroSet _ _).mp hj).2

/-- An empty mutable set retains all original frozen variables and the full
matrix; the actual angular coefficients vanish. -/
theorem empty_mutable_uniform_growth (hM : S.mutable = ∅) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : S.Point,
      p.zeroSet = ∅ ∧ LocalAngularDynamics.nu S ε κ δ p p = 0 ∧
      GrowthAt S hdet ε κ hδ C p := by
  obtain ⟨C, hC, hb⟩ := uniform_native_growth S hdet hε hκ hδ
  refine ⟨C, hC, fun p => ⟨?_, LocalAngularDynamicsConsumer.empty_mutable_nu S hM ε κ δ p p, hb p⟩⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  simpa [hM] using ((p.mem_zeroSet j).mp hj).1

section Frozen
open NativeRadialOrbitConsumer

theorem frozen_size (x y : ℝ) : R frozenSeed (frozenPoint x y) = |x| + |y| := by
  rw [R_eq_log_norm_sum]
  simp [frozenPoint, Seed.Point.a, Fin.sum_univ_succ, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos x), abs_of_pos (Real.exp_pos y), Real.log_exp]

/-- Both frozen moduli vary independently over all positive real values. -/
theorem frozen_two_parameters {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖(frozenPoint x y).a 0‖ = Real.exp x ∧
      ‖(frozenPoint x y).a 1‖ = Real.exp y ∧
      R frozenSeed (frozenPoint x y) = |x| + |y| ∧
      LocalAngularDynamics.nu frozenSeed ε κ δ (frozenPoint x y) (frozenPoint x y) = 0 ∧
      GrowthAt frozenSeed frozen_unimodular ε κ hδ C (frozenPoint x y) := by
  obtain ⟨C, hC, hb⟩ := empty_mutable_uniform_growth frozenSeed frozen_unimodular rfl hε hκ hδ
  exact ⟨C, hC, fun x y => ⟨(frozen_norms x y).1, (frozen_norms x y).2,
    frozen_size x y, (hb _).2.1, (hb _).2.2⟩⟩

/-- Dimension zero still uses an inhabited actual seed and an already proved
native identity flow; the growth theorem applies to every point of its carrier. -/
theorem dimension_zero_application {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (letI := SmoothAtlas.charts emptySeed empty_unimodular;
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model 0))
        (fun t => Flow.id ℝ emptySeed.Point t p)
        (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ) univ) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ p : emptySeed.Point,
      R emptySeed p = 0 ∧ GrowthAt emptySeed empty_unimodular ε κ hδ C p := by
  obtain ⟨C, hC, hb⟩ := uniform_native_growth emptySeed empty_unimodular hε hκ hδ
  exact ⟨dimension_zero_flow_native ε κ hδ, C, hC,
    fun p => ⟨by simp [R], hb p⟩⟩
end Frozen

end AllStrataGrowthConsumer

-- Native audit: unchanged accepted collectAxioms selection and traversal.
section
set_option maxHeartbeats 800000

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let before ← getEnv
    for (name, info) in before.constants.toList do
      let idx := before.getModuleIdxFor? name
      let fresh := idx.any fun i => before.header.moduleNames[i]! == `ClusterSkeleton.AllStrataGrowth
      if fresh || idx.isNone then
        match info with
        | .defnInfo _ =>
          let _ ← Lean.Meta.getEqnsFor? name
          pure ()
        | _ => pure ()
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.NativeRadialOrbit.c, `NativeRadialOrbitConsumer.tripleSeed, `NativeRadialOrbitConsumer.triplePoint, `NativeRadialOrbitConsumer.frozenSeed, `NativeRadialOrbitConsumer.frozenPoint, `NativeRadialOrbitConsumer.emptySeed, `ClusterSkeleton.ScalarOrbitDynamics.RadialEquation, `ScalarOrbitDynamicsConsumer.frozenSeed, `ScalarOrbitDynamicsConsumer.variableFrozenPoint, `ClusterSkeleton.LocalAngularDynamics.maskedLogs, `ClusterSkeleton.LocalAngularDynamics.angularRhs, `ClusterSkeleton.LocalAngularDynamics.nu, `DynamicsCompositionConsumer.ZeroCurveLaws, `ZeroStratumEscapeConsumer.boundaryPoint,
        `ZeroStratumEscapeConsumer.reversedBoundary,
        `ZeroStratumEscapeConsumer.pairSeed,
        `ZeroStratumEscapeConsumer.frozenSeed,
        `ZeroStratumEscapeConsumer.frozenPoint,
        `ZeroStratumEscapeConsumer.emptySeed,
        `ZeroStratumEscapeConsumer.doubleBoundary,
        `ZeroStratumEscapeConsumer.variableFrozenBoundary,
        `ClusterSkeleton.BoundaryTangency.nodeProduct,
        `ClusterSkeleton.BoundaryTangency.drift,
        `ClusterSkeleton.BoundaryTangency.boundaryPerturb,
        `ClusterSkeleton.GlobalLiouvilleField.Z,
        `ClusterSkeleton.GlobalLiouvilleField.logarithmicComponents,
        `ClusterSkeleton.GlobalLiouvilleField.A,
        `ClusterSkeleton.GlobalLiouvilleField.L,
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
        `ClusterSkeleton.Seed.Point.a,
        `ClusterSkeleton.Seed.Point.b,
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
  for mod in env.header.moduleNames do
    report := report.push s!"IMPORT {mod}"
    let nativePath ← Lean.findOLean mod
    report := report.push s!"NATIVEPATH {mod}: {nativePath}"
  let required := #[`ClusterSkeleton.ZeroStratumEscape, `ClusterSkeleton.ZeroStratumPartnerDynamics, `ClusterSkeleton.ZeroStratumInvariance, `ClusterSkeleton.NormalizedPartnerNormDrift, `ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "all-strata-growth133-joint-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"

end
