import ClusterSkeleton.ZeroStratumPartnerDynamics
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry ZeroStratumPartnerDynamics

namespace ZeroStratumPartnerDynamicsConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Literal native derivative, zero-set invariance and the integrated law together. -/
theorem native_composition {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    letI := SmoothAtlas.charts S hdet
    (γ s).zeroSet = (γ t).zeroSet ∧
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      (fun r : S.Point => Complex.normSq (normalizedPartner r i)) (γ t)
      (GlobalLiouvilleField.Z S hdet ε κ hδ (γ t)) =
        2*(1+κ)*Complex.normSq (normalizedPartner (γ t) i) ∧
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ t) i)) J t ∧
    Complex.normSq (normalizedPartner (γ t) i) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq (normalizedPartner (γ s) i) := by
  refine ⟨ZeroStratumInvariance.zeroSet_eq S hdet hε hκ hδ hγ hJ hs ht, ?_,
    normSq_hasDerivWithinAt S hdet hε hκ hδ hγ hJ hs ht i ha,
    normSq_eq_exp_mul S hdet hε hκ hδ hγ hJ hs ht i ha⟩
  exact NormalizedPartnerNormDrift.normSq_drift_zero S hdet hε hκ hδ (γ t) i
    ((ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs ht i).mp ha)

theorem both_time_directions {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    Complex.normSq (normalizedPartner (γ t) i) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq (normalizedPartner (γ s) i) ∧
    Complex.normSq (normalizedPartner (γ s) i) =
      Real.exp (2*(1+κ)*(s-t))*Complex.normSq (normalizedPartner (γ t) i) ∧
    (normalizedPartner (γ t) i = 0 ↔ normalizedPartner (γ s) i = 0) ∧
    (normalizedPartner (γ t) i ≠ 0 ↔ normalizedPartner (γ s) i ≠ 0) := by
  have hat := (ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs ht i).mp ha
  exact ⟨normSq_eq_exp_mul S hdet hε hκ hδ hγ hJ hs ht i ha,
    normSq_eq_exp_mul S hdet hε hκ hδ hγ hJ ht hs i hat,
    (partner_zero_iff S hdet hε hκ hδ hγ hJ hs ht i ha).symm,
    (partner_ne_zero_iff S hdet hε hκ hδ hγ hJ hs ht i ha).symm⟩

theorem strict_growth {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (i : S.Mutable) (ha : (γ s).a i = 0) (hb : normalizedPartner (γ s) i ≠ 0)
    (hst : s < t) :
    Complex.normSq (normalizedPartner (γ s) i) < Complex.normSq (normalizedPartner (γ t) i) ∧
    StrictMonoOn (fun u => Complex.normSq (normalizedPartner (γ u) i)) J :=
  ⟨normSq_lt S hdet hε hκ hδ hγ hJ hs ht i ha hb hst,
    strictMonoOn_normSq S hdet hε hκ hδ hγ hJ hs i ha hb⟩

theorem closed_interval_endpoints {ε κ δ a b : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hab : a ≤ b) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Icc a b))
    (i : S.Mutable) (ha : (γ a).a i = 0) :
    Complex.normSq (normalizedPartner (γ b) i) =
      Real.exp (2*(1+κ)*(b-a))*Complex.normSq (normalizedPartner (γ a) i) ∧
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ a) i)) (Icc a b) a ∧
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ b) i)) (Icc a b) b :=
  ⟨normSq_eq_exp_mul S hdet hε hκ hδ hγ isPreconnected_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ i ha,
    normSq_hasDerivWithinAt S hdet hε hκ hδ hγ isPreconnected_Icc ⟨le_rfl, hab⟩ ⟨le_rfl, hab⟩ i ha,
    normSq_hasDerivWithinAt S hdet hε hκ hδ hγ isPreconnected_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ i ha⟩

theorem singleton_domain {ε κ δ a : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) {a}) {s t : ℝ}
    (hs : s ∈ ({a} : Set ℝ)) (ht : t ∈ ({a} : Set ℝ))
    (i : S.Mutable) (ha : (γ s).a i = 0) :
    Complex.normSq (normalizedPartner (γ t) i) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq (normalizedPartner (γ s) i) ∧
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ t) i)) {a} t :=
  ⟨normSq_eq_exp_mul S hdet hε hκ hδ hγ isPreconnected_singleton hs ht i ha,
    normSq_hasDerivWithinAt S hdet hε hκ hδ hγ isPreconnected_singleton hs ht i ha⟩

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

theorem double_partners (u v : ℂ) :
    normalizedPartner (doubleBoundary u v) ⟨0, by simp [pairSeed]⟩ = u ∧
    normalizedPartner (doubleBoundary u v) ⟨2, by simp [pairSeed]⟩ = v := by
  simp [normalizedPartner, doubleBoundary, Seed.Point.a, Seed.Point.b,
    Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]

/-- Arbitrary A₂ partner, with a genuine native curve as the only dynamical input. -/
theorem a2_arbitrary_partner_curve (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → Examples.a2Seed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hstart : γ s = boundaryPoint w) :
    (γ t).a 0 = 0 ∧
    Complex.normSq (normalizedPartner (γ t) ⟨0, by simp [Examples.a2Seed]⟩) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq w := by
  have ha : (γ s).a 0 = 0 := by rw [hstart]; rfl
  refine ⟨(ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ hγ hJ hs ht 0).mp ha, ?_⟩
  simpa only [hstart, a2_partner] using normSq_eq_exp_mul _ _ hε hκ hδ hγ hJ hs ht
    ⟨0, by simp [Examples.a2Seed]⟩ ha

theorem a2_zero_partner_curve {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → Examples.a2Seed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hstart : γ s = boundaryPoint 0) :
    (γ t).a 0 = 0 ∧ normalizedPartner (γ t) ⟨0, by simp [Examples.a2Seed]⟩ = 0 := by
  have h := a2_arbitrary_partner_curve 0 hε hκ hδ hγ hJ hs ht hstart
  exact ⟨h.1, Complex.normSq_eq_zero.mp (by simpa using h.2)⟩

theorem simultaneous_partners_curve (u v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → pairSeed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hstart : γ s = doubleBoundary u v) :
    (γ t).a 0 = 0 ∧ (γ t).a 2 = 0 ∧
    Complex.normSq (normalizedPartner (γ t) ⟨0, by simp [pairSeed]⟩) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq u ∧
    Complex.normSq (normalizedPartner (γ t) ⟨2, by simp [pairSeed]⟩) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq v := by
  have h0 : (γ s).a 0 = 0 := by rw [hstart]; rfl
  have h2 : (γ s).a 2 = 0 := by rw [hstart]; rfl
  refine ⟨(ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ hγ hJ hs ht 0).mp h0,
    (ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ hγ hJ hs ht 2).mp h2, ?_, ?_⟩
  · simpa only [hstart, (double_partners u v).1] using
      normSq_eq_exp_mul _ _ hε hκ hδ hγ hJ hs ht ⟨0, by simp [pairSeed]⟩ h0
  · simpa only [hstart, (double_partners u v).2] using
      normSq_eq_exp_mul _ _ hε hκ hδ hγ hJ hs ht ⟨2, by simp [pairSeed]⟩ h2

/-- A zero partner and a nonzero partner may occur simultaneously. -/
theorem simultaneous_zero_and_growing_partner (v : ℂ) (hv : v ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → pairSeed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s < t)
    (hstart : γ s = doubleBoundary 0 v) :
    normalizedPartner (γ t) ⟨0, by simp [pairSeed]⟩ = 0 ∧
    Complex.normSq v < Complex.normSq (normalizedPartner (γ t) ⟨2, by simp [pairSeed]⟩) := by
  have h := simultaneous_partners_curve 0 v hε hκ hδ hγ hJ hs ht hstart
  refine ⟨Complex.normSq_eq_zero.mp (by simpa using h.2.2.1), ?_⟩
  have ha : (γ s).a 2 = 0 := by rw [hstart]; rfl
  have hb : normalizedPartner (γ s) ⟨2, by simp [pairSeed]⟩ ≠ 0 := by
    simpa only [hstart, (double_partners 0 v).2] using hv
  simpa only [hstart, (double_partners 0 v).2] using
    normSq_lt _ _ hε hκ hδ hγ hJ hs ht ⟨2, by simp [pairSeed]⟩ ha hb hst

/-- The frozen coordinate z remains a variable, independent of the initial partner w. -/
theorem variable_frozen_curve (w z : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → pairSeed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hstart : γ s = variableFrozenBoundary w z hz) :
    (γ s).a 3 = z ∧ (γ t).a 3 ≠ 0 ∧ (γ t).a 0 = 0 ∧
    Complex.normSq (normalizedPartner (γ t) ⟨0, by simp [pairSeed]⟩) =
      Real.exp (2*(1+κ)*(t-s))*Complex.normSq w := by
  have ha : (γ s).a 0 = 0 := by rw [hstart]; rfl
  have hb : normalizedPartner (variableFrozenBoundary w z hz) ⟨0, by simp [pairSeed]⟩ = w := by
    simp [normalizedPartner, variableFrozenBoundary, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
  refine ⟨by rw [hstart]; rfl, (γ t).frozen_ne_zero 3 (by simp [pairSeed]),
    (ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ hγ hJ hs ht 0).mp ha, ?_⟩
  simpa only [hstart, hb] using
    normSq_eq_exp_mul _ _ hε hκ hδ hγ hJ hs ht ⟨0, by simp [pairSeed]⟩ ha

theorem empty_mutable_scope (hM : S.mutable = ∅) (q : S.Point) :
    q.zeroSet = ∅ ∧ IsEmpty S.Mutable := by
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hm := ((q.mem_zeroSet i).mp hi).1
    simpa only [hM, Finset.notMem_empty] using hm
  · exact ⟨fun i => by simpa only [hM, Finset.notMem_empty] using i.property⟩

theorem frozen_only_family (t : ℝ) :
    (frozenPoint t).a 0 = (Real.exp t : ℂ) ∧
    (frozenPoint t).zeroSet = ∅ ∧ IsEmpty frozenSeed.Mutable := by
  refine ⟨?_, empty_mutable_scope frozenSeed rfl _⟩
  simp [frozenPoint]

/-- An actual native all-time curve exists in dimension zero; there is no mutable index. -/
theorem dimension_zero_native_curve (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts emptySeed empty_unimodular
    IsMIntegralCurve (I := 𝓘(ℝ, Model 0)) (fun _ : ℝ => emptySeed.unitPoint)
      (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ) ∧
    IsEmpty emptySeed.Mutable := by
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  refine ⟨?_, ⟨fun i => Fin.elim0 i.val⟩⟩
  intro t
  have hz : GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ emptySeed.unitPoint = 0 := by
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  rw [hz]
  convert (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model (2*0)))
    (x := t) emptySeed.unitPoint) using 1 <;> simp <;> rfl

end ZeroStratumPartnerDynamicsConsumer

-- Native audit using unchanged Lean.collectAxioms and accepted complete selector.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ZeroStratumPartnerDynamicsConsumer.boundaryPoint,
        `ZeroStratumPartnerDynamicsConsumer.pairSeed,
        `ZeroStratumPartnerDynamicsConsumer.frozenSeed,
        `ZeroStratumPartnerDynamicsConsumer.frozenPoint,
        `ZeroStratumPartnerDynamicsConsumer.emptySeed,
        `ZeroStratumPartnerDynamicsConsumer.doubleBoundary,
        `ZeroStratumPartnerDynamicsConsumer.variableFrozenBoundary,
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
  for mod in env.header.moduleNames do report := report.push s!"IMPORT {mod}"
  let required := #[`ClusterSkeleton.ZeroStratumPartnerDynamics, `ClusterSkeleton.ZeroStratumInvariance, `ClusterSkeleton.NormalizedPartnerNormDrift, `ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "zero-stratum-partner-dynamics-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
