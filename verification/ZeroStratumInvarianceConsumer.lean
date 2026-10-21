import ClusterSkeleton.BoundaryTangency
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms
import ClusterSkeleton.ZeroStratumInvariance

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry ZeroStratumInvariance

namespace ZeroStratumInvarianceConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The consumer spells out Mathlib mfderiv and the pinned scalarDerivative. -/
theorem literal_native_normSq {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      (fun r : S.Point => Complex.normSq (r.a i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) = -2*κ*Complex.normSq (q.a i) ∧
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) = -2*κ*Complex.normSq (q.a i) :=
  ⟨normSq_drift S hdet hε hκ hδ p q hq i hi,
    normSq_drift S hdet hε hκ hδ p q hq i hi⟩

theorem native_chain_bridge {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    {t : ℝ} (ht : t ∈ J) (hq : γ t ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    HasDerivWithinAt (fun s => (γ s).a i)
      ((SmoothAtlas.presentation S hdet).coordinateDifferential i (γ t)
        (GlobalLiouvilleField.Z S hdet ε κ hδ (γ t))) J t ∧
    HasDerivWithinAt (fun s => Complex.normSq ((γ s).a i))
      (-2*κ*Complex.normSq ((γ t).a i)) J t :=
  ⟨coordinate_hasDerivWithinAt S hdet hδ hγ ht i,
    normSq_hasDerivWithinAt S hdet hε hκ hδ p hγ ht hq i hi⟩

theorem preconnected_curve_both_directions {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {γ : ℝ → S.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (i : Fin d) :
    (γ s).zeroSet = (γ t).zeroSet ∧ (γ t).zeroSet = (γ s).zeroSet ∧
    ((γ s).a i = 0 ↔ (γ t).a i = 0) ∧ ((γ s).a i ≠ 0 ↔ (γ t).a i ≠ 0) :=
  ⟨zeroSet_eq S hdet hε hκ hδ hγ hJ hs ht,
    zeroSet_eq S hdet hε hκ hδ hγ hJ ht hs,
    coordinate_zero_iff S hdet hε hκ hδ hγ hJ hs ht i,
    coordinate_ne_zero_iff S hdet hε hκ hδ hγ hJ hs ht i⟩

/-- The derivative hypothesis is within the closed interval, at both endpoints. -/
theorem closed_interval_endpoints {ε κ δ a b : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hab : a ≤ b) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Icc a b)) (i : Fin d) :
    (γ a).zeroSet = (γ b).zeroSet ∧ ((γ b).a i = 0 ↔ (γ a).a i = 0) :=
  ⟨zeroSet_eq S hdet hε hκ hδ hγ isPreconnected_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩,
    coordinate_zero_iff S hdet hε hκ hδ hγ isPreconnected_Icc ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩ i⟩

theorem singleton_domain {ε κ δ a : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) {a}) {s t : ℝ}
    (hs : s ∈ ({a} : Set ℝ)) (ht : t ∈ ({a} : Set ℝ)) :
    (γ s).zeroSet = (γ t).zeroSet :=
  zeroSet_eq S hdet hε hκ hδ hγ isPreconnected_singleton hs ht

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


def selectedBoundary (z v : ℂ) : pairSeed.Point :=
  ⟨(![z,-1,0,-1], fun j => if (j : Fin 4) = 0 then 0 else v), by
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

theorem a2_boundary_local (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (q : Examples.a2Seed.Point)
    (hq : q ∈ LocalPrimitive.neighborhood Examples.a2Seed ε κ δ (boundaryPoint w)) :
    normalizedPartner (boundaryPoint w) ⟨0, by simp [Examples.a2Seed]⟩ = w ∧
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a 0)) q
      (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ q) =
        -2*κ*Complex.normSq (q.a 0) := by
  constructor
  · simp [normalizedPartner, boundaryPoint, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]
  · exact normSq_drift _ _ hε hκ hδ _ q hq ⟨0, by simp [Examples.a2Seed]⟩
      (by simp [Seed.Point.mem_zeroSet, Examples.a2Seed, boundaryPoint, Seed.Point.a])

theorem a2_zero_partner_local {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (q : Examples.a2Seed.Point)
    (hq : q ∈ LocalPrimitive.neighborhood Examples.a2Seed ε κ δ (boundaryPoint 0)) :
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a 0)) q
      (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ q) =
        -2*κ*Complex.normSq (q.a 0) := (a2_boundary_local 0 hε hκ hδ q hq).2

theorem a2_center (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation Examples.a2Seed Examples.a2Seed_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a 0)) (boundaryPoint w)
      (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ (boundaryPoint w)) = 0 := by
  simpa [boundary_coordinates] using
    (a2_boundary_local w hε hκ hδ _ (LocalPrimitive.mem_neighborhood _ ε κ hδ _)).2

theorem simultaneous_local (u v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (q : pairSeed.Point)
    (hq : q ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary u v)) :
    (∀ i : Fin 4, i ∈ ({0,2} : Finset (Fin 4)) →
      (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
        (fun r => Complex.normSq (r.a i)) q
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ q) = -2*κ*Complex.normSq (q.a i)) := by
  intro i hi
  have hm : i ∈ pairSeed.mutable := hi
  apply normSq_drift _ _ hε hκ hδ _ q hq ⟨i,hm⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp [Seed.Point.mem_zeroSet, doubleBoundary, Seed.Point.a, pairSeed]

theorem simultaneous_zero_partners_local {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (q : pairSeed.Point)
    (hq : q ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary 0 0)) :
    normalizedPartner (doubleBoundary 0 0) ⟨0, by simp [pairSeed]⟩ = 0 ∧
    normalizedPartner (doubleBoundary 0 0) ⟨2, by simp [pairSeed]⟩ = 0 ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a 2)) q
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ q) = -2*κ*Complex.normSq (q.a 2) := by
  refine ⟨by simp [normalizedPartner, doubleBoundary, Seed.Point.b],
    by simp [normalizedPartner, doubleBoundary, Seed.Point.b], ?_⟩
  exact simultaneous_local 0 0 hε hκ hδ q hq 2 (by simp)

/-- A nonzero selected coordinate, while another mutable coordinate is zero. -/
theorem selected_with_other_zero (z v : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    (hq : selectedBoundary z v ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary 0 v)) :
    selectedBoundary z v ∉ initialTorus pairSeed ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a 0)) (selectedBoundary z v)
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (selectedBoundary z v)) =
        -2*κ*Complex.normSq z ∧ Complex.normSq z ≠ 0 :=
  ⟨fun h => h 2 rfl, simultaneous_local 0 v hε hκ hδ _ hq 0 (by simp),
    (Complex.normSq_pos.mpr hz).ne'⟩

theorem continuous_selectedBoundary (v : ℂ) : Continuous (fun z => selectedBoundary z v) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    fin_cases j <;> fun_prop
  · exact continuous_const

theorem selected_neighborhood_nonvacuous (v : ℂ) {ε κ δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧
      selectedBoundary z v ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary 0 v) := by
  have hc : Tendsto (fun z => selectedBoundary z v) (𝓝 0) (𝓝 (doubleBoundary 0 v)) :=
    (continuous_selectedBoundary v).continuousAt
  have hm := hc.eventually ((LocalPrimitive.isOpen_neighborhood pairSeed ε κ δ _).mem_nhds
    (LocalPrimitive.mem_neighborhood pairSeed ε κ hδ _))
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
  exact ⟨hn,hz⟩

theorem variable_frozen_boundary (w z : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (variableFrozenBoundary w z hz).a 3 = z ∧
    (SmoothAtlas.presentation pairSeed pair_unimodular).manifold.scalarDerivative
      (fun r => Complex.normSq (r.a 0)) (variableFrozenBoundary w z hz)
      (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ (variableFrozenBoundary w z hz)) = 0 ∧
    GlobalLiouvilleField.L pairSeed pair_unimodular ε κ hδ (variableFrozenBoundary w z hz) 3 =
      Real.log ‖z‖ := by
  refine ⟨rfl, ?_, GlobalLiouvilleField.frozen_radial_equation _ _ hε hκ hδ _ _ (by simp [pairSeed])⟩
  have h := normSq_drift pairSeed pair_unimodular hε hκ hδ (variableFrozenBoundary w z hz) _
    (LocalPrimitive.mem_neighborhood _ ε κ hδ _) ⟨0, by simp [pairSeed]⟩
    (by simp [Seed.Point.mem_zeroSet, pairSeed, variableFrozenBoundary, Seed.Point.a])
  simpa [variableFrozenBoundary, Seed.Point.a] using h

/-- An empty mutable set is compatible with freely varying nonzero frozen data. -/
theorem empty_mutable_variable (t : ℝ) :
    (frozenPoint t).zeroSet = ∅ ∧ (frozenPoint t).a 0 = (Real.exp t : ℂ) := by
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact Finset.notMem_empty i (((frozenPoint t).mem_zeroSet i).mp hi).1
  · simp [frozenPoint]

theorem empty_mutable_curve {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {γ : ℝ → frozenSeed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts frozenSeed frozen_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z frozenSeed frozen_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    (γ s).zeroSet = (γ t).zeroSet ∧ (γ t).zeroSet = ∅ := by
  refine ⟨zeroSet_eq _ _ hε hκ hδ hγ hJ hs ht, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact Finset.notMem_empty i (((γ t).mem_zeroSet i).mp hi).1

theorem inhabited_dimension_zero (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty emptySeed.Point ∧ emptySeed.unitPoint.zeroSet = ∅ ∧
    GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ emptySeed.unitPoint = 0 := by
  refine ⟨⟨emptySeed.unitPoint⟩, ?_, ?_⟩
  · ext i; exact Fin.elim0 i
  · apply PiLp.ext
    intro i
    exact Fin.elim0 i


/-- Initial simultaneous zeros and arbitrary partners propagate along the actual curve. -/
theorem simultaneous_curve (u v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → pairSeed.Point} {J : Set ℝ}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) J)
    (hJ : IsPreconnected J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hstart : γ s = doubleBoundary u v) :
    (γ t).a 0 = 0 ∧ (γ t).a 2 = 0 ∧ (γ t).zeroSet = (doubleBoundary u v).zeroSet := by
  refine ⟨?_, ?_, ?_⟩
  · apply (coordinate_zero_iff _ _ hε hκ hδ hγ hJ hs ht 0).mp
    rw [hstart]; rfl
  · apply (coordinate_zero_iff _ _ hε hκ hδ hγ hJ hs ht 2).mp
    rw [hstart]; rfl
  · rw [zeroSet_eq _ _ hε hκ hδ hγ hJ ht hs, hstart]

/-- In dimension zero the actual field has a genuine constant integral curve on
all of real time, so restrictions to singletons are inhabited. -/
theorem dimension_zero_native_curve (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts emptySeed empty_unimodular
    IsMIntegralCurve (I := 𝓘(ℝ, Model 0)) (fun _ : ℝ => emptySeed.unitPoint)
      (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ) := by
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  intro t
  have hz := (inhabited_dimension_zero ε κ hδ).2.2
  rw [hz]
  convert (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model (2*0)))
    (x := t) emptySeed.unitPoint) using 1 <;> simp <;> rfl

end ZeroStratumInvarianceConsumer
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.BoundaryTangency.nodeProduct, `ClusterSkeleton.BoundaryTangency.drift,
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
    for name in #[
        `ClusterSkeleton.BoundaryTangency.boundaryPerturb,
        `ClusterSkeleton.BoundaryTangency.drift,
        `ClusterSkeleton.BoundaryTangency.nodeProduct,
        `ClusterSkeleton.DominanceCutoff.chi,
        `ClusterSkeleton.DominanceCutoff.dominance,
        `ClusterSkeleton.DominanceCutoff.localizationNeighborhood,
        `ClusterSkeleton.DominanceCutoff.logNorms,
        `ClusterSkeleton.DominanceCutoff.mutableNeighbors,
        `ClusterSkeleton.Examples.a2Matrix,
        `ClusterSkeleton.Examples.a2Seed,
        `ClusterSkeleton.GlobalLiouvilleField.A,
        `ClusterSkeleton.GlobalLiouvilleField.L,
        `ClusterSkeleton.GlobalLiouvilleField.Z,
        `ClusterSkeleton.GlobalLiouvilleField.logarithmicComponents,
        `ClusterSkeleton.GlobalLiouvilleField.nonzeroLocus,
        `ClusterSkeleton.GlobalPrimitive.alpha,
        `ClusterSkeleton.GlobalTwoForm.matrixForm,
        `ClusterSkeleton.IndependentNodeChart.flatten,
        `ClusterSkeleton.IndependentNodeChart.forward,
        `ClusterSkeleton.IndependentNodeChart.nodeTorus,
        `ClusterSkeleton.IndependentNodeChart.original,
        `ClusterSkeleton.IndependentNodeChart.outside,
        `ClusterSkeleton.IndependentNodeChart.parameters,
        `ClusterSkeleton.IndependentNodeChart.partner,
        `ClusterSkeleton.IndependentNodeChart.rawOriginal,
        `ClusterSkeleton.IndependentNodeChart.rawOutside,
        `ClusterSkeleton.IndependentNodeChart.rawParameters,
        `ClusterSkeleton.IndependentNodeChart.rawPartner,
        `ClusterSkeleton.IndependentNodeChart.recoveredOutside,
        `ClusterSkeleton.LaurentCoordinates.monomialMap,
        `ClusterSkeleton.LaurentCoordinates.nonzeroMonomialMap,
        `ClusterSkeleton.LocalFormGluing.LocallySmooth,
        `ClusterSkeleton.LocalFormGluing.glue,
        `ClusterSkeleton.LocalPrimitive.eta,
        `ClusterSkeleton.LocalPrimitive.neighborhood,
        `ClusterSkeleton.NativeNodePrimitive.block,
        `ClusterSkeleton.NativeNodePrimitive.lambda,
        `ClusterSkeleton.NativeNodePrimitive.locus,
        `ClusterSkeleton.NativeNodePrimitive.nodeDifferential,
        `ClusterSkeleton.NativeNodePrimitive.nodeMap,
        `ClusterSkeleton.NodeNondegeneracy.complementMatrix,
        `ClusterSkeleton.NodeNondegeneracy.rowProjection,
        `ClusterSkeleton.NodePrimitiveCancellation.A,
        `ClusterSkeleton.NodePrimitiveCancellation.L,
        `ClusterSkeleton.NodePrimitiveCancellation.S,
        `ClusterSkeleton.NodePrimitiveCancellation.T,
        `ClusterSkeleton.NodePrimitiveCancellation.dL,
        `ClusterSkeleton.NodePrimitiveCancellation.dtheta,
        `ClusterSkeleton.NodePrimitiveCancellation.du,
        `ClusterSkeleton.NodePrimitiveCancellation.lambda,
        `ClusterSkeleton.NodePrimitiveCancellation.oneForm,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.NodeTwoForm.complexForm,
        `ClusterSkeleton.NodeTwoForm.du,
        `ClusterSkeleton.NodeTwoForm.dv,
        `ClusterSkeleton.NodeTwoForm.dw,
        `ClusterSkeleton.NodeTwoForm.logParameter,
        `ClusterSkeleton.NodeTwoForm.matrixValue,
        `ClusterSkeleton.NodeTwoForm.originalLog,
        `ClusterSkeleton.NodeTwoForm.outsideLog,
        `ClusterSkeleton.NodeTwoForm.residualMatrix,
        `ClusterSkeleton.PrimitiveCutoffs.angularRadius,
        `ClusterSkeleton.PrimitiveCutoffs.angularWindow,
        `ClusterSkeleton.PrimitiveCutoffs.radial,
        `ClusterSkeleton.PrimitiveCutoffs.radialLength,
        `ClusterSkeleton.PrimitiveCutoffs.transitionPrimitive,
        `ClusterSkeleton.PrimitiveCutoffs.vartheta,
        `ClusterSkeleton.PrimitiveLocalization.affineCorrection,
        `ClusterSkeleton.PrimitiveLocalization.angle,
        `ClusterSkeleton.PrimitiveLocalization.correction,
        `ClusterSkeleton.PrimitiveLocalization.neighborhood,
        `ClusterSkeleton.PrimitiveLocalization.nodeLog,
        `ClusterSkeleton.PrimitiveLocalization.region,
        `ClusterSkeleton.PrimitiveLocalization.rowLog,
        `ClusterSkeleton.PrimitiveResidual.logRow,
        `ClusterSkeleton.PrimitiveResidual.residual,
        `ClusterSkeleton.PrimitiveResidual.tau,
        `ClusterSkeleton.RegularCorrection.regularForm,
        `ClusterSkeleton.RegularCorrection.regularH,
        `ClusterSkeleton.RegularCorrection.singularH,
        `ClusterSkeleton.RegularCorrection.surviving,
        `ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a,
        `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.Seed.Point.zeroSet,
        `ClusterSkeleton.Seed.Unimodular,
        `ClusterSkeleton.Seed.negativeMonomial,
        `ClusterSkeleton.Seed.positiveMonomial,
        `ClusterSkeleton.SmoothAtlas.chart,
        `ClusterSkeleton.SmoothAtlas.rawChart,
        `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue,
        `ClusterSkeleton.SplitIntegerRows.forwardMatrix,
        `ClusterSkeleton.SplitIntegerRows.inverseMatrix,
        `ClusterSkeleton.TorusCorrection.A,
        `ClusterSkeleton.TorusCorrection.H,
        `ClusterSkeleton.TorusCorrection.alpha,
        `ClusterSkeleton.TorusCorrection.angular,
        `ClusterSkeleton.TorusCorrection.localAngle,
        `ClusterSkeleton.TorusCorrection.rowLog,
        `ClusterSkeleton.TorusLiouvilleDynamics.Z,
        `ClusterSkeleton.TorusLiouvilleDynamics.amplitude,
        `ClusterSkeleton.TorusLiouvilleDynamics.angularTangent,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicComponents,
        `ClusterSkeleton.TorusLiouvilleDynamics.logarithmicHamiltonian,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialCorrection,
        `ClusterSkeleton.TorusLiouvilleDynamics.radialTangent,
        `ClusterSkeleton.TorusNondegeneracy.complexMatrix,
        `ClusterSkeleton.TorusPrimitive.alpha,
        `ClusterSkeleton.TorusPrimitive.angleCovector,
        `ClusterSkeleton.TorusPrimitive.beta,
        `ClusterSkeleton.TorusPrimitive.logarithmicPrimitive,
        `ClusterSkeleton.candidateChartLocus,
        `ClusterSkeleton.coordinateCap,
        `ClusterSkeleton.independentRowLaurentHomeomorph,
        `ClusterSkeleton.initialTorus,
        `ClusterSkeleton.nodeLogDomain,
        `ClusterSkeleton.nodeLogQuotient,
        `ClusterSkeleton.normalizedPartner,
        `FsFltz.CoordinateGeometry.complexStructure,
        `FsFltz.CoordinateGeometry.derivativeNormSq,
        `FsFltz.CoordinateGeometry.evaluation,
        `FsFltz.CoordinateGeometry.liouville,
        `FsFltz.CoordinateGeometry.omega,
        `FsFltz.CoordinateGeometry.primitive,
        `FsFltz.G,
        `FsFltz.Geometry.SmoothManifold.chartContraction,
        `FsFltz.Geometry.SmoothManifold.evalOne,
        `FsFltz.Geometry.SmoothManifold.evalTwo,
        `FsFltz.Geometry.SmoothManifold.liouvilleVector,
        `FsFltz.Geometry.cotangentAngleCovector,
        `FsFltz.Geometry.cotangentCircleCoordinate,
        `FsFltz.Geometry.cotangentCover,
        `FsFltz.Geometry.covectorForm,
        `FsFltz.Geometry.coverLambda0,
        `FsFltz.Geometry.coverLambdaCan,
        `FsFltz.Geometry.coverPlaneForm,
        `FsFltz.Geometry.differentialCovector,
        `FsFltz.Geometry.lambda0Form,
        `FsFltz.Geometry.lambdaCanForm,
        `FsFltz.Geometry.lgAngleCovector,
        `FsFltz.Geometry.lgCircleCoordinate,
        `FsFltz.Geometry.lgCover,
        `FsFltz.Geometry.phaseCovector,
        `FsFltz.Geometry.planeLambda,
        `FsFltz.Geometry.superpotentialPlaneForm,
        `FsFltz.W,
        `FsFltz.a,
        `FsFltz.angleCircleHomeomorph,
        `FsFltz.angleQuotient,
        `FsFltz.b0,
        `FsFltz.character,
        `FsFltz.complexCoordinateLinearMap,
        `FsFltz.complexStructureCoordinates,
        `FsFltz.coneTorus,
        `FsFltz.cotangentManifold,
        `FsFltz.dAbsWSq,
        `FsFltz.dAbsWSqLinearMap,
        `FsFltz.dPhi0,
        `FsFltz.dW,
        `FsFltz.dWLinearMap,
        `FsFltz.exponentLinearMap,
        `FsFltz.flowCore,
        `FsFltz.integralAngle,
        `FsFltz.lambda0Coordinates,
        `FsFltz.lambdaKCoordinates,
        `FsFltz.lgManifold,
        `FsFltz.liouvilleCoordinates,
        `FsFltz.monomial,
        `FsFltz.omega0Coordinates,
        `FsFltz.omegaKCoordinates,
        `FsFltz.pairing,
        `FsFltz.periodShift,
        `FsFltz.radialComplexCoordinates,
        `FsFltz.realSquaredNorm,
        `FsFltz.tangentComplexCoordinates,
        `ZeroStratumInvarianceConsumer.boundaryPoint,
        `ZeroStratumInvarianceConsumer.doubleBoundary,
        `ZeroStratumInvarianceConsumer.emptySeed,
        `ZeroStratumInvarianceConsumer.frozenPoint,
        `ZeroStratumInvarianceConsumer.frozenSeed,
        `ZeroStratumInvarianceConsumer.pairSeed,
        `ZeroStratumInvarianceConsumer.selectedBoundary,
        `ZeroStratumInvarianceConsumer.variableFrozenBoundary] do
      unless (← getEnv).contains name do
        throwError "Missing required imported or own-consumer definition {name}"
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize required equation for {name}"
  let env ← getEnv
  let mut report : Array String := #[]
  for mod in env.header.moduleNames do report := report.push s!"IMPORT {mod}"
  let required := #[`ClusterSkeleton.ZeroStratumInvariance, `ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "zero-stratum-consumer-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
