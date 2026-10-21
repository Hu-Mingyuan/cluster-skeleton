import ClusterSkeleton.LocalAngularDynamics
import ClusterSkeleton.Examples.A2
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry LocalAngularDynamics

namespace LocalAngularDynamicsConsumer
variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- All finite indices, including frozen ones, have native smooth coefficients. -/
theorem generic_smooth (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) (j : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun q => nu S ε κ δ p q j) (LocalPrimitive.neighborhood S ε κ δ p) :=
  nu_smooth S hdet ε κ hδ p j

/-- The literal native complex differential in the manuscript parameter range. -/
theorem generic_native {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) (fun r => normalizedPartner r i) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
      (q.a i * normalizedPartner q i - 1) * nodeLogQuotient (q.a i, normalizedPartner q i) -
        normalizedPartner q i * (-(κ : ℂ) + Complex.I * (nu S ε κ δ p q i : ℂ)) :=
  partner_drift S hdet hε hκ hδ p q hq i hi

/-- The native derivative of nu exists because U is open and the construction is smooth. -/
theorem coefficient_native_differentiable (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (j : Fin d) :
    letI := SmoothAtlas.charts S hdet
    HasMFDerivAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) (fun r => nu S ε κ δ p r j) q
      (mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) (fun r => nu S ε κ δ p r j) q) := by
  letI := SmoothAtlas.charts S hdet
  exact (((nu_smooth S hdet ε κ hδ p j) q hq).contMDiffAt
    ((LocalPrimitive.isOpen_neighborhood S ε κ δ p).mem_nhds hq)).mdifferentiableAt
      (by simp) |>.hasMFDerivAt

theorem genuine_curve_local {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p →
    HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
      (((γ t).a i * normalizedPartner (γ t) i - 1) *
        nodeLogQuotient ((γ t).a i, normalizedPartner (γ t) i) -
        normalizedPartner (γ t) i * (-(κ : ℂ) + Complex.I * (nu S ε κ δ p (γ t) i : ℂ))) s t :=
  partner_hasDerivWithinAt S hdet hε hκ hδ p i hi

theorem genuine_curve_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p → (γ t).a i = 0 →
    HasDerivWithinAt (fun u => normalizedPartner (γ u) i)
      ((1 + (κ : ℂ) - Complex.I * (nu S ε κ δ p (γ t) i : ℂ)) * normalizedPartner (γ t) i) s t :=
  partner_hasDerivWithinAt_zero S hdet hε hκ hδ p i hi

/-- A useful specialization at the actual center; the normalized partner may vanish. -/
theorem center_partner {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (q : S.Point) (i : S.Mutable) (ha : q.a i = 0) :
    BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) q =
      (1 + (κ : ℂ) - Complex.I * (nu S ε κ δ q q i : ℂ)) * normalizedPartner q i :=
  partner_drift_zero S hdet hε hκ hδ q q (LocalPrimitive.mem_neighborhood S ε κ hδ q)
    i ((q.mem_zeroSet i).mpr ⟨i.property, ha⟩) ha

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
Its partner is one, so the density consumer does not reduce to a zero partner. -/
theorem mixed_complex_family (v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      mixedPoint t v ∈ LocalPrimitive.neighborhood pairSeed ε κ δ (doubleBoundary 1 v) ∧
      (mixedPoint t v).a 0 ≠ 0 ∧ (mixedPoint t v).a 2 = 0 ∧
      normalizedPartner (mixedPoint t v) ⟨0, by simp [pairSeed]⟩ = 1 ∧
      BoundaryTangency.drift pairSeed pair_unimodular ε κ hδ
        (fun r => normalizedPartner r ⟨0, by simp [pairSeed]⟩) (mixedPoint t v) =
        ((mixedPoint t v).a 0 - 1) * nodeLogQuotient ((mixedPoint t v).a 0, 1) -
          (-(κ : ℂ) + Complex.I * (nu pairSeed ε κ δ (doubleBoundary 1 v) (mixedPoint t v) 0 : ℂ)) := by
  have hc : Tendsto (fun t => mixedPoint t v) (𝓝 0) (𝓝 (doubleBoundary 1 v)) := by
    simpa only [ContinuousAt, mixed_zero] using (continuous_mixedPoint v).continuousAt (x := 0)
  have hm := hc.eventually ((LocalPrimitive.isOpen_neighborhood pairSeed ε κ δ
    (doubleBoundary 1 v)).mem_nhds (LocalPrimitive.mem_neighborhood pairSeed ε κ hδ _))
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
  obtain ⟨ha, hz, hb⟩ := mixed_coordinates t v hn
  refine ⟨ht, ha, hz, hb, ?_⟩
  simpa only [hb, mul_one, one_mul] using
    partner_drift pairSeed pair_unimodular hε hκ hδ (doubleBoundary 1 v) (mixedPoint t v) ht
      ⟨0, by simp [pairSeed]⟩ (by simp [Seed.Point.mem_zeroSet, pairSeed, doubleBoundary, Seed.Point.a])

theorem a2_arbitrary_partner (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    BoundaryTangency.drift Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ
      (fun r => normalizedPartner r ⟨0, by simp [Examples.a2Seed]⟩) (boundaryPoint w) =
      (1 + (κ : ℂ) - Complex.I *
        (nu Examples.a2Seed ε κ δ (boundaryPoint w) (boundaryPoint w) 0 : ℂ)) * w := by
  simpa only [a2_partner] using center_partner Examples.a2Seed Examples.a2Seed_unimodular
    hε hκ hδ (boundaryPoint w) ⟨0, by simp [Examples.a2Seed]⟩ rfl

theorem a2_zero_partner {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    BoundaryTangency.drift Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ
      (fun r => normalizedPartner r ⟨0, by simp [Examples.a2Seed]⟩) (boundaryPoint 0) = 0 := by
  simpa only [mul_zero] using a2_arbitrary_partner 0 hε hκ hδ

theorem simultaneous_zero_complex (u v : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    BoundaryTangency.drift pairSeed pair_unimodular ε κ hδ
      (fun r => normalizedPartner r ⟨0, by simp [pairSeed]⟩) (doubleBoundary u v) =
        (1 + (κ : ℂ) - Complex.I *
          (nu pairSeed ε κ δ (doubleBoundary u v) (doubleBoundary u v) 0 : ℂ)) * u ∧
    BoundaryTangency.drift pairSeed pair_unimodular ε κ hδ
      (fun r => normalizedPartner r ⟨2, by simp [pairSeed]⟩) (doubleBoundary u v) =
        (1 + (κ : ℂ) - Complex.I *
          (nu pairSeed ε κ δ (doubleBoundary u v) (doubleBoundary u v) 2 : ℂ)) * v := by
  constructor
  · simpa only [(double_partners u v).1] using center_partner pairSeed pair_unimodular
      hε hκ hδ (doubleBoundary u v) ⟨0, by simp [pairSeed]⟩ rfl
  · simpa only [(double_partners u v).2] using center_partner pairSeed pair_unimodular
      hε hκ hδ (doubleBoundary u v) ⟨2, by simp [pairSeed]⟩ rfl

theorem variable_frozen_complex (w z : ℂ) (hz : z ≠ 0) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    (variableFrozenBoundary w z hz).a 3 = z ∧
    BoundaryTangency.drift pairSeed pair_unimodular ε κ hδ
      (fun r => normalizedPartner r ⟨0, by simp [pairSeed]⟩) (variableFrozenBoundary w z hz) =
        (1 + (κ : ℂ) - Complex.I *
          (nu pairSeed ε κ δ (variableFrozenBoundary w z hz) (variableFrozenBoundary w z hz) 0 : ℂ)) * w := by
  refine ⟨rfl, ?_⟩
  have hb : normalizedPartner (variableFrozenBoundary w z hz) ⟨0, by simp [pairSeed]⟩ = w := by
    simp [normalizedPartner, variableFrozenBoundary, Seed.Point.a, Seed.Point.b,
      Seed.negativeMonomial, pairSeed, Fin.prod_univ_succ]
  simpa only [hb] using center_partner pairSeed pair_unimodular hε hκ hδ
    (variableFrozenBoundary w z hz) ⟨0, by simp [pairSeed]⟩ rfl

/-- Frozen-only spaces still have all angular coefficients; the formula is zero. -/
theorem empty_mutable_nu (hM : S.mutable = ∅) (ε κ δ : ℝ) (p q : S.Point) :
    nu S ε κ δ p q = 0 := by
  haveI : IsEmpty S.Mutable := ⟨fun i => by simpa [hM] using i.property⟩
  funext j
  simp [nu, angularRhs, Matrix.mulVec, dotProduct]

theorem frozen_only_family (t : ℝ) (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts frozenSeed frozen_unimodular
    (frozenPoint t).a 0 = (Real.exp t : ℂ) ∧
    nu frozenSeed ε κ δ (frozenPoint t) (frozenPoint t) = 0 ∧
    ContMDiffOn 𝓘(ℝ, Model (2*2)) 𝓘(ℝ, ℝ) ∞
      (fun q => nu frozenSeed ε κ δ (frozenPoint t) q 0)
      (LocalPrimitive.neighborhood frozenSeed ε κ δ (frozenPoint t)) := by
  letI := SmoothAtlas.charts frozenSeed frozen_unimodular
  refine ⟨?_, empty_mutable_nu frozenSeed rfl ε κ δ _ _, nu_smooth frozenSeed frozen_unimodular ε κ hδ _ 0⟩
  simp [frozenPoint, pointOfCoordinateTorus, torusCoordinates, Seed.Point.a]

/-- The actual dimension-zero space is inhabited, and native complex differentiation works. -/
theorem dimension_zero (c : ℂ) (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    let q := pointOfCoordinateTorus emptySeed (fun j => Fin.elim0 j)
    nu emptySeed ε κ δ q q = 0 ∧
    BoundaryTangency.drift emptySeed empty_unimodular ε κ hδ (fun _ => c) q = 0 := by
  let q := pointOfCoordinateTorus emptySeed (fun j => Fin.elim0 j)
  refine ⟨empty_mutable_nu emptySeed rfl ε κ δ q q, ?_⟩
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  change mfderiv 𝓘(ℝ, Model (2*0)) 𝓘(ℝ, ℂ) (fun _ : emptySeed.Point => c) q _ = 0
  rw [mfderiv_const]
  rfl

def a4Matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,1,0,0; -1,0,1,0; 0,-1,0,1; 0,0,-1,0]

def a4Seed : Seed 4 where
  B := a4Matrix
  mutable := Finset.univ
  skew := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [a4Matrix]
  acyclic := by
    apply (measure (fun i : {i : Fin 4 // i ∈ (Finset.univ : Finset (Fin 4))} => i.1.val)).wf.mono
    intro i j hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    change i.val < j.val
    fin_cases i <;> fin_cases j <;> norm_num [a4Matrix] at hij
    all_goals norm_num

theorem a4_unimodular : a4Seed.Unimodular := by
  norm_num [Seed.Unimodular, a4Seed, a4Matrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]

def a4Boundary (w : ℂ) (x t : ℝ) : a4Seed.Point :=
  ⟨(![0, -1, (Real.exp x : ℂ), Complex.exp ((t : ℂ) * Complex.I)],
    fun j => ![w, -(Real.exp x : ℂ),
      (Complex.exp ((t : ℂ) * Complex.I) - 1) / (Real.exp x : ℂ),
      (1 + (Real.exp x : ℂ)) / Complex.exp ((t : ℂ) * Complex.I)] (j : Fin 4)), by
    constructor
    · intro j
      rcases j with ⟨j, hj⟩
      have hr : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero x
      fin_cases j <;> simp [Seed.positiveMonomial, Seed.negativeMonomial,
        a4Seed, a4Matrix, Fin.prod_univ_succ] <;>
        field_simp [hr, Complex.exp_ne_zero] <;> ring
    · intro j hj
      simp [a4Seed] at hj⟩

def a4v0 : a4Seed.Mutable := ⟨0, by simp [a4Seed]⟩
def a4v2 : a4Seed.Mutable := ⟨2, by simp [a4Seed]⟩
def a4v3 : a4Seed.Mutable := ⟨3, by simp [a4Seed]⟩

theorem a4_zeroSet (w : ℂ) (x t : ℝ) : (a4Boundary w x t).zeroSet = {0} := by
  have hr : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero x
  ext i
  fin_cases i <;> simp [Seed.Point.mem_zeroSet, a4Boundary, Seed.Point.a,
    a4Seed, Complex.exp_ne_zero]

theorem a4_partner (w : ℂ) (x t : ℝ) : normalizedPartner (a4Boundary w x t) a4v0 = w := by
  simp [normalizedPartner, a4Boundary, a4v0, Seed.Point.a, Seed.Point.b,
    Seed.negativeMonomial, a4Seed, a4Matrix, Fin.prod_univ_succ]

theorem a4_surviving : RegularCorrection.surviving a4Seed {0} = {a4v2, a4v3} := by
  ext j
  obtain ⟨j, hj⟩ := j
  fin_cases j <;> simp [RegularCorrection.surviving, a4Seed, a4Matrix, a4v2, a4v3]

theorem a4_logs (w : ℂ) (x t : ℝ) :
    DominanceCutoff.logNorms a4Seed (a4Boundary w x t) = ![0,0,x,0] := by
  funext i
  fin_cases i <;> simp [DominanceCutoff.logNorms, a4Boundary, Seed.Point.a,
    Real.log_exp, Complex.norm_exp]

theorem a4_character (w : ℂ) (x t : ℝ) :
    -exchangeCharacter (a4Boundary w x t) 2 = Complex.exp ((t : ℂ) * Complex.I) := by
  norm_num [exchangeCharacter, a4Boundary, Seed.Point.a, Seed.positiveMonomial,
    Seed.negativeMonomial, a4Seed, a4Matrix, Fin.prod_univ_succ]
  rw [div_neg, div_one, neg_neg]

theorem a4_dominance (w : ℂ) (t : ℝ) :
    DominanceCutoff.dominance a4Seed 1 2 (DominanceCutoff.logNorms a4Seed (a4Boundary w (-5) t)) = 1 := by
  apply DominanceCutoff.dominance_eq_one_of a4Seed (by norm_num) 2 _
  intro j hj
  rw [a4_logs]
  fin_cases j <;> norm_num [DominanceCutoff.mem_mutableNeighbors, a4Seed, a4Matrix] at *

theorem a4_correction_nonzero (w : ℂ) :
    PrimitiveLocalization.correction 1 3 (Real.pi/2) a4v2 (a4Boundary w (-5) (Real.pi/8)) =
      -2 * (Real.pi/8) := by
  have hr : PrimitiveCutoffs.radial 1 3 (-5) = -2 := by
    convert PrimitiveCutoffs.radial_tail (ε := 1) (κ := 3) (A := -5) (by norm_num)
      (by norm_num [PrimitiveCutoffs.radialLength]) using 1 <;> norm_num
  have hv : PrimitiveCutoffs.vartheta (Real.pi/2) (Real.pi/8) = Real.pi/8 := by
    apply PrimitiveCutoffs.vartheta_eq_self (by positivity)
    norm_num [PrimitiveCutoffs.angularRadius, abs_of_pos Real.pi_pos, abs_div, div_div]
  have ht : toIocMod Real.two_pi_pos (-Real.pi) (Real.pi/8) = Real.pi/8 := by
    apply (toIocMod_eq_self Real.two_pi_pos).mpr
    constructor <;> linarith [Real.pi_pos]
  have ha : PrimitiveLocalization.angle (a4Boundary w (-5) (Real.pi/8)) 2 = Real.pi/8 := by
    unfold PrimitiveLocalization.angle
    rw [a4_character, Complex.log_im, Complex.arg_exp]
    simpa using ht
  have hrow : PrimitiveLocalization.rowLog (a4Boundary w (-5) (Real.pi/8)) 2 = 0 := by
    unfold PrimitiveLocalization.rowLog
    rw [a4_logs]
    norm_num [a4Seed, a4Matrix, Fin.sum_univ_succ]
  unfold PrimitiveLocalization.correction
  rw [show (a4v2 : Fin 4) = 2 from rfl, a4_dominance, a4_logs, hrow, ha]
  norm_num [hr, hv, PrimitiveCutoffs.rho_eq_one (x := 0) (by norm_num)]

/-- Concrete nonzero surviving correction at an actual center of the actual neighborhood. -/
theorem a4_nonvacuous (w : ℂ) :
    let p := a4Boundary w (-5) (Real.pi/8)
    p.zeroSet = {0} ∧ a4v2 ∈ RegularCorrection.surviving a4Seed p.zeroSet ∧
    p ∈ LocalPrimitive.neighborhood a4Seed 1 3 (Real.pi/2) p ∧
    PrimitiveLocalization.correction 1 3 (Real.pi/2) a4v2 p ≠ 0 := by
  refine ⟨a4_zeroSet w _ _, ?_, LocalPrimitive.mem_neighborhood a4Seed 1 3 (by positivity) _, ?_⟩
  · rw [a4_zeroSet, a4_surviving]
    exact Finset.mem_insert_self _ _
  · rw [a4_correction_nonzero]
    exact mul_ne_zero (by norm_num) (by positivity)

/-- Full complex dynamics and native angular smoothness at that nontrivial configuration. -/
theorem a4_complex_consumer (w : ℂ) :
    let p := a4Boundary w (-5) (Real.pi/8)
    letI := SmoothAtlas.charts a4Seed a4_unimodular
    ContMDiffOn 𝓘(ℝ, Model (2*4)) 𝓘(ℝ, ℝ) ∞
      (fun q => nu a4Seed 1 3 (Real.pi/2) p q 0)
      (LocalPrimitive.neighborhood a4Seed 1 3 (Real.pi/2) p) ∧
    mfderiv 𝓘(ℝ, Model (2*4)) 𝓘(ℝ, ℂ) (fun r => normalizedPartner r a4v0) p
      (GlobalLiouvilleField.Z a4Seed a4_unimodular 1 3 (by positivity : 0 < Real.pi/2) p) =
      (1 + (3 : ℂ) - Complex.I * (nu a4Seed 1 3 (Real.pi/2) p p 0 : ℂ)) * w := by
  let p := a4Boundary w (-5) (Real.pi/8)
  letI := SmoothAtlas.charts a4Seed a4_unimodular
  refine ⟨nu_smooth a4Seed a4_unimodular 1 3 (by positivity) p 0, ?_⟩
  change BoundaryTangency.drift a4Seed a4_unimodular 1 3 (by positivity : 0 < Real.pi/2)
    (fun r => normalizedPartner r a4v0) p = _
  simpa only [p, a4_partner, Complex.ofReal_ofNat, show (a4v0 : Fin 4) = 0 from rfl] using
    center_partner a4Seed a4_unimodular (by norm_num : (0:ℝ)<1)
    (by norm_num : (2:ℝ)*1+1≤3) (by positivity : 0 < Real.pi/2) p a4v0 rfl

end LocalAngularDynamicsConsumer

-- Native transitive audit; unmodified Lean.collectAxioms and accepted root selector.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`LocalAngularDynamicsConsumer.boundaryPoint,
        `LocalAngularDynamicsConsumer.pairSeed,
        `LocalAngularDynamicsConsumer.frozenSeed,
        `LocalAngularDynamicsConsumer.frozenPoint,
        `LocalAngularDynamicsConsumer.emptySeed,
        `LocalAngularDynamicsConsumer.doubleBoundary,
        `LocalAngularDynamicsConsumer.variableFrozenBoundary,
        `LocalAngularDynamicsConsumer.mixedPoint,
        `LocalAngularDynamicsConsumer.a4Matrix,
        `LocalAngularDynamicsConsumer.a4Seed,
        `LocalAngularDynamicsConsumer.a4Boundary,
        `LocalAngularDynamicsConsumer.a4v0,
        `LocalAngularDynamicsConsumer.a4v2,
        `LocalAngularDynamicsConsumer.a4v3,
        `ClusterSkeleton.LocalAngularDynamics.maskedLogs,
        `ClusterSkeleton.LocalAngularDynamics.angularRhs,
        `ClusterSkeleton.LocalAngularDynamics.nu,
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
  let required := #[`ClusterSkeleton.LocalAngularDynamics, `ClusterSkeleton.NormalizedPartnerNormDrift, `ClusterSkeleton.BoundaryTangency, `ClusterSkeleton.GlobalLiouvilleField,
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "local-angular-dynamics-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
