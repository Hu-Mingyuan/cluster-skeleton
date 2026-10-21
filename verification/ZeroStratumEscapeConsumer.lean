import ClusterSkeleton.ZeroStratumEscape
import ClusterSkeleton.Examples.A2
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry ZeroStratumEscape

namespace ZeroStratumEscapeConsumer

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

/-- Reversed A₂ has denominator -1, so its normalized partner is -w. -/
def reversedBoundary (w : ℂ) : Examples.a2Seed.Point :=
  ⟨(![-1,0], fun j => if (j : Fin 2) = 1 then w else -1), by
    constructor
    · intro j
      rcases j with ⟨j,hj⟩
      fin_cases j <;> norm_num [Seed.positiveMonomial, Seed.negativeMonomial,
        Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two]
    · intro j hj
      simp [Examples.a2Seed] at hj⟩

theorem reversed_coordinates (w : ℂ) :
    (reversedBoundary w).a 1 = 0 ∧
    (reversedBoundary w).b ⟨1, by simp [Examples.a2Seed]⟩ = w ∧
    Examples.a2Seed.negativeMonomial (reversedBoundary w).a 1 = -1 ∧
    normalizedPartner (reversedBoundary w) ⟨1, by simp [Examples.a2Seed]⟩ = -w := by
  simp [normalizedPartner, reversedBoundary, Seed.Point.a, Seed.Point.b,
    Seed.negativeMonomial, Examples.a2Seed, Examples.a2Matrix, Fin.prod_univ_two, div_neg]

theorem a2_nonzero_partner_escape (w : ℂ) (hw : w ≠ 0) {ε κ δ s : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → Examples.a2Seed.Point}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ici s))
    (hstart : γ s = boundaryPoint w) :
    (∀ K : Set Examples.a2Seed.Point, IsCompact K → ∃ T ≥ s, ∀ t ≥ T, γ t ∉ K) ∧
    ¬ IsCompact (closure (γ '' Ici s)) := by
  have ha : (γ s).a 0 = 0 := by rw [hstart]; rfl
  have hb : (γ s).b ⟨0, by simp [Examples.a2Seed]⟩ ≠ 0 := by
    simpa only [hstart, (boundary_coordinates w).2.2] using hw
  exact ⟨fun K hK => eventually_not_mem_compact _ _ hε hκ hδ hγ _ ha hb hK,
    not_isCompact_closure_forward_image _ _ hε hκ hδ hγ _ ha hb⟩

theorem a2_compact_closure_forces_zero (w : ℂ) {ε κ δ s : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → Examples.a2Seed.Point}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ici s))
    (hstart : γ s = boundaryPoint w) (hK : IsCompact (closure (γ '' Ici s))) : w = 0 := by
  have ha : (γ s).a 0 = 0 := by rw [hstart]; rfl
  simpa only [hstart, (boundary_coordinates w).2.2] using
    partner_eq_zero_of_isCompact_closure _ _ hε hκ hδ hγ hK
      ⟨0, by simp [Examples.a2Seed]⟩ ha

/-- The zero-partner case preserves the original partner; it asserts no escape. -/
theorem a2_zero_partner_persists {ε κ δ s t : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → Examples.a2Seed.Point}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ici s))
    (hstart : γ s = boundaryPoint 0) (ht : s ≤ t) :
    (γ t).a 0 = 0 ∧ (γ t).b ⟨0, by simp [Examples.a2Seed]⟩ = 0 := by
  have ha : (γ s).a 0 = 0 := by rw [hstart]; rfl
  have haz := (ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ
    hγ isPreconnected_Ici (show s ∈ Ici s by simp) ht 0).mp ha
  refine ⟨haz, (normalizedPartner_eq_zero_iff _ _ haz).mp ?_⟩
  apply (ZeroStratumPartnerDynamics.partner_zero_iff _ _ hε hκ hδ hγ isPreconnected_Ici
    (show s ∈ Ici s by simp) ht ⟨0, by simp [Examples.a2Seed]⟩ ha).mp
  simp only [hstart, a2_partner]

theorem reversed_a2_escape (w : ℂ) (hw : w ≠ 0) {ε κ δ s : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → Examples.a2Seed.Point}
    (hγ : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) γ
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ici s))
    (hstart : γ s = reversedBoundary w) :
    (∀ K : Set Examples.a2Seed.Point, IsCompact K → ∃ T ≥ s, ∀ t ≥ T, γ t ∉ K) ∧
    ¬ IsCompact (closure (γ '' Ici s)) := by
  have ha : (γ s).a 1 = 0 := by rw [hstart]; rfl
  have hb : (γ s).b ⟨1, by simp [Examples.a2Seed]⟩ ≠ 0 := by
    simpa only [hstart, (reversed_coordinates w).2.1] using hw
  exact ⟨fun K hK => eventually_not_mem_compact _ _ hε hκ hδ hγ _ ha hb hK,
    not_isCompact_closure_forward_image _ _ hε hκ hδ hγ _ ha hb⟩

/-- Two coordinates vanish, the first original partner stays zero, and the
second nonzero original partner forces escape from every compact set. -/
theorem simultaneous_zero_and_escape (v : ℂ) (hv : v ≠ 0) {ε κ δ s : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → pairSeed.Point}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ici s))
    (hstart : γ s = doubleBoundary 0 v) :
    (∀ t ≥ s, (γ t).a 0 = 0 ∧ (γ t).a 2 = 0 ∧
      (γ t).b ⟨0, by simp [pairSeed]⟩ = 0) ∧
    (∀ K : Set pairSeed.Point, IsCompact K → ∃ T ≥ s, ∀ t ≥ T, γ t ∉ K) ∧
    ¬ IsCompact (closure (γ '' Ici s)) := by
  have ha0 : (γ s).a 0 = 0 := by rw [hstart]; rfl
  have ha2 : (γ s).a 2 = 0 := by rw [hstart]; rfl
  have hb2 : (γ s).b ⟨2, by simp [pairSeed]⟩ ≠ 0 := by
    simpa [hstart, doubleBoundary, Seed.Point.b] using hv
  refine ⟨?_, fun K hK => eventually_not_mem_compact _ _ hε hκ hδ hγ _ ha2 hb2 hK,
    not_isCompact_closure_forward_image _ _ hε hκ hδ hγ _ ha2 hb2⟩
  intro t ht
  have h0 := (ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ
    hγ isPreconnected_Ici (show s ∈ Ici s by simp) ht 0).mp ha0
  have h2 := (ZeroStratumInvariance.coordinate_zero_iff _ _ hε hκ hδ
    hγ isPreconnected_Ici (show s ∈ Ici s by simp) ht 2).mp ha2
  refine ⟨h0, h2, (normalizedPartner_eq_zero_iff _ _ h0).mp ?_⟩
  apply (ZeroStratumPartnerDynamics.partner_zero_iff _ _ hε hκ hδ hγ isPreconnected_Ici
    (show s ∈ Ici s by simp) ht ⟨0, by simp [pairSeed]⟩ ha0).mp
  simp only [hstart, (double_partners 0 v).1]

/-- The frozen value z is independently arbitrary and remains nonzero. -/
theorem variable_frozen_escape (w z : ℂ) (hw : w ≠ 0) (hz : z ≠ 0) {ε κ δ s : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
    {γ : ℝ → pairSeed.Point}
    (hγ : letI := SmoothAtlas.charts pairSeed pair_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 8)) γ
        (GlobalLiouvilleField.Z pairSeed pair_unimodular ε κ hδ) (Ici s))
    (hstart : γ s = variableFrozenBoundary w z hz) :
    (γ s).a 3 = z ∧ (∀ t : ℝ, (γ t).a 3 ≠ 0) ∧
    (∀ K : Set pairSeed.Point, IsCompact K → ∃ T ≥ s, ∀ t ≥ T, γ t ∉ K) ∧
    ¬ IsCompact (closure (γ '' Ici s)) := by
  have ha : (γ s).a 0 = 0 := by rw [hstart]; rfl
  have hb : (γ s).b ⟨0, by simp [pairSeed]⟩ ≠ 0 := by
    simpa [hstart, variableFrozenBoundary, Seed.Point.b] using hw
  exact ⟨by rw [hstart]; rfl, fun t => (γ t).frozen_ne_zero 3 (by simp [pairSeed]),
    fun K hK => eventually_not_mem_compact _ _ hε hκ hδ hγ _ ha hb hK,
    not_isCompact_closure_forward_image _ _ hε hκ hδ hγ _ ha hb⟩

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Native within-derivative at an arbitrary shifted closed endpoint, exact
growth and compact escape, including the manuscript range 0 < δ < π. -/
theorem shifted_halfline_endpoint {ε κ δ s τ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (_hδπ : δ < Real.pi)
    {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici (s+τ)))
    (i : S.Mutable) (ha : (γ (s+τ)).a i = 0) (hb : (γ (s+τ)).b i ≠ 0) :
    HasDerivWithinAt (fun t => Complex.normSq (normalizedPartner (γ t) i))
      (2*(1+κ)*Complex.normSq (normalizedPartner (γ (s+τ)) i)) (Ici (s+τ)) (s+τ) ∧
    (∀ t ≥ s+τ, (γ t).a i = 0 ∧
      Complex.normSq (normalizedPartner (γ t) i) =
        Real.exp (2*(1+κ)*(t-(s+τ))) * Complex.normSq (normalizedPartner (γ (s+τ)) i)) ∧
    (∀ K : Set S.Point, IsCompact K → ∃ T ≥ s+τ, ∀ t ≥ T, γ t ∉ K) := by
  refine ⟨ZeroStratumPartnerDynamics.normSq_hasDerivWithinAt S hdet hε hκ hδ hγ
    isPreconnected_Ici (show s+τ ∈ Ici (s+τ) by simp) (show s+τ ∈ Ici (s+τ) by simp) i ha,
    ?_, fun K hK => eventually_not_mem_compact S hdet hε hκ hδ hγ i ha hb hK⟩
  intro t ht
  exact ⟨(ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ
    isPreconnected_Ici (show s+τ ∈ Ici (s+τ) by simp) ht i).mp ha,
    ZeroStratumPartnerDynamics.normSq_eq_exp_mul S hdet hε hκ hδ hγ
      isPreconnected_Ici (show s+τ ∈ Ici (s+τ) by simp) ht i ha⟩

/-- Translate a supplied native half-line curve to start at time zero. -/
theorem time_translation_escape {ε κ δ s : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici s))
    (i : S.Mutable) (ha : (γ s).a i = 0) (hb : (γ s).b i ≠ 0) :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => γ (t+s))
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici 0) ∧
    (∀ K : Set S.Point, IsCompact K → ∃ T ≥ 0, ∀ t ≥ T, γ (t+s) ∉ K) ∧
    ¬ IsCompact (closure ((fun t => γ (t+s)) '' Ici 0)) := by
  letI := SmoothAtlas.charts S hdet
  have hdomain : {t : ℝ | t+s ∈ Ici s} = Ici 0 := by
    ext t
    simp only [mem_ofPred_eq, mem_Ici]
    constructor <;> intro h <;> linarith
  have hshift : IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => γ (t+s))
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici 0) := by
    simpa only [Function.comp_def, hdomain] using hγ.comp_add s
  have ha' : (γ (0+s)).a i = 0 := by simpa only [zero_add] using ha
  have hb' : (γ (0+s)).b i ≠ 0 := by simpa only [zero_add] using hb
  exact ⟨hshift, fun K hK => eventually_not_mem_compact S hdet hε hκ hδ hshift i ha' hb' hK,
    not_isCompact_closure_forward_image S hdet hε hκ hδ hshift i ha' hb'⟩

/-- Uses the existing independently defined trappedSet of the supplied flow. -/
theorem supplied_flow_necessary_and_excluded {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ S.Point) (p : S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ici 0))
    (i : S.Mutable) (ha : p.a i = 0) :
    (p ∈ trappedSet flow → p.b i = 0) ∧ (p.b i ≠ 0 → p ∉ trappedSet flow) :=
  ⟨fun hp => partner_eq_zero_of_mem_trappedSet S hdet hε hκ hδ flow p hflow hp i ha,
    fun hb => not_mem_trappedSet S hdet hε hκ hδ flow p hflow i ha hb⟩

theorem a2_supplied_flow (w : ℂ) {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (flow : Flow ℝ Examples.a2Seed.Point)
    (hflow : letI := SmoothAtlas.charts Examples.a2Seed Examples.a2Seed_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 4)) (fun t => flow t (boundaryPoint w))
        (GlobalLiouvilleField.Z Examples.a2Seed Examples.a2Seed_unimodular ε κ hδ) (Ici 0)) :
    (boundaryPoint w ∈ trappedSet flow → w = 0) ∧
    (w ≠ 0 → boundaryPoint w ∉ trappedSet flow) := by
  simpa only [(boundary_coordinates w).2.2] using
    supplied_flow_necessary_and_excluded _ _ hε hκ hδ flow (boundaryPoint w) hflow
      ⟨0, by simp [Examples.a2Seed]⟩ (boundary_coordinates w).1


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


/-- In dimension zero an actual native curve has compact forward closure;
there is no mutable index to which the escape hypothesis could apply. -/
theorem dimension_zero_compact_forward (ε κ s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts emptySeed empty_unimodular
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model 0)) (fun _ : ℝ => emptySeed.unitPoint)
      (GlobalLiouvilleField.Z emptySeed empty_unimodular ε κ hδ) (Ici s) ∧
    IsCompact (closure ((fun _ : ℝ => emptySeed.unitPoint) '' Ici s)) ∧
    IsEmpty emptySeed.Mutable := by
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  have h := dimension_zero_native_curve ε κ hδ
  refine ⟨h.1.isMIntegralCurveOn _, ?_, h.2⟩
  have himage : (fun _ : ℝ => emptySeed.unitPoint) '' Ici s = {emptySeed.unitPoint} := by
    ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      rfl
    · intro hp
      exact ⟨s, by simp, (Set.mem_singleton_iff.mp hp).symm⟩
  rw [himage, closure_singleton]
  exact isCompact_singleton

end ZeroStratumEscapeConsumer

-- Native audit using unchanged Lean.collectAxioms and accepted complete selector.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ZeroStratumEscapeConsumer.boundaryPoint,
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
  for mod in env.header.moduleNames do report := report.push s!"IMPORT {mod}"
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
  let path := System.FilePath.mk (dir.getD "/tmp") / "zero-stratum-escape-native-audit.txt"
  IO.FS.writeFile path (String.intercalate "\n" report.toList ++ "\n")
  logInfo m!"AUDITED native combined/imported/local/supplement roots: {count}"
  logInfo m!"Complete native audit written to {path}"
