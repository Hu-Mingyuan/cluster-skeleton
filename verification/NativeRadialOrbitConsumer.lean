import ClusterSkeleton.NativeRadialOrbit
import ClusterSkeleton.Examples.A2

/-! Native radial consumers on the literal exchange carrier. Additional inherited
consumer contexts are assembled byte for byte by the private verification fixture. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter ClusterSkeleton FsFltz.Geometry
open ClusterSkeleton.NativeRadialOrbit ClusterSkeleton.GlobalLiouvilleField

namespace NativeRadialOrbitConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The closed cutoff boundary, even away from the initial torus. -/
theorem cutoff_boundary {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) (ha : A S p j = -2*ε) :
    L S hdet ε κ hδ p j = -2*ε ∧ c S hdet ε κ hδ p j = 0 := by
  have hL := L_eq_A_of_ge_cutoff S hdet hε hκ hδ p j hj (by rw [ha])
  exact ⟨hL.trans ha, by simp [c, hL]⟩

/-- The equation at an honestly interior shifted initial time, without a caller's scalar ODE. -/
theorem shifted_time_seven {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) {γ : ℝ → S.Point}
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ (Z S hdet ε κ hδ) (Ioi (7-2)))
    (j : Fin d) (hj : (γ 7).a j ≠ 0) :
    ScalarOrbitDynamics.RadialEquation ε κ (fun t => A S (γ (7+t)) j)
      (fun t => c S hdet ε κ hδ (γ (7+t)) j) ∧
    HasDerivAt (fun t => A S (γ (7+t)) j) (L S hdet ε κ hδ (γ 7) j) 0 ∧
    (∀ t ≥ 0, (γ (7+t)).a j ≠ 0) := by
  refine ⟨radialEquation S hdet hε hκ hδ (by norm_num : (0 : ℝ) < 2) hγ j hj, ?_, ?_⟩
  · simpa only [add_zero] using shifted_hasDerivAt_A S hdet hε hκ hδ
      (by norm_num : (0 : ℝ) < 2) hγ j hj (le_refl (0 : ℝ))
  · intro t ht
    exact coordinate_ne_zero S hdet hε hκ hδ (by norm_num : (0 : ℝ) < 2)
      hγ j hj (by linarith)

/-- Literal supplied-flow application with the original independently defined trapped set. -/
theorem supplied_flow_trapped {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (_hδπ : δ < Real.pi) (flow : Flow ℝ S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (Z S hdet ε κ hδ) univ) {p : S.Point} (hp : p ∈ trappedSet flow) :
    (∀ j : Fin d, ‖p.a j‖ ≤ 1) ∧ (∀ f : Fin d, f ∉ S.mutable → ‖p.a f‖ = 1) :=
  trapped_radial_restrictions S hdet hε hκ hδ flow hflow hp

/-- Empty mutable scope retains the full native frozen restriction. -/
theorem empty_mutable_trapped {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (hM : S.mutable = ∅) (flow : Flow ℝ S.Point)
    (hflow : letI := SmoothAtlas.charts S hdet
      ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) (fun t => flow t p)
        (Z S hdet ε κ hδ) univ) {p : S.Point} (hp : p ∈ trappedSet flow) :
    ∀ j : Fin d, ‖p.a j‖ = 1 := by
  intro j
  exact frozen_norm_eq_one_of_mem_trappedSet S hdet hε hκ hδ flow hflow hp j (by simp [hM])

/-- Three skew blocks, with only the first vertex of each block mutable. -/
def tripleSeed : Seed 6 where
  B := !![0,1,0,0,0,0; -1,0,0,0,0,0; 0,0,0,1,0,0;
    0,0,-1,0,0,0; 0,0,0,0,0,1; 0,0,0,0,-1,0]
  mutable := {0,2,4}
  skew := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  acyclic := by
    refine ⟨fun i => Acc.intro i fun j h => ?_⟩
    have hi := i.property
    have hj := j.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
      simp [hi, hj] at h

theorem triple_unimodular : tripleSeed.Unimodular := by
  norm_num [Seed.Unimodular, tripleSeed, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]

/-- Actual exchange points. The mutable partners at the two zero coordinates remain free. -/
def triplePoint (x : ℝ) (u v : ℂ) : tripleSeed.Point :=
  ⟨(![(Real.exp x : ℂ), -1, 0, -1, 0, -1],
    fun j => if (j : Fin 6) = 0 then 0 else if (j : Fin 6) = 2 then u else v), by
    constructor
    · intro j
      have hj := j.property
      simp only [tripleSeed, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj | hj <;>
        simp [hj, Seed.positiveMonomial, Seed.negativeMonomial, tripleSeed,
          Fin.prod_univ_succ]
    · intro j hj
      fin_cases j <;> simp_all [tripleSeed]⟩

theorem triple_coordinates (x : ℝ) (u v : ℂ) :
    (triplePoint x u v).a 0 = (Real.exp x : ℂ) ∧
    (triplePoint x u v).a 2 = 0 ∧ (triplePoint x u v).a 4 = 0 ∧
    (triplePoint x u v).b ⟨0, by simp [tripleSeed]⟩ = 0 ∧
    (triplePoint x u v).b ⟨2, by simp [tripleSeed]⟩ = u ∧
    (triplePoint x u v).b ⟨4, by simp [tripleSeed]⟩ = v := by
  simp [triplePoint, Seed.Point.a, Seed.Point.b]

theorem triple_selected_nonzero (x : ℝ) (u v : ℂ) : (triplePoint x u v).a 0 ≠ 0 := by
  change (Real.exp x : ℂ) ≠ 0
  exact_mod_cast Real.exp_ne_zero x

theorem triple_zeroSet (x : ℝ) (u v : ℂ) : (triplePoint x u v).zeroSet = {2,4} := by
  have hr : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero x
  ext j
  fin_cases j <;> simp [Seed.Point.mem_zeroSet, triplePoint, Seed.Point.a, tripleSeed, hr]

theorem triple_selected_log (x : ℝ) (u v : ℂ) :
    GlobalLiouvilleField.A tripleSeed (triplePoint x u v) 0 = x := by
  simp [GlobalLiouvilleField.A, triplePoint, Seed.Point.a, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos x), Real.log_exp]

/-- Native drift at the exact cutoff boundary, with TWO other mutable coordinates zero. -/
theorem triple_cutoff_boundary (u v : ℂ) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    GlobalLiouvilleField.L tripleSeed triple_unimodular ε κ hδ
      (triplePoint (-2*ε) u v) 0 = -2*ε := by
  have h := NativeRadialOrbit.L_eq_A_of_ge_cutoff tripleSeed triple_unimodular
    hε hκ hδ (triplePoint (-2*ε) u v) 0
    (triple_selected_nonzero _ _ _) (by rw [triple_selected_log])
  simpa only [triple_selected_log] using h

section TripleCurves
variable {ε κ δ t₀ η x : ℝ} {u v : ℂ}
variable (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η)
variable {γ : ℝ → tripleSeed.Point}
variable (hγ : letI := SmoothAtlas.charts tripleSeed triple_unimodular
  IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*6))) γ
    (GlobalLiouvilleField.Z tripleSeed triple_unimodular ε κ hδ) (Ioi (t₀-η)))
variable (hinit : γ t₀ = triplePoint x u v)
include hε hκ hδ hη hγ hinit

/-- The two zero coordinates remain zero along the supplied actual native curve. -/
theorem triple_two_zeros_persist {t : ℝ} (ht : 0 ≤ t) :
    (γ (t₀+t)).a 2 = 0 ∧ (γ (t₀+t)).a 4 = 0 := by
  have hs : t₀ ∈ Ioi (t₀-η) := by change t₀-η < t₀; linarith
  have ht' : t₀+t ∈ Ioi (t₀-η) := by change t₀-η < t₀+t; linarith
  constructor
  · apply (ZeroStratumInvariance.coordinate_zero_iff tripleSeed triple_unimodular
      hε hκ hδ hγ isPreconnected_Ioi hs ht' 2).mp
    rw [hinit]
    rfl
  · apply (ZeroStratumInvariance.coordinate_zero_iff tripleSeed triple_unimodular
      hε hκ hδ hγ isPreconnected_Ioi hs ht' 4).mp
    rw [hinit]
    rfl

/-- The positive scalar law is obtained from the actual native field. -/
theorem triple_positive_log (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0 = x * Real.exp t := by
  have hj : (γ t₀).a 0 ≠ 0 := by rw [hinit]; exact triple_selected_nonzero _ _ _
  have hA : GlobalLiouvilleField.A tripleSeed (γ t₀) 0 = x := by
    rw [hinit, triple_selected_log]
  simpa only [hA] using NativeRadialOrbit.positive_log_law tripleSeed triple_unimodular
    hε hκ hδ hη hγ 0 hj (by rw [hA]; exact hx) ht

/-- The zero logarithm remains zero, even though the other zero strata are present. -/
theorem triple_zero_log (hx : x = 0) {t : ℝ} (ht : 0 ≤ t) :
    GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0 = 0 := by
  have hj : (γ t₀).a 0 ≠ 0 := by rw [hinit]; exact triple_selected_nonzero _ _ _
  have hA : GlobalLiouvilleField.A tripleSeed (γ t₀) 0 = 0 := by
    rw [hinit, triple_selected_log, hx]
  exact NativeRadialOrbit.zero_log_law tripleSeed triple_unimodular
    hε hκ hδ hη hγ 0 hj hA ht

/-- Every conclusion comes from the native negative-law theorem. -/
theorem triple_negative_logs (hx : x < 0) :
    (∀ t ≥ 0, GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0 ≤ x) ∧
    (∀ t ≥ 0, GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0 < 0) ∧
    AntitoneOn (fun t => GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0) (Ici 0) ∧
    (∀ t ≥ 0, GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0 ≤
      x + (x - PrimitiveCutoffs.radial ε κ x) * t) ∧
    Tendsto (fun t => GlobalLiouvilleField.A tripleSeed (γ (t₀+t)) 0) atTop atBot ∧
    Tendsto (fun t => ‖(γ (t₀+t)).a 0‖) atTop (𝓝 0) := by
  have hj : (γ t₀).a 0 ≠ 0 := by rw [hinit]; exact triple_selected_nonzero _ _ _
  have hA : GlobalLiouvilleField.A tripleSeed (γ t₀) 0 = x := by
    rw [hinit, triple_selected_log]
  simpa only [hA] using NativeRadialOrbit.negative_log_laws tripleSeed triple_unimodular
    hε hκ hδ hη hγ 0 hj (by rw [hA]; exact hx)
end TripleCurves

/-- The full skew determinant-one matrix remains, even when all vertices are frozen. -/
def frozenSeed : Seed 2 where
  B := Examples.a2Matrix
  mutable := ∅
  skew := Examples.a2Seed.skew
  acyclic := ⟨fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

theorem frozen_unimodular : frozenSeed.Unimodular := Examples.a2Seed_unimodular

/-- Both frozen coordinates vary independently in actual complex points. -/
def frozenPoint (x y : ℝ) : frozenSeed.Point :=
  ⟨(![(Real.exp x : ℂ), (Real.exp y : ℂ)],
    fun j => False.elim (Finset.notMem_empty j.val j.property)), by
    constructor
    · intro j
      exact False.elim (Finset.notMem_empty j.val j.property)
    · intro j _
      fin_cases j <;> simp [Real.exp_ne_zero]⟩

theorem frozen_coordinates (x y : ℝ) :
    (frozenPoint x y).a = ![(Real.exp x : ℂ), (Real.exp y : ℂ)] := rfl

theorem frozen_norms (x y : ℝ) :
    ‖(frozenPoint x y).a 0‖ = Real.exp x ∧ ‖(frozenPoint x y).a 1‖ = Real.exp y := by
  simp [frozenPoint, Seed.Point.a, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos x), abs_of_pos (Real.exp_pos y)]

theorem frozen_logs (x y : ℝ) :
    GlobalLiouvilleField.A frozenSeed (frozenPoint x y) 0 = x ∧
    GlobalLiouvilleField.A frozenSeed (frozenPoint x y) 1 = y := by
  simp [GlobalLiouvilleField.A, frozenPoint, Seed.Point.a, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos x), abs_of_pos (Real.exp_pos y), Real.log_exp]

section FrozenFlow
variable {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ)
variable (flow : Flow ℝ frozenSeed.Point)
variable (hflow : letI := SmoothAtlas.charts frozenSeed frozen_unimodular
  ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*2))) (fun t => flow t p)
    (GlobalLiouvilleField.Z frozenSeed frozen_unimodular ε κ hδ) univ)

include hε hκ hδ hflow

/-- Both frozen coordinates obey equality, rather than merely a disk bound. -/
theorem frozen_trapped_norms {x y : ℝ} (hp : frozenPoint x y ∈ trappedSet flow) :
    ‖(frozenPoint x y).a 0‖ = 1 ∧ ‖(frozenPoint x y).a 1‖ = 1 :=
  ⟨NativeRadialOrbit.frozen_norm_eq_one_of_mem_trappedSet frozenSeed frozen_unimodular
      hε hκ hδ flow hflow hp 0 (by simp [frozenSeed]),
    NativeRadialOrbit.frozen_norm_eq_one_of_mem_trappedSet frozenSeed frozen_unimodular
      hε hκ hδ flow hflow hp 1 (by simp [frozenSeed])⟩

theorem frozen_trapped_parameters {x y : ℝ} (hp : frozenPoint x y ∈ trappedSet flow) :
    x = 0 ∧ y = 0 := by
  obtain ⟨h0, h1⟩ := frozen_trapped_norms hε hκ hδ flow hflow hp
  rw [(frozen_norms x y).1] at h0
  rw [(frozen_norms x y).2] at h1
  exact ⟨Real.exp_injective (h0.trans Real.exp_zero.symm), Real.exp_injective (h1.trans Real.exp_zero.symm)⟩

theorem frozen_not_trapped_of_nonzero_parameter {x y : ℝ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    frozenPoint x y ∉ trappedSet flow := by
  intro hp
  have h := frozen_trapped_parameters hε hκ hδ flow hflow hp
  exact hxy.elim (fun hx => hx h.1) (fun hy => hy h.2)

/-- Explicit tests on either side of radius one in EACH independent frozen coordinate. -/
theorem frozen_both_sides_of_one :
    frozenPoint 1 0 ∉ trappedSet flow ∧ frozenPoint (-1) 0 ∉ trappedSet flow ∧
    frozenPoint 0 1 ∉ trappedSet flow ∧ frozenPoint 0 (-1) ∉ trappedSet flow := by
  refine ⟨frozen_not_trapped_of_nonzero_parameter hε hκ hδ flow hflow (by norm_num),
    frozen_not_trapped_of_nonzero_parameter hε hκ hδ flow hflow (by norm_num),
    frozen_not_trapped_of_nonzero_parameter hε hκ hδ flow hflow (by norm_num),
    frozen_not_trapped_of_nonzero_parameter hε hκ hδ flow hflow (by norm_num)⟩
end FrozenFlow



/-- The positive example leaves every compact set despite two simultaneous other zeros. -/
theorem triple_positive_escape (u v : ℂ) {ε κ δ t₀ η x : ℝ}
    (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (hη : 0 < η) (hx : 0 < x)
    {γ : ℝ → tripleSeed.Point}
    (hγ : letI := SmoothAtlas.charts tripleSeed triple_unimodular
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model 12)) γ
        (Z tripleSeed triple_unimodular ε κ hδ) (Ioi (t₀-η)))
    (hinit : γ t₀ = triplePoint x u v) :
    (∀ K : Set tripleSeed.Point, IsCompact K → ∃ T ≥ t₀, ∀ t ≥ T, γ t ∉ K) ∧
    ¬ IsCompact (closure (γ '' Ici t₀)) := by
  have hn : 1 < ‖(γ t₀).a 0‖ := by
    rw [hinit]
    simpa [triplePoint, Seed.Point.a] using Real.one_lt_exp_iff.mpr hx
  exact ⟨fun _ hK => eventually_not_mem_compact tripleSeed triple_unimodular
    hε hκ hδ hη hγ 0 hn hK,
    not_isCompact_closure_forward_image tripleSeed triple_unimodular hε hκ hδ hη hγ 0 hn⟩

/-- Dimension zero still has an actual determinant-one seed. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem empty_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

/-- The identity flow is an actual solution in dimension zero. -/
theorem dimension_zero_flow_native (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts emptySeed empty_unimodular
    ∀ p, IsMIntegralCurveOn (I := 𝓘(ℝ, Model 0))
      (fun t => Flow.id ℝ emptySeed.Point t p)
      (Z emptySeed empty_unimodular ε κ hδ) univ := by
  letI := SmoothAtlas.charts emptySeed empty_unimodular
  intro p t _
  have hz : Z emptySeed empty_unimodular ε κ hδ p = 0 := by
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  simp only [Flow.id_apply, id_eq, hz]
  convert (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model (2*0)))
    (x := t) p).hasMFDerivWithinAt (s := univ) using 1 <;> simp <;> rfl

/-- The native supplied-flow theorem applies to the dimension-zero trapped point. -/
theorem dimension_zero_trapped {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : emptySeed.Point) :
    p ∈ trappedSet (Flow.id ℝ emptySeed.Point) ∧
    (∀ j : Fin 0, ‖p.a j‖ ≤ 1) ∧
    (∀ j : Fin 0, j ∉ emptySeed.mutable → ‖p.a j‖ = 1) := by
  have hp : p ∈ trappedSet (Flow.id ℝ emptySeed.Point) := by
    change IsCompact (closure ((Flow.id ℝ emptySeed.Point).forwardOrbit p))
    rw [Flow.forwardOrbit_eq_range_nonneg]
    simp only [Flow.id_apply, id_eq, range_const, closure_singleton]
    exact isCompact_singleton
  exact ⟨hp, trapped_radial_restrictions emptySeed empty_unimodular hε hκ hδ
    (Flow.id ℝ emptySeed.Point) (dimension_zero_flow_native ε κ hδ) hp⟩

end NativeRadialOrbitConsumer
