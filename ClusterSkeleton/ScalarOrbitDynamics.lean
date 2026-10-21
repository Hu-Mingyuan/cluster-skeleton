import ClusterSkeleton.PrimitiveCutoffs
import ClusterSkeleton.Seed
import ClusterSkeleton.TrappedSet
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Scalar consequences of (2.9)--(2.10), and the frozen-coordinate obstruction
in Proposition 2.6. These results do not construct the cluster vector field or flow. -/
noncomputable section
open Set Filter
open scoped Topology

namespace ClusterSkeleton.ScalarOrbitDynamics
open PrimitiveCutoffs

/-- The scalar radial equation on forward time, using the accepted cutoff. -/
def RadialEquation (ε κ : ℝ) (A c : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt A (A t - radial ε κ (A t) * c t) t

theorem radial_drift_monotone {ε κ : ℝ} (hκ : 2 * ε + 1 ≤ κ) :
    Monotone (fun x => x - radial ε κ x) := by
  have hk : 2 * ε < κ := by linarith
  have hd (x : ℝ) := (hasDerivAt_id x).sub (radial_hasDerivAt hk x)
  apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  exact sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem radial_velocity_le {ε κ x c : ℝ} (hκ : 2 * ε + 1 ≤ κ) (hc : c ≤ 1) :
    x - radial ε κ x * c ≤ x - radial ε κ x := by
  have h := mul_le_mul_of_nonpos_left hc (radial_nonpos (by linarith : 2 * ε < κ) x)
  linarith

theorem radial_le_initial {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (hc : ∀ t, 0 ≤ t → c t ≤ 1) (h0 : A 0 < 0) {t : ℝ} (ht : 0 ≤ t) :
    A t ≤ A 0 := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f' := fun s => A s - radial ε κ (A s) * c s)
    (B := fun _ => A 0) (B' := fun _ => 0)
    (fun s hs => (hA s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hA s hs.1).hasDerivWithinAt) (le_refl _)
    (fun s => hasDerivAt_const s (A 0)) _ ⟨ht, le_rfl⟩
  intro s hs he
  have hv := radial_velocity_le (x := A s) hκ (hc s hs.1)
  rw [he] at hv
  have hg := radial_gt hε (by linarith : 2 * ε < κ) h0
  simpa only [he] using lt_of_le_of_lt hv (sub_neg.mpr hg)

theorem radial_negative {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (hc : ∀ t, 0 ≤ t → c t ≤ 1) (h0 : A 0 < 0) {t : ℝ} (ht : 0 ≤ t) :
    A t < 0 := (radial_le_initial hε hκ hA hc h0 ht).trans_lt h0

theorem radial_affine_bound {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (hc : ∀ t, 0 ≤ t → c t ≤ 1) (h0 : A 0 < 0) {t : ℝ} (ht : 0 ≤ t) :
    A t ≤ A 0 + (A 0 - radial ε κ (A 0)) * t := by
  let v := A 0 - radial ε κ (A 0)
  apply image_le_of_deriv_right_le_deriv_boundary
    (f' := fun s => A s - radial ε κ (A s) * c s)
    (B := fun s => A 0 + v * s) (B' := fun _ => v)
    (fun s hs => (hA s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hA s hs.1).hasDerivWithinAt) (by simp) (by fun_prop)
    (fun s _ => by simpa using (((hasDerivAt_id s).const_mul v).const_add (A 0)).hasDerivWithinAt)
    _ ⟨ht, le_rfl⟩
  intro s hs
  exact (radial_velocity_le hκ (hc s hs.1)).trans
    (radial_drift_monotone hκ (radial_le_initial hε hκ hA hc h0 hs.1))

theorem radial_antitone {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (hc : ∀ t, 0 ≤ t → c t ≤ 1) (h0 : A 0 < 0) : AntitoneOn A (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t ht => (hA t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hA t (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  have ht0 : 0 ≤ t := interior_subset ht
  exact (radial_velocity_le hκ (hc t ht0)).trans
    (sub_neg.mpr (radial_gt hε (by linarith)
      (radial_negative hε hκ hA hc h0 ht0))).le

theorem radial_tendsto_atBot {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (hc : ∀ t, 0 ≤ t → c t ≤ 1) (h0 : A 0 < 0) : Tendsto A atTop atBot := by
  have hv : A 0 - radial ε κ (A 0) < 0 :=
    sub_neg.mpr (radial_gt hε (by linarith) h0)
  have hb : Tendsto (fun t : ℝ => (A 0 - radial ε κ (A 0)) * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg hv
  apply tendsto_atBot_mono' atTop _ (tendsto_atBot_add_const_left atTop (A 0) hb)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact radial_affine_bound hε hκ hA hc h0 ht

theorem radial_exp_tendsto_zero {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (hc : ∀ t, 0 ≤ t → c t ≤ 1) (h0 : A 0 < 0) :
    Tendsto (fun t => Real.exp (A t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (radial_tendsto_atBot hε hκ hA hc h0)

/-- Nonnegative initial values never leave the zero-cutoff region. A strict
exponential fence proves this from the equation; no regularity of `c` is needed. -/
theorem radial_eq_exp_of_nonneg {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (h0 : 0 ≤ A 0) {T : ℝ} (hT : 0 ≤ T) : A T = A 0 * Real.exp T := by
  have hk : 2 * ε < κ := by linarith
  let B : ℝ → ℝ := fun t => ε * Real.exp (2 * (t - T))
  have hBpos (t : ℝ) : 0 < B t := mul_pos hε (Real.exp_pos _)
  have hBle (t : ℝ) (ht : t ∈ Icc 0 T) : B t ≤ ε := by
    dsimp [B]
    calc
      ε * Real.exp (2 * (t - T)) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith [ht.2])) hε.le
      _ = ε := mul_one ε
  have hBd (t : ℝ) : HasDerivAt B (2 * B t) t := by
    convert (((((hasDerivAt_id t).sub_const T).const_mul 2).exp).const_mul ε)
      using 1 <;> dsimp [B] <;> first | rfl | ring
  have hcont : ContinuousOn A (Icc 0 T) :=
    fun t ht => (hA t ht.1).continuousAt.continuousWithinAt
  have hfence : ∀ ⦃t⦄, t ∈ Icc 0 T → -A t ≤ B t := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => -A t) (f' := fun t => -(A t - radial ε κ (A t) * c t))
      hcont.neg (fun t ht => (hA t ht.1).neg.hasDerivWithinAt)
      (B := B) (B' := fun t => 2 * B t)
    · linarith [hBpos 0]
    · exact hBd
    · intro t ht heq
      have hb := hBle t ⟨ht.1, ht.2.le⟩
      have hr : radial ε κ (A t) = 0 := radial_eq_zero hk (by linarith)
      rw [hr, zero_mul, sub_zero]
      linarith [hBpos t]
  have hr (t : ℝ) (ht : t ∈ Icc 0 T) : radial ε κ (A t) = 0 := by
    apply radial_eq_zero hk
    have hf := hfence ht
    have hb := hBle t ht
    linarith
  let J : ℝ → ℝ := fun t => A t * Real.exp (-t)
  have hJcont : ContinuousOn J (Icc 0 T) := hcont.mul (by fun_prop)
  have hJd : ∀ t ∈ Ico 0 T, HasDerivWithinAt J 0 (Ici t) t := by
    intro t ht
    have hlin : HasDerivAt A (A t) t := by
      simpa [hr t ⟨ht.1, ht.2.le⟩] using hA t ht.1
    have hj : HasDerivAt J 0 t := by
      convert hlin.mul ((hasDerivAt_id t).neg.exp) using 1 <;> dsimp [J] <;> first | rfl | ring
    exact hj.hasDerivWithinAt
  have hJ : J T = A 0 :=
    eq_of_has_deriv_right_eq (f := J) (g := fun _ => A 0) (f' := fun _ => 0)
      hJd (fun t _ => (hasDerivAt_const t (A 0)).hasDerivWithinAt)
      hJcont continuousOn_const (by simp [J]) T ⟨hT, le_rfl⟩
  have hm := congrArg (fun z : ℝ => z * Real.exp T) hJ
  simpa [J, Real.exp_neg, mul_assoc, Real.exp_ne_zero] using hm

theorem radial_zero {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (h0 : A 0 = 0) {t : ℝ} (ht : 0 ≤ t) : A t = 0 := by
  simpa [h0] using radial_eq_exp_of_nonneg hε hκ hA (le_of_eq h0.symm) ht

theorem radial_positive {ε κ : ℝ} {A c : ℝ → ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hA : RadialEquation ε κ A c)
    (h0 : 0 < A 0) {t : ℝ} (ht : 0 ≤ t) : A t = A 0 * Real.exp t :=
  radial_eq_exp_of_nonneg hε hκ hA h0.le ht

section Frozen
variable {d : ℕ} {S : Seed d}

/-- Globally defined only for the specified frozen coordinate. Its continuity
uses the actual exchange-point nonvanishing condition. -/
theorem continuous_frozen_log (f : Fin d) (hf : f ∉ S.mutable) :
    Continuous (fun p : S.Point => Real.log ‖p.a f‖) := by
  apply Continuous.log
  · exact ((continuous_apply f).comp continuous_subtype_val.fst).norm
  · intro p
    exact norm_ne_zero_iff.mpr (p.frozen_ne_zero f hf)

/-- Conditional on the native frozen ODE, the log radius along the actual
flow is exponential. No existence or cluster-flow identification is asserted. -/
theorem frozen_log_orbit (flow : Flow ℝ S.Point) (f : Fin d)
    (hODE : ∀ p t, HasDerivAt (fun s => Real.log ‖(flow s p).a f‖)
      (Real.log ‖(flow t p).a f‖) t) (p : S.Point) (t : ℝ) :
    Real.log ‖(flow t p).a f‖ = Real.log ‖p.a f‖ * Real.exp t := by
  let A := fun s => Real.log ‖(flow s p).a f‖
  have hd (s : ℝ) : HasDerivAt (fun s => A s * Real.exp (-s)) 0 s := by
    convert (hODE p s).mul ((hasDerivAt_id s).neg.exp) using 1 <;> dsimp [A] <;> first | rfl | ring
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have hm := congrArg (fun x => x * Real.exp t) he
  simpa [A, mul_assoc, ← Real.exp_add] using hm

/-- Compact forward-orbit closure bounds the absolute frozen log radius. -/
theorem trapped_frozen_log_bounded (flow : Flow ℝ S.Point) (f : Fin d)
    (hf : f ∉ S.mutable) {p : S.Point} (hp : p ∈ trappedSet flow) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → |Real.log ‖(flow t p).a f‖| ≤ C := by
  obtain ⟨C, hC⟩ := (hp.image (continuous_frozen_log f hf).abs).bddAbove
  refine ⟨C, fun t ht => hC ?_⟩
  apply mem_image_of_mem
  apply subset_closure
  exact ⟨⟨t, ht⟩, rfl⟩

/-- Frozen radii on trapped orbits are one, under their explicit native ODE.
The absolute-value contradiction excludes both positive and negative log radii. -/
theorem trapped_frozen_norm_eq_one (flow : Flow ℝ S.Point) (f : Fin d)
    (hf : f ∉ S.mutable)
    (hODE : ∀ p t, HasDerivAt (fun s => Real.log ‖(flow s p).a f‖)
      (Real.log ‖(flow t p).a f‖) t)
    {p : S.Point} (hp : p ∈ trappedSet flow) : ‖p.a f‖ = 1 := by
  apply Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (p.frozen_ne_zero f hf))
  by_contra hn
  obtain ⟨C, hC⟩ := trapped_frozen_log_bounded flow f hf hp
  have he : Tendsto (fun t => |Real.log ‖p.a f‖| * Real.exp t) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (abs_pos.mpr hn)
  obtain ⟨t, ht, hb⟩ := ((eventually_ge_atTop (0 : ℝ)).and (he.eventually_gt_atTop C)).exists
  have h := hC t ht
  rw [frozen_log_orbit flow f hODE p t, abs_mul, abs_of_pos (Real.exp_pos t)] at h
  exact (not_lt_of_ge h) hb

end Frozen
end ClusterSkeleton.ScalarOrbitDynamics
