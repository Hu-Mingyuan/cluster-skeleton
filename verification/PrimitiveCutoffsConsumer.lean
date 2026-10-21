import ClusterSkeleton.PrimitiveCutoffs
import ClusterSkeleton.GlobalTwoForm

/-! Parameterized scalar-cutoff consumers and native transitive axiom checks. -/
noncomputable section
open scoped ContDiff Topology

namespace PrimitiveCutoffsConsumer

open Set Function ClusterSkeleton.PrimitiveCutoffs

/-- The fixed cutoff has a genuine open plateau, compact support and all-order bounds. -/
theorem rho_contract :
    ContDiff ℝ ∞ rho ∧ HasCompactSupport rho ∧
    (∀ x, 0 ≤ rho x ∧ rho x ≤ 1) ∧
    (∀ x, |x| < 1 → rho x = 1) ∧
    (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n rho x| ≤ C) := by
  exact ⟨rho_smooth, rho_compactSupport,
    fun x => ⟨rho_nonneg x, rho_le_one x⟩,
    fun x hx => rho_eq_one hx.le, rho_iteratedDeriv_bound⟩

/-- No cutoff witness is supplied: every allowed intercept uses the constructed function. -/
theorem radial_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ →
      ContDiff ℝ ∞ (radial ε κ) ∧
      (∀ A, radial ε κ A ≤ 0) ∧
      (∀ A, 0 ≤ deriv (radial ε κ) A ∧ deriv (radial ε κ) A ≤ 1) ∧
      (∀ A, A < 0 → A < radial ε κ A) ∧
      (∀ A, -2 * ε ≤ A → radial ε κ A = 0) ∧
      (∀ B : ℝ, ∃ A : ℝ, A < B ∧ A < 0 ∧ radial ε κ A = A + κ) := by
  refine ⟨2 * ε + 1, by linarith, ?_⟩
  intro κ hκ
  have hk : 2 * ε < κ := by linarith
  refine ⟨radial_smooth ε κ, radial_nonpos hk,
    fun A => ⟨radial_deriv_nonneg hk A, radial_deriv_le_one hk A⟩,
    fun A hA => radial_gt hε hk hA,
    fun A hA => radial_eq_zero hk hA, ?_⟩
  intro B
  let A := min B (min 0 (-radialLength ε κ - 2 * ε)) - 1
  have hAB : A < B := by
    dsimp [A]
    have := min_le_left B (min 0 (-radialLength ε κ - 2 * ε))
    linarith
  have hA0 : A < 0 := by
    dsimp [A]
    have := min_le_right B (min 0 (-radialLength ε κ - 2 * ε))
    have := min_le_left (0 : ℝ) (-radialLength ε κ - 2 * ε)
    linarith
  have hAt : A ≤ -radialLength ε κ - 2 * ε := by
    dsimp [A]
    have := min_le_right B (min 0 (-radialLength ε κ - 2 * ε))
    have := min_le_right (0 : ℝ) (-radialLength ε κ - 2 * ε)
    linarith
  exact ⟨A, hAB, hA0, radial_tail hk hAt⟩

/-- The zero plateau includes its boundary and zero itself for arbitrary parameters. -/
theorem radial_plateau (ε κ : ℝ) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) :
    radial ε κ (-2 * ε) = 0 ∧ radial ε κ 0 = 0 := by
  have hk : 2 * ε < κ := by linarith
  exact ⟨radial_eq_zero hk le_rfl, radial_eq_zero hk (by linarith)⟩


/-- Every positive-order native radial derivative is bounded; growth uses the same h. -/
theorem radial_bounds (ε κ : ℝ) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) :
    (∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 ≤ C ∧
      ∀ A, |iteratedDeriv n (radial ε κ) A| ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ A, |radial ε κ A| ≤ C * (1 + |A|)) := by
  have hk : 2 * ε < κ := by linarith
  exact ⟨radial_iteratedDeriv_bound hk, radial_linear_growth hε hk⟩

/-- Arbitrary prescribed arcs have a nonempty identity germ, not merely a zero cutoff. -/
theorem angular_parameters (δ : ℝ) (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    ContDiff ℝ ∞ (vartheta δ) ∧ Function.Periodic (vartheta δ) (2 * Real.pi) ∧
    (∃ r : ℝ, 0 < r ∧ r < δ ∧ ∀ T, |T| ≤ r → vartheta δ T = T) ∧
    (∀ T, |T| ≤ Real.pi → vartheta δ T ≠ 0 → |T| < δ) ∧
    (∀ T, deriv (vartheta δ) T ≤ 1) ∧
    (∀ T, |T| ≤ Real.pi → 0 ≤ T * vartheta δ T) ∧
    (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T, |iteratedDeriv n (vartheta δ) T| ≤ C) := by
  refine ⟨vartheta_smooth hδ, vartheta_periodic δ, ?_,
    fun T hT hn => vartheta_support_principal hδ hT hn,
    vartheta_deriv_le_one hδ, fun T hT => vartheta_local_sign hδ hT,
    vartheta_iteratedDeriv_bound hδ⟩
  refine ⟨angularRadius δ / 2, by linarith [angularRadius_pos hδ],
    by linarith [angularRadius_pos hδ, angularRadius_lt hδ], ?_⟩
  exact fun T hT => vartheta_eq_self hδ hT

/-- The periodic value does not depend on the integer representative. -/
theorem angular_representatives (δ T : ℝ) (k : ℤ) :
    vartheta δ (T + k * (2 * Real.pi)) = vartheta δ T :=
  vartheta_representative_independent δ T k

/-- A nonzero point of the identity germ exists in every prescribed arc. -/
theorem angular_nonzero_germ (δ : ℝ) (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    ∃ T : ℝ, 0 < T ∧ T < δ ∧ vartheta δ T = T ∧ vartheta δ T ≠ 0 := by
  let T := angularRadius δ / 4
  have hT : 0 < T := by dsimp [T]; linarith [angularRadius_pos hδ]
  have hsmall : |T| ≤ angularRadius δ / 2 := by
    rw [abs_of_pos hT]
    dsimp [T]
    linarith [angularRadius_pos hδ]
  have he := vartheta_eq_self hδ hsmall
  exact ⟨T, hT, by dsimp [T]; linarith [angularRadius_pos hδ, angularRadius_lt hδ],
    he, by rw [he]; exact ne_of_gt hT⟩


/-- The closure of angular support, rather than only nonzero values, stays inside the arc. -/
theorem angular_closed_support (δ : ℝ) (hδ : 0 < δ) (_hδπ : δ < Real.pi) :
    ∀ T : ℝ, |T| ≤ Real.pi → T ∈ tsupport (vartheta δ) → |T| < δ :=
  fun T hT hs => vartheta_tsupport_principal hδ hT hs


/-- One negative threshold controls the entire affine tail for every allowed intercept. -/
theorem radial_tail_halfline (ε κ : ℝ) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) :
    ∃ A₀ : ℝ, A₀ < 0 ∧ ∀ A : ℝ, A ≤ A₀ → radial ε κ A = A + κ := by
  have hk : 2 * ε < κ := by linarith
  exact ⟨-radialLength ε κ - 2 * ε,
    by linarith [radial_length_pos hk], fun A hA => radial_tail hk hA⟩

end PrimitiveCutoffsConsumer

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mod := `ClusterSkeleton.PrimitiveCutoffs
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  for name in supplements do
    unless env.contains name do throwError "Missing generated root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut moduleCount : Nat := 0
  let mut otherCount : Nat := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => env.header.moduleNames[i]! == mod
    let named := name.toString.startsWith "ClusterSkeleton.PrimitiveCutoffs." ||
      name.toString.startsWith "_private.ClusterSkeleton.PrimitiveCutoffs."
    if defining || named || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if defining || named then moduleCount := moduleCount + 1
      else otherCount := otherCount + 1
  if moduleCount == 0 || otherCount == 0 then throwError "Empty audit selection"
  logInfo m!"AUDITED {mod}: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
