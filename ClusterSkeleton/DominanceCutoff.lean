import ClusterSkeleton.CoordinateLoci
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith

/-!
# Dominance cutoffs and simultaneous zero-stratum localization

Equation (2.5) and the first localization step of Lemma 2.4, manuscript page 10.
All neighborhoods use the inherited topology of the actual exchange points.
No primitive, angular cutoff, flow, or skeleton assertion is made here.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace ClusterSkeleton.DominanceCutoff

/-- A concrete smooth cutoff with the manuscript's orientation and scale. -/
def chi (ε x : ℝ) : ℝ := Real.smoothTransition ((-2 * x - ε) / ε)

theorem contDiff_chi (ε : ℝ) : ContDiff ℝ ∞ (chi ε) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const |>.div_const ε)

theorem chi_nonneg (ε x : ℝ) : 0 ≤ chi ε x := Real.smoothTransition.nonneg _

theorem chi_le_one (ε x : ℝ) : chi ε x ≤ 1 := Real.smoothTransition.le_one _

theorem chi_eq_one_iff {ε x : ℝ} (hε : 0 < ε) : chi ε x = 1 ↔ x ≤ -ε := by
  rw [chi, Real.smoothTransition.eq_one_iff_one_le, le_div_iff₀ hε]
  constructor <;> intro h <;> linarith

theorem chi_eq_zero_iff {ε x : ℝ} (hε : 0 < ε) : chi ε x = 0 ↔ -ε / 2 ≤ x := by
  rw [chi, Real.smoothTransition.zero_iff_nonpos, div_le_iff₀ hε]
  constructor <;> intro h <;> linarith

theorem exists_chi {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, x ≤ -ε → f x = 1) ∧ (∀ x, -ε / 2 ≤ x → f x = 0) :=
  ⟨chi ε, contDiff_chi ε, fun x => ⟨chi_nonneg ε x, chi_le_one ε x⟩,
    fun _ h => (chi_eq_one_iff hε).2 h, fun _ h => (chi_eq_zero_iff hε).2 h⟩

variable {d : ℕ} (S : Seed d)

/-- Only mutable neighbors enter equation (2.5). -/
def mutableNeighbors (i : Fin d) : Finset (Fin d) :=
  S.mutable.filter (fun j => S.B i j ≠ 0)

@[simp] theorem mem_mutableNeighbors (i j : Fin d) :
    j ∈ mutableNeighbors S i ↔ j ∈ S.mutable ∧ S.B i j ≠ 0 :=
  Finset.mem_filter

/-- Exactly the product in equation (2.5), with original real coordinates. -/
def dominance (ε : ℝ) (i : Fin d) (A : Fin d → ℝ) : ℝ :=
  ∏ j ∈ mutableNeighbors S i, chi ε (A i - A j)

theorem dominance_of_no_neighbors (ε : ℝ) (i : Fin d) (A : Fin d → ℝ)
    (h : mutableNeighbors S i = ∅) : dominance S ε i A = 1 := by
  simp [dominance, h]

theorem contDiff_dominance (ε : ℝ) (i : Fin d) :
    ContDiff ℝ ∞ (dominance S ε i) := by
  apply contDiff_prod
  intro j _
  exact (contDiff_chi ε).comp ((contDiff_apply ℝ ℝ i).sub (contDiff_apply ℝ ℝ j))

theorem dominance_nonneg (ε : ℝ) (i : Fin d) (A : Fin d → ℝ) :
    0 ≤ dominance S ε i A :=
  Finset.prod_nonneg fun _ _ => chi_nonneg _ _

theorem dominance_le_one (ε : ℝ) (i : Fin d) (A : Fin d → ℝ) :
    dominance S ε i A ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => chi_nonneg _ _) (fun _ _ => chi_le_one _ _)

theorem dominance_eq_one_of {ε : ℝ} (hε : 0 < ε) (i : Fin d) (A : Fin d → ℝ)
    (h : ∀ j ∈ mutableNeighbors S i, A i - A j ≤ -ε) : dominance S ε i A = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  exact (chi_eq_one_iff hε).2 (h j hj)

theorem dominance_eq_zero_iff {ε : ℝ} (hε : 0 < ε) (i : Fin d) (A : Fin d → ℝ) :
    dominance S ε i A = 0 ↔ ∃ j ∈ mutableNeighbors S i, -ε / 2 ≤ A i - A j := by
  simp only [dominance, Finset.prod_eq_zero_iff, chi_eq_zero_iff hε]

theorem adjacent_exclusion {ε : ℝ} (hε : 0 < ε) (i j : Fin d)
    (hi : i ∈ S.mutable) (hj : j ∈ S.mutable) (hij : S.B i j ≠ 0)
    (A : Fin d → ℝ) : dominance S ε i A = 0 ∨ dominance S ε j A = 0 := by
  -- The exponent matrix is not skew-symmetric when `D ≠ 1`, but vanishing of an
  -- entry is still a symmetric condition.
  have hji : S.B j i ≠ 0 := fun h => hij ((S.B_eq_zero_iff j i).mp h)
  by_cases h : -ε / 2 ≤ A i - A j
  · exact Or.inl ((dominance_eq_zero_iff S hε i A).2
      ⟨j, (mem_mutableNeighbors S i j).2 ⟨hj, hij⟩, h⟩)
  · exact Or.inr ((dominance_eq_zero_iff S hε j A).2
      ⟨i, (mem_mutableNeighbors S j i).2 ⟨hi, hji⟩, by linarith⟩)

/-- The literal logarithms of norms of original coordinates. Equalities below
are restricted to the initial torus, since `Real.log 0 = 0`. -/
def logNorms (q : S.Point) (i : Fin d) : ℝ := Real.log ‖q.a i‖

/-- One finite intersection of strict norm inequalities for all zero vertices
and all their mutable neighbors. This definition makes sense on the stratum. -/
def localizationNeighborhood (ε : ℝ) (p : S.Point) : Set S.Point :=
  {q | ∀ i ∈ p.zeroSet, ∀ j ∈ mutableNeighbors S i,
    ‖q.a i‖ < Real.exp (-ε) * ‖q.a j‖}

theorem isOpen_localizationNeighborhood (ε : ℝ) (p : S.Point) :
    IsOpen (localizationNeighborhood S ε p) := by
  simp only [localizationNeighborhood, Set.ofPred_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun _ =>
    isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_lt (continuous_originalCoordinate S i).norm
    (continuous_const.mul (continuous_originalCoordinate S j).norm)

theorem mem_localizationNeighborhood (ε : ℝ) (p : S.Point) :
    p ∈ localizationNeighborhood S ε p := by
  intro i hi j hj
  have hi0 := ((p.mem_zeroSet i).1 hi).2
  have hj0 : p.a j ≠ 0 := by
    intro hj0
    have hjI := (p.mem_zeroSet j).2 ⟨((mem_mutableNeighbors S i j).1 hj).1, hj0⟩
    exact ((mem_mutableNeighbors S i j).1 hj).2
      (p.zeroSet_independent.exponent_eq_zero hi hjI)
  rw [hi0, norm_zero]
  exact mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hj0)

theorem logNorms_sub_lt {ε : ℝ} {p q : S.Point}
    (hq : q ∈ localizationNeighborhood S ε p) (ht : q ∈ initialTorus S)
    {i j : Fin d} (hi : i ∈ p.zeroSet) (hj : j ∈ mutableNeighbors S i) :
    logNorms S q i - logNorms S q j < -ε := by
  have h := Real.log_lt_log (norm_pos_iff.mpr (ht i)) (hq i hi j hj)
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (ht j)), Real.log_exp] at h
  dsimp [logNorms]
  linarith

/-- Simultaneous localization on one explicit open neighborhood, on its torus
part. Independence is proved from the actual exchange equations, not assumed. -/
theorem localization {ε : ℝ} (hε : 0 < ε) (p : S.Point) :
    ∃ U : Set S.Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U ∩ initialTorus S,
        (∀ i ∈ p.zeroSet, dominance S ε i (logNorms S q) = 1) ∧
        (∀ j ∈ S.mutable, (∃ i ∈ p.zeroSet, S.B i j ≠ 0) →
          dominance S ε j (logNorms S q) = 0) := by
  refine ⟨localizationNeighborhood S ε p, isOpen_localizationNeighborhood S ε p,
    mem_localizationNeighborhood S ε p, ?_⟩
  intro q hq
  have hone : ∀ i ∈ p.zeroSet, dominance S ε i (logNorms S q) = 1 := by
    intro i hi
    apply dominance_eq_one_of S hε
    intro j hj
    exact (logNorms_sub_lt S hq.1 hq.2 hi hj).le
  refine ⟨hone, ?_⟩
  rintro j hj ⟨i, hi, hij⟩
  rcases adjacent_exclusion S hε i j ((p.mem_zeroSet i).1 hi).1 hj hij (logNorms S q) with h | h
  · rw [hone i hi] at h
    exact (one_ne_zero h).elim
  · exact h

end ClusterSkeleton.DominanceCutoff
