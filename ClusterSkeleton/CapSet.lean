import ClusterSkeleton.Seed
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The coordinate cap set is compact

The cap set is defined by the coordinate equations in (2.2), independently of
any vector field or flow. Its compactness uses the exchange equations but does
not use acyclicity or unimodularity. This is the compactness argument at the end
of Proposition 2.6, not a proof of the identification with the trapped set.
-/

namespace ClusterSkeleton

open Set

variable {d : ℕ} (S : Seed d)

/-- The geometric candidate for the skeleton, defined in the actual affine
cluster variety. Frozen coordinates are variables of modulus one. -/
def coordinateCap : Set S.Point :=
  {p | (∀ f, f ∉ S.mutable → ‖p.a f‖ = 1) ∧
    ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧
      ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0}

theorem unitPoint_mem_coordinateCap : S.unitPoint ∈ coordinateCap S := by
  simp [coordinateCap]

theorem coordinateCap_nonempty : (coordinateCap S).Nonempty :=
  ⟨S.unitPoint, unitPoint_mem_coordinateCap S⟩

variable {S}

theorem coordinateCap_norm_a_le {p : S.Point} (hp : p ∈ coordinateCap S)
    (j : Fin d) : ‖p.a j‖ ≤ 1 := by
  by_cases hj : j ∈ S.mutable
  · exact (hp.2 ⟨j, hj⟩).1
  · exact le_of_eq (hp.1 j hj)

theorem norm_positiveMonomial_le_one {a : Fin d → ℂ}
    (ha : ∀ j, ‖a j‖ ≤ 1) (i : Fin d) : ‖S.positiveMonomial a i‖ ≤ 1 := by
  simp only [Seed.positiveMonomial, norm_prod, norm_pow]
  exact Finset.prod_le_one₀ (fun j _ => pow_nonneg (norm_nonneg _) _)
    (fun j _ => pow_le_one₀ (norm_nonneg _) (ha j))

theorem norm_negativeMonomial_le_one {a : Fin d → ℂ}
    (ha : ∀ j, ‖a j‖ ≤ 1) (i : Fin d) : ‖S.negativeMonomial a i‖ ≤ 1 := by
  simp only [Seed.negativeMonomial, norm_prod, norm_pow]
  exact Finset.prod_le_one₀ (fun j _ => pow_nonneg (norm_nonneg _) _)
    (fun j _ => pow_le_one₀ (norm_nonneg _) (ha j))

/-- An exchange partner vanishes in the interior of its coordinate disk. -/
theorem coordinateCap_b_eq_zero {p : S.Point} (hp : p ∈ coordinateCap S)
    (i : S.Mutable) (hi : ‖p.a i‖ < 1) : p.b i = 0 := by
  have hreal : (1 - ‖p.a i‖ ^ 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) hi (by decide)))
  have hcomplex : ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hreal
  exact (mul_eq_zero.mp (hp.2 i).2).resolve_left hcomplex

/-- The bound uses both exchange monomials; their coefficients are one. -/
theorem coordinateCap_norm_b_le {p : S.Point} (hp : p ∈ coordinateCap S)
    (i : S.Mutable) : ‖p.b i‖ ≤ 2 := by
  by_cases hi : ‖p.a i‖ < 1
  · simp [coordinateCap_b_eq_zero hp i hi]
  · have hai : ‖p.a i‖ = 1 := le_antisymm (hp.2 i).1 (le_of_not_gt hi)
    calc
      ‖p.b i‖ = ‖p.a i * p.b i‖ := by rw [norm_mul, hai, one_mul]
      _ = ‖S.positiveMonomial p.a i + S.negativeMonomial p.a i‖ := by
        rw [p.exchange i]
      _ ≤ ‖S.positiveMonomial p.a i‖ + ‖S.negativeMonomial p.a i‖ :=
        norm_add_le _ _
      _ ≤ 2 := by
        have hp' := norm_positiveMonomial_le_one (S := S)
          (coordinateCap_norm_a_le hp) (i : Fin d)
        have hn' := norm_negativeMonomial_le_one (S := S)
          (coordinateCap_norm_a_le hp) (i : Fin d)
        linarith

variable (S)

private abbrev Ambient := (Fin d → ℂ) × (S.Mutable → ℂ)

/-- The image of the coordinate cap in its ambient affine coordinate space.
The frozen nonzero condition follows from its modulus-one equations. -/
private def ambientCap : Set (Ambient S) :=
  {x | (∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
    (∀ f, f ∉ S.mutable → ‖x.1 f‖ = 1) ∧
    ∀ i : S.Mutable, ‖x.1 i‖ ≤ 1 ∧
      ((1 - ‖x.1 i‖ ^ 2 : ℝ) : ℂ) * x.2 i = 0}

private theorem isClosed_ambientCap : IsClosed (ambientCap S) := by
  have he : IsClosed {x : Ambient S | ∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i} := by
    simp only [setOf_forall]
    refine isClosed_iInter fun i => isClosed_eq (by fun_prop) ?_
    unfold Seed.positiveMonomial Seed.negativeMonomial
    fun_prop
  have hf : IsClosed {x : Ambient S | ∀ f, f ∉ S.mutable → ‖x.1 f‖ = 1} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  have hm : IsClosed {x : Ambient S | ∀ i : S.Mutable,
      ‖x.1 i‖ ≤ 1 ∧ ((1 - ‖x.1 i‖ ^ 2 : ℝ) : ℂ) * x.2 i = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i =>
      (isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const)
  exact he.inter (hf.inter hm)

private theorem image_coordinateCap :
    Subtype.val '' coordinateCap S = ambientCap S := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2.1, hp⟩
  · intro hx
    have hfn : ∀ f, f ∉ S.mutable → x.1 f ≠ 0 := by
      intro f hf hzero
      have hnorm := hx.2.1 f hf
      simpa [hzero] using hnorm
    exact ⟨⟨x, hx.1, hfn⟩, hx.2, rfl⟩

/-- Compactness is proved in the inherited topology of the actual point set.
In particular, it is not supplied as an extra assumption on a model. -/
theorem isCompact_coordinateCap : IsCompact (coordinateCap S) := by
  have hclosed : IsClosed (Subtype.val '' coordinateCap S) := by
    rw [image_coordinateCap]
    exact isClosed_ambientCap S
  have hbound : Subtype.val '' coordinateCap S ⊆
      Metric.closedBall (0 : Ambient S) 2 := by
    rintro x ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change max ‖p.a‖ ‖p.b‖ ≤ 2
    refine max_le ?_ ?_
    · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2
        (fun j => (coordinateCap_norm_a_le hp j).trans (by norm_num))
    · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2
        (coordinateCap_norm_b_le hp)
  have hc : IsCompact (Subtype.val '' coordinateCap S) :=
    (isCompact_closedBall (0 : Ambient S) 2).of_isClosed_subset hclosed hbound
  exact Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr hc

end ClusterSkeleton
