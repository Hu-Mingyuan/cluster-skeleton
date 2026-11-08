import ClusterSkeleton.IndependentNodeChart
import ClusterSkeleton.GeometryTarget
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Explicit smooth ambient extensions of the accepted independent node coordinates. -/

noncomputable section
open scoped BigOperators ContDiff
open Set

namespace ClusterSkeleton.IndependentNodeChart

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))

/-- The vector space containing the literal node/torus product. -/
abbrev Vector := ({i : Fin d // i ∈ I} → ℂ × ℂ) × (Complement S I → ℂ)
abbrev Ambient := (Fin d → ℂ) × (S.Mutable → ℂ)

/-- The open node and nonzero-coordinate conditions, with no restriction on either node axis. -/
def domain : Set (Vector S I) :=
  {x | (∀ i, (x.1 i).1 * (x.1 i).2 ≠ 1) ∧ ∀ k, x.2 k ≠ 0}

/-- Forget only the nonvanishing proofs in the accepted product. -/
def flatten (x : Model S I) : Vector S I := (fun i => (x.1 i).val, fun k => (x.2 k).val)

/-- Restore precisely those proofs on the open domain. -/
def pack (x : Vector S I) (hx : x ∈ domain S I) : Model S I :=
  (fun i => ⟨x.1 i, hx.1 i⟩, fun k => ⟨x.2 k, hx.2 k⟩)

@[simp] theorem flatten_pack (x : Vector S I) (hx : x ∈ domain S I) :
    flatten S I (pack S I x hx) = x := rfl
@[simp] theorem pack_flatten (x : Model S I) :
    pack S I (flatten S I x) ⟨fun i => (x.1 i).property, fun k => (x.2 k).property⟩ = x := rfl

theorem flatten_mem_domain (x : Model S I) : flatten S I x ∈ domain S I :=
  ⟨fun i => (x.1 i).property, fun k => (x.2 k).property⟩

theorem isOpen_domain : IsOpen (domain S I) := by
  change IsOpen ({x : Vector S I | ∀ i, (x.1 i).1 * (x.1 i).2 ≠ 1} ∩
    {x : Vector S I | ∀ k, x.2 k ≠ 0})
  simp only [ofPred_forall]
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite fun i => isOpen_ne_fun
      ((show Continuous (fun x : Vector S I => (x.1 i).1) by fun_prop).mul
        (show Continuous (fun x : Vector S I => (x.1 i).2) by fun_prop)) continuous_const
  · exact isOpen_iInter_of_finite fun k => isOpen_ne_fun
      (show Continuous (fun x : Vector S I => x.2 k) by fun_prop) continuous_const

theorem continuous_flatten : Continuous (flatten S I) := by
  exact (continuous_pi fun i => continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun k => continuous_subtype_val.comp
        ((continuous_apply k).comp continuous_snd))

/-- The literal product is homeomorphic to this open subset, in the inherited topologies. -/
def domainHomeomorph : Model S I ≃ₜ domain S I where
  toFun x := ⟨flatten S I x, flatten_mem_domain S I x⟩
  invFun x := pack S I x.val x.property
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_flatten S I).subtype_mk _
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => (((continuous_apply i).comp
        (continuous_fst.comp continuous_subtype_val))).subtype_mk _
    · exact continuous_pi fun k => (((continuous_apply k).comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- Integer Laurent powers are smooth wherever the base is nonzero. -/
theorem contDiffAt_zpow_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : ContDiffAt ℂ ∞ f x) (hx : f x ≠ 0) (n : ℤ) :
    ContDiffAt ℂ ∞ (fun y => f y ^ n) x := by
  cases n with
  | ofNat n => simpa using hf.pow n
  | negSucc n => simpa only [zpow_negSucc] using! (hf.pow (n + 1)).fun_inv (pow_ne_zero _ hx)

variable (hdet : S.Unimodular) (hI : S.Independent I)

/-- Forward formula on the entire ambient coordinate space. -/
def ambientForward (p : Ambient S) : Vector S I :=
  (fun i => (p.1 i, p.2 ⟨i, hI.1 i.property⟩ / S.negativeMonomial p.1 i),
   fun k => ∏ j : {j : Fin d // j ∉ I},
     p.1 j ^ independentRowForwardMatrix S I hdet hI (Sum.inr k) j)

/-- The forward extension agrees with the accepted homeomorphism on its full source. -/
theorem ambientForward_eq (p : Locus S I) :
    ambientForward S I hdet hI p.val.val = flatten S I (homeomorph S I hdet hI p) := by
  apply Prod.ext
  · rfl
  · funext k
    symm
    exact LaurentCoordinates.nonzeroMonomialHomeomorph_apply _ _ _ _ (outside S I p) _

/-- Polynomial node characters together with the free Laurent parameters. -/
def rawParameters (x : Vector S I) : IndependentRowBasisIndex S I → ℂ :=
  Sum.elim (fun i => (x.1 i).1 * (x.1 i).2 - 1) x.2

/-- The original outside coordinates, using exactly the accepted inverse matrix. -/
def rawOutside (x : Vector S I) (j : {j : Fin d // j ∉ I}) : ℂ :=
  ∏ k, rawParameters S I x k ^ independentRowInverseMatrix S I hdet hI j k

/-- Original coordinates extended to the vector space. -/
def rawOriginal (x : Vector S I) (j : Fin d) : ℂ :=
  if hj : j ∈ I then (x.1 ⟨j, hj⟩).1 else rawOutside S I hdet hI x ⟨j, hj⟩

/-- Partner coordinates extended by the actual node and exchange formulas. -/
def rawPartner (x : Vector S I) (j : S.Mutable) : ℂ :=
  if hj : (j : Fin d) ∈ I then
    (x.1 ⟨j, hj⟩).2 * S.negativeMonomial (rawOriginal S I hdet hI x) j
  else (S.positiveMonomial (rawOriginal S I hdet hI x) j +
    S.negativeMonomial (rawOriginal S I hdet hI x) j) / rawOriginal S I hdet hI x j

/-- Ambient extension of the inverse chart. -/
def ambientBackward (x : Vector S I) : Ambient S :=
  (rawOriginal S I hdet hI x, rawPartner S I hdet hI x)

@[simp] theorem rawParameters_flatten (x : Model S I) (k : IndependentRowBasisIndex S I) :
    rawParameters S I (flatten S I x) k = (parameters S I x k).val := by
  cases k <;> rfl

theorem rawOutside_flatten (x : Model S I) (j : {j : Fin d // j ∉ I}) :
    rawOutside S I hdet hI (flatten S I x) j = (recoveredOutside S I hdet hI x j).val := by
  rw [recoveredOutside_apply]
  simp only [rawOutside, rawParameters_flatten]

theorem rawOriginal_flatten (x : Model S I) :
    rawOriginal S I hdet hI (flatten S I x) = original S I hdet hI x := by
  funext j
  by_cases hj : j ∈ I
  · simp [rawOriginal, original, hj, flatten]
  · simp [rawOriginal, original, hj, rawOutside_flatten]

theorem ambientBackward_eq (x : Model S I) :
    ambientBackward S I hdet hI (flatten S I x) =
      ((homeomorph S I hdet hI).symm x).val.val := by
  apply Prod.ext
  · exact rawOriginal_flatten S I hdet hI x
  · change rawPartner S I hdet hI (flatten S I x) = partner S I hdet hI x
    funext j
    unfold rawPartner partner
    rw [rawOriginal_flatten]
    rfl

/-- The polynomial exchange monomials are smooth, including at zero coordinates. -/
theorem contDiff_positiveMonomial (j : Fin d) : ContDiff ℂ ∞ (fun a => S.positiveMonomial a j) := by
  apply contDiff_prod
  intro k _
  exact (contDiff_apply ℂ ℂ k).pow _

theorem contDiff_negativeMonomial (j : Fin d) : ContDiff ℂ ∞ (fun a => S.negativeMonomial a j) := by
  apply contDiff_prod
  intro k _
  exact (contDiff_apply ℂ ℂ k).pow _

/-- Smoothness of the actual forward formulas at every point of the independent locus. -/
theorem contDiffAt_ambientForward (p : Locus S I) :
    ContDiffAt ℂ ∞ (ambientForward S I hdet hI) p.val.val := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.prodMk
    · exact ((contDiff_apply ℂ ℂ (i : Fin d)).comp (show ContDiff ℂ ∞ (Prod.fst : Ambient S → _) from contDiff_fst)).contDiffAt
    · exact (((contDiff_apply ℂ ℂ (⟨i, hI.1 i.property⟩ : S.Mutable)).comp
        (show ContDiff ℂ ∞ (Prod.snd : Ambient S → _) from contDiff_snd)).contDiffAt).div
        (((contDiff_negativeMonomial S i).comp contDiff_fst).contDiffAt)
        (negativeMonomial_ne_zero_on_independent_locus hI p.property i.property)
  · apply contDiffAt_pi.mpr
    intro k
    apply contDiffAt_prod
    intro j _
    exact contDiffAt_zpow_complex (((contDiff_apply ℂ ℂ (j : Fin d)).comp
      contDiff_fst).contDiffAt) (p.property j j.property) _

omit hdet hI in
theorem contDiff_rawParameters (k : IndependentRowBasisIndex S I) :
    ContDiff ℂ ∞ (fun x => rawParameters S I x k) := by
  cases k with
  | inl i => exact ((((contDiff_apply ℂ (ℂ × ℂ) i).comp contDiff_fst).fst).mul
      (((contDiff_apply ℂ (ℂ × ℂ) i).comp contDiff_fst).snd)).sub contDiff_const
  | inr k => exact (contDiff_apply ℂ ℂ k).comp contDiff_snd

omit hdet hI in
theorem rawParameters_ne_zero {x : Vector S I} (hx : x ∈ domain S I)
    (k : IndependentRowBasisIndex S I) : rawParameters S I x k ≠ 0 := by
  cases k with
  | inl i => exact sub_ne_zero.mpr (hx.1 i)
  | inr k => exact hx.2 k

theorem contDiffAt_rawOutside {x : Vector S I} (hx : x ∈ domain S I)
    (j : {j : Fin d // j ∉ I}) : ContDiffAt ℂ ∞ (fun y => rawOutside S I hdet hI y j) x := by
  apply contDiffAt_prod
  intro k _
  exact contDiffAt_zpow_complex (contDiff_rawParameters S I k).contDiffAt
    (rawParameters_ne_zero S I hx k) _

theorem contDiffAt_rawOriginal {x : Vector S I} (hx : x ∈ domain S I) :
    ContDiffAt ℂ ∞ (rawOriginal S I hdet hI) x := by
  apply contDiffAt_pi.mpr
  intro j
  by_cases hj : j ∈ I
  · simp only [rawOriginal, dite_eq_left hj]
    exact (((contDiff_apply ℂ (ℂ × ℂ) (⟨j, hj⟩ : {j : Fin d // j ∈ I})).comp
      contDiff_fst).fst).contDiffAt
  · simp only [rawOriginal, dite_eq_right hj]
    exact contDiffAt_rawOutside S I hdet hI hx ⟨j, hj⟩

theorem rawOriginal_ne_zero {x : Vector S I} (hx : x ∈ domain S I)
    (j : Fin d) (hj : j ∉ I) : rawOriginal S I hdet hI x j ≠ 0 := by
  rw [← flatten_pack S I x hx, rawOriginal_flatten]
  exact original_ne_zero S I hdet hI _ j hj

/-- The inverse formulas are smooth throughout the open product, at all zero strata. -/
theorem contDiffAt_ambientBackward {x : Vector S I} (hx : x ∈ domain S I) :
    ContDiffAt ℂ ∞ (ambientBackward S I hdet hI) x := by
  apply ContDiffAt.prodMk (contDiffAt_rawOriginal S I hdet hI hx)
  apply contDiffAt_pi.mpr
  intro j
  have ho := contDiffAt_rawOriginal S I hdet hI hx
  have hP := (contDiff_positiveMonomial S j).contDiffAt.comp x ho
  have hQ := (contDiff_negativeMonomial S j).contDiffAt.comp x ho
  by_cases hj : (j : Fin d) ∈ I
  · simp only [rawPartner, dite_eq_left hj]
    exact ((((contDiff_apply ℂ (ℂ × ℂ) (⟨j, hj⟩ : {j : Fin d // j ∈ I})).comp
      contDiff_fst).snd).contDiffAt).mul hQ
  · simp only [rawPartner, dite_eq_right hj]
    exact (hP.add hQ).div ((contDiff_apply ℂ ℂ (j : Fin d)).contDiffAt.comp x ho)
      (rawOriginal_ne_zero S I hdet hI hx j hj)

/-- Real smoothness for the fixed real manifold interface. -/
theorem contDiffAt_ambientForward_real (p : Locus S I) :
    ContDiffAt ℝ ∞ (ambientForward S I hdet hI) p.val.val :=
  (contDiffAt_ambientForward S I hdet hI p).restrict_scalars ℝ

theorem contDiffAt_ambientBackward_real {x : Vector S I} (hx : x ∈ domain S I) :
    ContDiffAt ℝ ∞ (ambientBackward S I hdet hI) x :=
  (contDiffAt_ambientBackward S I hdet hI hx).restrict_scalars ℝ

include hdet hI

/-- The completed integral basis accounts for every outside coordinate. -/
theorem basis_cardinality :
    Fintype.card {i : Fin d // i ∈ I} + Fintype.card (Complement S I) =
      Fintype.card {j : Fin d // j ∉ I} := by
  have h := Module.finrank_eq_card_basis (independentRowBasis S I hdet hI)
  simpa only [Module.finrank_pi, Fintype.card_sum] using h.symm

/-- The outside coordinates not consumed by the independent rows, as a literal count:
independence forces `2 * |I| ≤ d`. -/
theorem two_mul_card_le :
    2 * I.card ≤ d := by
  classical
  have hb := basis_cardinality S I hdet hI
  have hin : Fintype.card {i : Fin d // i ∈ I} = I.card := Fintype.card_coe I
  have hout : Fintype.card {j : Fin d // j ∉ I} = d - I.card := by
    rw [Fintype.card_subtype_compl (fun j : Fin d => j ∈ I), hin, Fintype.card_fin]
  have hle : I.card ≤ d := by simpa using Finset.card_le_univ I
  rw [hin, hout] at hb
  omega

/-- The torus exponent of the node chart is literally `d - 2 * |I|`, the reference's
`m + f - 2|I|` for the full set of original coordinates. -/
theorem complementRank_eq_sub_two_mul_card :
    SplitIntegerRows.complementRank (independentRowRightInverse S I)
      = d - 2 * I.card := by
  classical
  have hb := basis_cardinality S I hdet hI
  have hin : Fintype.card {i : Fin d // i ∈ I} = I.card := Fintype.card_coe I
  have hout : Fintype.card {j : Fin d // j ∉ I} = d - I.card := by
    rw [Fintype.card_subtype_compl (fun j : Fin d => j ∈ I), hin, Fintype.card_fin]
  have hle : I.card ≤ d := by simpa using Finset.card_le_univ I
  have hc : Fintype.card (Complement S I)
      = SplitIntegerRows.complementRank (independentRowRightInverse S I) := by
    simp [Complement]
  rw [hin, hout, hc] at hb
  omega

/-- The complex node vector space has dimension d, including empty index sets. -/
theorem vector_finrank_complex : Module.finrank ℂ (Vector S I) = d := by
  have hb := basis_cardinality S I hdet hI
  have hc := Fintype.card_subtype_compl (fun i : Fin d => i ∈ I)
  have hl := Fintype.card_subtype_le (fun i : Fin d => i ∈ I)
  simp only [Fintype.card_fin] at hc hl
  simp only [Vector, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_self, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

/-- Real dimension 2*d, proved from the accepted integer basis completion. -/
theorem vector_finrank_real : Module.finrank ℝ (Vector S I) = 2 * d := by
  rw [finrank_real_of_complex, vector_finrank_complex S I hdet hI]

/-- A fixed real linear identification with the pinned FsFltz model. -/
def modelEquiv : Vector S I ≃L[ℝ] FsFltz.Geometry.Model (2 * d) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    change Module.finrank ℝ (Vector S I) = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * d)))
    rw [vector_finrank_real S I hdet hI, finrank_euclideanSpace_fin])

end ClusterSkeleton.IndependentNodeChart
