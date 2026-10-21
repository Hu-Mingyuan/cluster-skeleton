import ClusterSkeleton.IndependentLaurentCoordinates
import ClusterSkeleton.TorusChart

/-!
# The independent-locus node homeomorphism

The source is the actual exchange-point locus with its inherited topology.
The target is the literal product of nodes `uv ≠ 1` and punctured complex lines,
indexed by the complement of the accepted integral row basis (Lemma 2.2).
-/

open scoped BigOperators

namespace ClusterSkeleton
namespace IndependentNodeChart

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))

abbrev Locus := {p : S.Point // p ∈ candidateChartLocus S I}
abbrev Node := {uv : ℂ × ℂ // uv.1 * uv.2 ≠ 1}
abbrev Complement := Fin (SplitIntegerRows.complementRank (independentRowRightInverse S I))
abbrev Model := ({i : Fin d // i ∈ I} → Node) ×
  LaurentCoordinates.NonzeroTorus (Complement S I)

/-- Actual original coordinates outside the independent set. -/
def outside (p : Locus S I) : LaurentCoordinates.NonzeroTorus {j : Fin d // j ∉ I} :=
  fun j => ⟨p.val.a j, p.property j j.property⟩

theorem continuous_outside : Continuous (outside S I) := by
  apply continuous_pi
  intro j
  exact ((continuous_originalCoordinate S j).comp continuous_subtype_val).subtype_mk _

variable {S I}

/-- Independence deletes the inside factors, including at simultaneous zeroes. -/
theorem row_product_eq_outside (hI : S.Independent I) (a : Fin d → ℂ)
    (i : {i : Fin d // i ∈ I}) :
    (∏ j, a j ^ S.B i j) = ∏ j : {j : Fin d // j ∉ I}, a j ^ S.B i j := by
  classical
  refine Finset.prod_congr_set {j : Fin d | j ∉ I}
    (fun j => a j ^ S.B i j) (fun j => a j ^ S.B i j) (fun _ _ => rfl) ?_
  intro j hj
  have hjI : j ∈ I := by simpa using hj
  simp [hI.2 i i.property j hjI]

/-- The positive monomial depends only on the outside coordinates. -/
theorem positiveMonomial_congr_outside (hI : S.Independent I)
    {a a' : Fin d → ℂ} (h : ∀ j, j ∉ I → a j = a' j)
    (i : {i : Fin d // i ∈ I}) : S.positiveMonomial a i = S.positiveMonomial a' i := by
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ I
  · simp [hI.2 i i.property j hj]
  · rw [h j hj]

/-- The negative monomial depends only on the outside coordinates. -/
theorem negativeMonomial_congr_outside (hI : S.Independent I)
    {a a' : Fin d → ℂ} (h : ∀ j, j ∉ I → a j = a' j)
    (i : {i : Fin d // i ∈ I}) : S.negativeMonomial a i = S.negativeMonomial a' i := by
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ I
  · simp [hI.2 i i.property j hj]
  · rw [h j hj]

variable (S I) (hdet : S.Unimodular) (hI : S.Independent I)

/-- Bridge from the accepted prescribed Laurent rows to actual exchange points. -/
theorem laurent_inl_eq_exchangeCharacter (p : Locus S I)
    (i : {i : Fin d // i ∈ I}) :
    (independentRowLaurentHomeomorph S I hdet hI (outside S I p) (Sum.inl i)).val =
      exchangeCharacter p.val i := by
  rw [independentRowLaurentHomeomorph_inl, exchangeCharacter_eq_zpow_product,
    row_product_eq_outside hI]
  rfl

/-- Forward coordinates: `a_i`, `b_i/Q_i`, and the complementary Laurent outputs. -/
noncomputable def forward (p : Locus S I) : Model S I :=
  (fun i => ⟨(p.val.a i, normalizedPartner p.val ⟨i, hI.1 i.property⟩),
    normalized_node_product_ne_one hI p.property ⟨i, hI.1 i.property⟩ i.property⟩,
   fun k => independentRowLaurentHomeomorph S I hdet hI (outside S I p) (Sum.inr k))

/-- Concatenate `q_i = u_i*v_i-1` with the free nonzero coordinates. -/
noncomputable def parameters (x : Model S I) :
    LaurentCoordinates.NonzeroTorus (IndependentRowBasisIndex S I) :=
  Sum.elim (fun i => ⟨(x.1 i).val.1 * (x.1 i).val.2 - 1,
    sub_ne_zero.mpr (x.1 i).property⟩) x.2

/-- The outside original coordinates are recovered by the accepted inverse matrix. -/
noncomputable def recoveredOutside (x : Model S I) :
    LaurentCoordinates.NonzeroTorus {j : Fin d // j ∉ I} :=
  (independentRowLaurentHomeomorph S I hdet hI).symm (parameters S I x)

/-- Explicit evaluation by the accepted inverse exponent matrix. -/
theorem recoveredOutside_apply (x : Model S I) (j : {j : Fin d // j ∉ I}) :
    (recoveredOutside S I hdet hI x j).val =
      ∏ k, (parameters S I x k).val ^ independentRowInverseMatrix S I hdet hI j k :=
  independentRowLaurentHomeomorph_symm_apply S I hdet hI (parameters S I x) j

/-- Original coordinates, retaining arbitrary (possibly zero) node coordinates. -/
noncomputable def original (x : Model S I) (j : Fin d) : ℂ :=
  if hj : j ∈ I then (x.1 ⟨j, hj⟩).val.1
  else (recoveredOutside S I hdet hI x ⟨j, hj⟩).val

@[simp] theorem original_inside (x : Model S I) (i : {i : Fin d // i ∈ I}) :
    original S I hdet hI x i = (x.1 i).val.1 := by simp [original, i.property]

@[simp] theorem original_outside (x : Model S I) (j : {j : Fin d // j ∉ I}) :
    original S I hdet hI x j = (recoveredOutside S I hdet hI x j).val := by
  simp [original, j.property]

theorem original_ne_zero (x : Model S I) (j : Fin d) (hj : j ∉ I) :
    original S I hdet hI x j ≠ 0 := by
  simpa only [original, dite_eq_right hj] using (recoveredOutside S I hdet hI x ⟨j, hj⟩).property

theorem negative_original_ne_zero (x : Model S I) (i : {i : Fin d // i ∈ I}) :
    S.negativeMonomial (original S I hdet hI x) i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j ∈ I
  · simp [hI.2 i i.property j hj]
  · exact pow_ne_zero _ (original_ne_zero S I hdet hI x j hj)

/-- The recovered monomial ratio equals precisely `uv-1`. -/
theorem recovered_ratio (x : Model S I) (i : {i : Fin d // i ∈ I}) :
    S.positiveMonomial (original S I hdet hI x) i /
      S.negativeMonomial (original S I hdet hI x) i =
      (x.1 i).val.1 * (x.1 i).val.2 - 1 := by
  have h := congrArg (fun z => (z (Sum.inl i)).val)
    ((independentRowLaurentHomeomorph S I hdet hI).apply_symm_apply (parameters S I x))
  rw [independentRowLaurentHomeomorph_inl] at h
  change (∏ j : {j : Fin d // j ∉ I},
    (recoveredOutside S I hdet hI x j).val ^ S.B i j) = _ at h
  unfold Seed.positiveMonomial Seed.negativeMonomial
  rw [← Finset.prod_div_distrib]
  simp_rw [pow_toNat_div_pow_neg_toNat]
  rw [row_product_eq_outside hI _ i]
  simpa only [original_outside, parameters, Sum.elim_inl] using h

/-- Partners on I use the node coordinate; all others use the exchange equation. -/
noncomputable def partner (x : Model S I) (j : S.Mutable) : ℂ :=
  if hj : (j : Fin d) ∈ I then
    (x.1 ⟨j, hj⟩).val.2 * S.negativeMonomial (original S I hdet hI x) j
  else (S.positiveMonomial (original S I hdet hI x) j +
    S.negativeMonomial (original S I hdet hI x) j) / original S I hdet hI x j

/-- Every reconstructed mutable coordinate satisfies the actual exchange equation. -/
theorem reconstructed_exchange (x : Model S I) (j : S.Mutable) :
    original S I hdet hI x j * partner S I hdet hI x j =
      S.positiveMonomial (original S I hdet hI x) j +
        S.negativeMonomial (original S I hdet hI x) j := by
  classical
  by_cases hj : (j : Fin d) ∈ I
  · rw [partner, dite_eq_left hj]
    have h := (div_eq_iff (negative_original_ne_zero S I hdet hI x ⟨j, hj⟩)).mp
      (recovered_ratio S I hdet hI x ⟨j, hj⟩)
    rw [h]
    rw [show original S I hdet hI x j = (x.1 ⟨j, hj⟩).val.1 from
      original_inside S I hdet hI x ⟨j, hj⟩]
    ring
  · rw [partner, dite_eq_right hj]
    exact mul_div_cancel₀ _ (original_ne_zero S I hdet hI x j hj)

/-- Reconstructed frozen coordinates remain variable and nonzero. -/
theorem reconstructed_frozen (x : Model S I) (f : Fin d) (hf : f ∉ S.mutable) :
    original S I hdet hI x f ≠ 0 :=
  original_ne_zero S I hdet hI x f (fun h => hf (hI.1 h))

/-- Reconstruction lands in the actual exchange-point locus. -/
noncomputable def backward (x : Model S I) : Locus S I :=
  ⟨⟨(original S I hdet hI x, partner S I hdet hI x),
    reconstructed_exchange S I hdet hI x, reconstructed_frozen S I hdet hI x⟩,
    original_ne_zero S I hdet hI x⟩

/-- Forward node equations recover the prescribed Laurent parameters. -/
theorem parameters_forward (p : Locus S I) :
    parameters S I (forward S I hdet hI p) =
      independentRowLaurentHomeomorph S I hdet hI (outside S I p) := by
  funext k
  cases k with
  | inl i =>
    apply Subtype.ext
    change p.val.a i * normalizedPartner p.val ⟨i, hI.1 i.property⟩ - 1 = _
    rw [normalized_node_equation hI p.property ⟨i, hI.1 i.property⟩ i.property,
      laurent_inl_eq_exchangeCharacter]
    ring
  | inr k => rfl

@[simp] theorem recoveredOutside_forward (p : Locus S I) :
    recoveredOutside S I hdet hI (forward S I hdet hI p) = outside S I p := by
  unfold recoveredOutside
  rw [parameters_forward]
  exact (independentRowLaurentHomeomorph S I hdet hI).symm_apply_apply _

@[simp] theorem original_forward (p : Locus S I) :
    original S I hdet hI (forward S I hdet hI p) = p.val.a := by
  funext j
  by_cases hj : j ∈ I
  · simp [original, hj, forward]
  · simp [original, hj, recoveredOutside_forward, outside]

/-- Reconstruction after the forward map is the original actual point. -/
theorem backward_forward (p : Locus S I) :
    backward S I hdet hI (forward S I hdet hI p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact original_forward S I hdet hI p
  · funext j
    change partner S I hdet hI (forward S I hdet hI p) j = p.val.b j
    unfold partner
    rw [original_forward]
    by_cases hj : (j : Fin d) ∈ I
    · simp only [dite_eq_left hj, forward, normalizedPartner]
      exact div_mul_cancel₀ _ (negativeMonomial_ne_zero_on_independent_locus hI p.property hj)
    · rw [dite_eq_right hj, ← p.val.exchange j]
      exact mul_div_cancel_left₀ _ (p.property j hj)

@[simp] theorem outside_backward (x : Model S I) :
    outside S I (backward S I hdet hI x) = recoveredOutside S I hdet hI x := by
  funext j
  apply Subtype.ext
  exact original_outside S I hdet hI x j

/-- The forward map after reconstruction is the original node/torus tuple. -/
theorem forward_backward (x : Model S I) :
    forward S I hdet hI (backward S I hdet hI x) = x := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    apply Prod.ext
    · exact original_inside S I hdet hI x i
    · change partner S I hdet hI x ⟨i, hI.1 i.property⟩ /
        S.negativeMonomial (original S I hdet hI x) i = (x.1 i).val.2
      rw [partner, dite_eq_left i.property]
      exact mul_div_cancel_right₀ _ (negative_original_ne_zero S I hdet hI x i)
  · funext k
    change independentRowLaurentHomeomorph S I hdet hI
      (outside S I (backward S I hdet hI x)) (Sum.inr k) = x.2 k
    rw [outside_backward, recoveredOutside,
      (independentRowLaurentHomeomorph S I hdet hI).apply_symm_apply]
    rfl

/-- Continuity is in the inherited point, product and subtype topologies. -/
theorem continuous_forward : Continuous (forward S I hdet hI) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (continuous_originalCoordinate S i).comp continuous_subtype_val
    · change Continuous (fun p : Locus S I =>
        p.val.val.2 ⟨i, hI.1 i.property⟩ / S.negativeMonomial p.val.a i)
      apply Continuous.div
      · exact (continuous_apply _).comp
          (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
      · exact (continuous_negativeMonomial S i).comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
      · intro p
        exact negativeMonomial_ne_zero_on_independent_locus hI p.property i.property
  · apply continuous_pi
    intro k
    exact (continuous_apply (Sum.inr k)).comp
      ((independentRowLaurentHomeomorph S I hdet hI).continuous.comp (continuous_outside S I))

theorem continuous_parameters : Continuous (parameters S I) := by
  apply continuous_pi
  intro k
  cases k with
  | inl i =>
    apply Continuous.subtype_mk
    exact ((continuous_fst.comp (continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_fst))).mul
      (continuous_snd.comp (continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_fst)))).sub continuous_const
  | inr k => exact (continuous_apply k).comp continuous_snd

theorem continuous_recoveredOutside : Continuous (recoveredOutside S I hdet hI) :=
  (independentRowLaurentHomeomorph S I hdet hI).symm.continuous.comp
    (continuous_parameters S I)

theorem continuous_original : Continuous (original S I hdet hI) := by
  apply continuous_pi
  intro j
  by_cases hj : j ∈ I
  · simp only [original, dite_eq_left hj]
    exact continuous_fst.comp (continuous_subtype_val.comp
      ((continuous_apply (⟨j, hj⟩ : {j : Fin d // j ∈ I})).comp continuous_fst))
  · simp only [original, dite_eq_right hj]
    exact continuous_subtype_val.comp ((continuous_apply (⟨j, hj⟩ : {j : Fin d // j ∉ I})).comp
      (continuous_recoveredOutside S I hdet hI))

theorem continuous_partner : Continuous (partner S I hdet hI) := by
  apply continuous_pi
  intro j
  have hP := (continuous_positiveMonomial S j).comp (continuous_original S I hdet hI)
  have hQ := (continuous_negativeMonomial S j).comp (continuous_original S I hdet hI)
  by_cases hj : (j : Fin d) ∈ I
  · simp only [partner, dite_eq_left hj]
    exact (continuous_snd.comp (continuous_subtype_val.comp
      ((continuous_apply (⟨j, hj⟩ : {j : Fin d // j ∈ I})).comp continuous_fst))).mul hQ
  · simp only [partner, dite_eq_right hj]
    exact (hP.add hQ).div ((continuous_apply (j : Fin d)).comp
      (continuous_original S I hdet hI)) (fun x => original_ne_zero S I hdet hI x j hj)

theorem continuous_backward : Continuous (backward S I hdet hI) :=
  (((continuous_original S I hdet hI).prodMk
    (continuous_partner S I hdet hI)).subtype_mk _).subtype_mk _

/-- Lemma 2.2's explicit node product homeomorphism on actual exchange points.
No nonemptiness or nonvanishing assumption is imposed on coordinates in I. -/
noncomputable def homeomorph : Locus S I ≃ₜ Model S I where
  toFun := forward S I hdet hI
  invFun := backward S I hdet hI
  left_inv := backward_forward S I hdet hI
  right_inv := forward_backward S I hdet hI
  continuous_toFun := continuous_forward S I hdet hI
  continuous_invFun := continuous_backward S I hdet hI

/-- The first node coordinate is the original cluster coordinate. -/
@[simp] theorem homeomorph_node_fst (p : Locus S I) (i : {i : Fin d // i ∈ I}) :
    ((homeomorph S I hdet hI p).1 i).val.1 = p.val.a i := rfl

/-- The second node coordinate is the normalized actual mutation partner. -/
@[simp] theorem homeomorph_node_snd (p : Locus S I) (i : {i : Fin d // i ∈ I}) :
    ((homeomorph S I hdet hI p).1 i).val.2 =
      p.val.b ⟨i, hI.1 i.property⟩ / S.negativeMonomial p.val.a i := rfl

/-- The free coordinates are the complementary Laurent outputs. -/
@[simp] theorem homeomorph_complement (p : Locus S I) (k : Complement S I) :
    (homeomorph S I hdet hI p).2 k =
      independentRowLaurentHomeomorph S I hdet hI (outside S I p) (Sum.inr k) := rfl

/-- The inverse's original coordinates are the explicit piecewise reconstruction. -/
@[simp] theorem homeomorph_symm_a (x : Model S I) :
    ((homeomorph S I hdet hI).symm x).val.a = original S I hdet hI x := rfl

/-- The inverse's mutable partners use the node or exchange formula as appropriate. -/
@[simp] theorem homeomorph_symm_b (x : Model S I) :
    ((homeomorph S I hdet hI).symm x).val.b = partner S I hdet hI x := rfl

end IndependentNodeChart
end ClusterSkeleton
