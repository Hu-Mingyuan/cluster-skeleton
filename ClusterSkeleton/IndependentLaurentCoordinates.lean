import ClusterSkeleton.IntegralBasisCompletion
import ClusterSkeleton.LaurentCoordinates

/-!
# Laurent coordinates for the completed independent seed rows

The prescribed outputs are exactly the restricted seed-row characters.
Node charts and smoothness require further constructions.
-/

open scoped BigOperators

namespace ClusterSkeleton

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))
variable (hdet : S.Unimodular) (hI : S.Independent I)

/-- The completed row basis induces an actual homeomorphism of complex tori. -/
noncomputable def independentRowLaurentHomeomorph :
    LaurentCoordinates.NonzeroTorus {j : Fin d // j ∉ I} ≃ₜ
      LaurentCoordinates.NonzeroTorus (IndependentRowBasisIndex S I) := by
  classical
  exact LaurentCoordinates.nonzeroMonomialHomeomorph
    (independentRowForwardMatrix S I hdet hI)
    (independentRowInverseMatrix S I hdet hI)
    (independentRowForward_mul_inverse S I hdet hI)
    (independentRowInverse_mul_forward S I hdet hI)

/-- Each prescribed output is the original signed seed-row character. -/
theorem independentRowLaurentHomeomorph_inl
    (z : LaurentCoordinates.NonzeroTorus {j : Fin d // j ∉ I})
    (i : {i : Fin d // i ∈ I}) :
    (independentRowLaurentHomeomorph S I hdet hI z (Sum.inl i)).val =
      ∏ j : {j : Fin d // j ∉ I}, (z j).val ^ S.B i j := by
  classical
  simp [independentRowLaurentHomeomorph]

/-- The inverse uses the inverse exponent matrix in the original orientation. -/
theorem independentRowLaurentHomeomorph_symm_apply
    (z : LaurentCoordinates.NonzeroTorus (IndependentRowBasisIndex S I))
    (j : {j : Fin d // j ∉ I}) :
    ((independentRowLaurentHomeomorph S I hdet hI).symm z j).val =
      ∏ i, (z i).val ^ independentRowInverseMatrix S I hdet hI j i := by
  classical
  exact LaurentCoordinates.nonzeroMonomialHomeomorph_symm_apply _ _ _ _ z j

end ClusterSkeleton
