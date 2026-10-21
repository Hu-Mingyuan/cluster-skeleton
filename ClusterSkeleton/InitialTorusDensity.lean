import ClusterSkeleton.IndependentNodeChart
import Mathlib.Topology.NhdsWithin

/-!
# Density of the actual initial torus

The first-coordinate-nonzero locus is dense in each node `uv ≠ 1`, hence in
every independent node product. The accepted homeomorphism identifies its
pullback with the actual initial torus restricted to the independent locus.
The independent-locus cover then gives density in the inherited topology of
the exchange-equation point subtype.
-/

namespace ClusterSkeleton
namespace IndependentNodeChart

open Set

/-- Removing the zero first coordinate leaves a dense subset of the node.
The second coordinate is unrestricted, including when both coordinates vanish. -/
theorem dense_node_fst_ne_zero : Dense {x : Node | x.val.1 ≠ 0} := by
  have hopen : IsOpen {uv : ℂ × ℂ | uv.1 * uv.2 ≠ 1} :=
    isOpen_ne_fun (continuous_fst.mul continuous_snd) continuous_const
  exact (dense_compl_singleton (0 : ℂ)).preimage
    (isOpenMap_fst.comp hopen.isOpenMap_subtype_val)

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))

/-- All first node coordinates are nonzero; complementary torus coordinates
retain their full range of nonzero values. -/
def nodeTorus : Set (Model S I) := {x | ∀ i, (x.1 i).val.1 ≠ 0}

/-- Product density also includes empty node and complementary index types. -/
theorem dense_nodeTorus : Dense (nodeTorus S I) := by
  have h : Dense (Set.pi Set.univ
      (fun _ : {i : Fin d // i ∈ I} => {x : Node | x.val.1 ≠ 0})) :=
    dense_pi _ (fun _ _ => dense_node_fst_ne_zero)
  convert
    h.prod (dense_univ :
      Dense (Set.univ : Set (LaurentCoordinates.NonzeroTorus (Complement S I)))) using 1
  ext x
  simp only [nodeTorus, Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_implies, and_true]

variable (hdet : S.Unimodular) (hI : S.Independent I)

/-- Exact correspondence with the original coordinates, using nonvanishing
outside I from the actual locus and the accepted first-coordinate formula inside I. -/
theorem homeomorph_mem_nodeTorus_iff (p : Locus S I) :
    homeomorph S I hdet hI p ∈ nodeTorus S I ↔ p.val ∈ initialTorus S := by
  change (∀ i : {i : Fin d // i ∈ I},
    ((homeomorph S I hdet hI p).1 i).val.1 ≠ 0) ↔ ∀ j, p.val.a j ≠ 0
  simp only [homeomorph_node_fst]
  constructor
  · intro h j
    by_cases hj : j ∈ I
    · exact h ⟨j, hj⟩
    · exact p.property j hj
  · intro h i
    exact h i

/-- The pullback is literally the restriction of the actual initial torus. -/
theorem preimage_nodeTorus :
    (homeomorph S I hdet hI) ⁻¹' nodeTorus S I =
      Subtype.val ⁻¹' initialTorus S := by
  ext p
  exact homeomorph_mem_nodeTorus_iff S I hdet hI p

include hdet hI in
/-- Density on each actual independent locus, in its inherited topology. -/
theorem dense_initialTorus_locus :
    Dense (Subtype.val ⁻¹' initialTorus S : Set (Locus S I)) := by
  rw [← preimage_nodeTorus S I hdet hI]
  exact (dense_nodeTorus S I).preimage (homeomorph S I hdet hI).isOpenMap

end IndependentNodeChart

/-- The actual initial torus is dense in the actual exchange-equation points.
Only determinant one is required in addition to the existing seed conventions. -/
theorem dense_initialTorus {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    Dense (initialTorus S) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨p, hp⟩ := hUne
  obtain ⟨I, hI, hpI⟩ := exists_independent_candidateChartLocus S p
  obtain ⟨q, hqU, hqT⟩ :=
    (IndependentNodeChart.dense_initialTorus_locus S I hdet hI).inter_open_nonempty
      (Subtype.val ⁻¹' U) (hU.preimage continuous_subtype_val) ⟨⟨p, hpI⟩, hp⟩
  exact ⟨q.val, hqU, hqT⟩

end ClusterSkeleton
