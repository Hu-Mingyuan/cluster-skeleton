import ClusterSkeleton.ZeroSet
import Mathlib.Topology.Separation.Hausdorff

/-!
# Open coordinate loci before the node-chart construction

These loci use the actual affine coordinate subtype and its inherited topology.
The independent loci cover the space by the proved zero-set lemma. No algebraic
or smooth isomorphism with a product of node models is claimed in this file.
-/

namespace ClusterSkeleton

open Set

variable {d : ℕ}

/-- Each original coordinate is continuous in the native subtype topology. -/
theorem continuous_originalCoordinate (S : Seed d) (j : Fin d) :
    Continuous (fun p : S.Point => p.a j) := by
  change Continuous (fun p : S.Point => p.val.1 j)
  exact (continuous_apply j).comp (continuous_fst.comp continuous_subtype_val)

/-- The candidate chart locus obtained by inverting all coordinates outside I.
Independence is required for the later node-chart identification, not for this
topological definition. -/
def candidateChartLocus (S : Seed d) (I : Finset (Fin d)) : Set S.Point :=
  {p | ∀ j, j ∉ I → p.a j ≠ 0}

/-- Every candidate coordinate locus is open in the actual cluster space. -/
theorem isOpen_candidateChartLocus (S : Seed d) (I : Finset (Fin d)) :
    IsOpen (candidateChartLocus S I) := by
  simp only [candidateChartLocus, ofPred_forall]
  refine isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_ne_fun (continuous_originalCoordinate S j) continuous_const

/-- The actual zero set selects an independent candidate locus through each point. -/
theorem exists_independent_candidateChartLocus (S : Seed d) (p : S.Point) :
    ∃ I : Finset (Fin d), S.Independent I ∧ p ∈ candidateChartLocus S I :=
  p.exists_independent_nonvanishing_locus

/-- The independent coordinate loci form an open cover; their product-chart
isomorphisms remain a separate construction. -/
theorem iUnion_independent_candidateChartLocus (S : Seed d) :
    (⋃ I : {I : Finset (Fin d) // S.Independent I}, candidateChartLocus S I.val) =
      Set.univ := by
  ext p
  constructor
  · intro _
    exact mem_univ p
  · intro _
    obtain ⟨I, hI, hp⟩ := exists_independent_candidateChartLocus S p
    exact mem_iUnion.mpr ⟨⟨I, hI⟩, hp⟩

/-- The original torus is defined by the actual cluster coordinates. -/
def initialTorus (S : Seed d) : Set S.Point :=
  {p | ∀ j, p.a j ≠ 0}

theorem initialTorus_eq_candidateChartLocus_empty (S : Seed d) :
    initialTorus S = candidateChartLocus S ∅ := by
  ext p
  simp [initialTorus, candidateChartLocus]

/-- The original torus is open in the actual inherited topology. -/
theorem isOpen_initialTorus (S : Seed d) : IsOpen (initialTorus S) := by
  rw [initialTorus_eq_candidateChartLocus_empty]
  exact isOpen_candidateChartLocus S ∅

/-- The actual coordinate torus is inhabited; the target is not made vacuous
by an empty point type. Every original coordinate is one at this point. -/
theorem initialTorus_nonempty (S : Seed d) : (initialTorus S).Nonempty := by
  refine ⟨S.unitPoint, ?_⟩
  change ∀ j : Fin d, S.unitPoint.a j ≠ 0
  intro j
  simp

end ClusterSkeleton
