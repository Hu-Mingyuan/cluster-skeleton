import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# The actual dynamical trapped set

The skeleton convention in Theorem 2.1 of `acyclic_cluster_HMS.pdf` uses
relative compactness of the full forward orbit of the specified flow.
No coordinate cap set or compact-domain presentation enters this definition.
-/

namespace ClusterSkeleton

open Set

variable {X : Type*} [TopologicalSpace X]

/-- Points whose entire forward orbit has compact closure. -/
def trappedSet (flow : Flow ℝ X) : Set X :=
  {x | IsCompact (closure (flow.forwardOrbit x))}

@[simp]
theorem mem_trappedSet {flow : Flow ℝ X} {x : X} :
    x ∈ trappedSet flow ↔ IsCompact (closure (flow.forwardOrbit x)) := Iff.rfl

/-- A forward orbit contained in a compact set is relatively compact. -/
theorem mem_trappedSet_of_forwardOrbit_subset [T2Space X]
    (flow : Flow ℝ X) {K : Set X} (hK : IsCompact K) {x : X}
    (horbit : flow.forwardOrbit x ⊆ K) : x ∈ trappedSet flow :=
  hK.of_isClosed_subset isClosed_closure (closure_minimal horbit hK.isClosed)

/-- Compactness and positive invariance give the easy skeleton inclusion.
The reverse inclusion still requires the escape analysis of the actual field. -/
theorem subset_trappedSet_of_isCompact_forwardInvariant [T2Space X]
    (flow : Flow ℝ X) {K : Set X} (hK : IsCompact K)
    (hinvariant : IsForwardInvariant flow K) : K ⊆ trappedSet flow := by
  intro x hx
  apply mem_trappedSet_of_forwardOrbit_subset flow hK
  rintro y ⟨t, rfl⟩
  exact hinvariant t.property hx

end ClusterSkeleton
