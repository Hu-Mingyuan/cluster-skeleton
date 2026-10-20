# Proof blueprint

This document links the manuscript's geometric argument to the Lean development. A source proof written below becomes a verified Lean result only after the build and transitive axiom audit succeed; the machine-readable receipt is `verification/first-batch.json`.

| Mathematical component | Lean location | Current scope |
| --- | --- | --- |
| Acyclic seed, mutable/frozen coordinates, actual exchange variety | [Seed](../ClusterSkeleton/Seed.lean) | Definitions; explicit nonempty point; acyclicity bridge |
| No adjacent zero coordinates, Lemma 2.2 | [ZeroSet](../ClusterSkeleton/ZeroSet.lean) | Proof written for general finite acyclic seeds |
| Independent coordinate loci cover Y_B | [CoordinateLoci](../ClusterSkeleton/CoordinateLoci.lean) | Open-cover proofs; no node-chart isomorphism claimed |
| Coordinate cap K_B | [CapSet](../ClusterSkeleton/CapSet.lean) | Bounds and compactness proof |
| Full forward trapped set | [TrappedSet](../ClusterSkeleton/TrappedSet.lean) | Native real flow; generic compact-invariance lemma |
| Exact Liouville/skeleton statement | [GeometryTarget](../ClusterSkeleton/GeometryTarget.lean) | Defined target and adapter to the pinned geometric library |
| Integral node charts and atlas | Not constructed | Next obligation |
| Smooth primitive through simultaneous zeros | Not constructed | Requires normalized node coordinates and cutoffs |
| Actual complete Liouville flow | Not constructed | Requires differential equations and global growth bounds |
| Equality of trapped set and K_B | Not proved | Both dynamical inclusions remain to be established for the constructed flow |

## 1. Zero-set independence

Use well-founded induction on the finite mutable arrow relation. At a zero coordinate aᵢ, induction excludes zero incoming neighbours, so Qᵢ is nonzero. A zero outgoing neighbour would force Pᵢ = 0, contradicting aᵢbᵢ = Pᵢ + Qᵢ. Skew-symmetry gives pairwise independence. This argument does not require unimodularity and includes multiple arrows and variable frozen coordinates.

## 2. Elementary compactness

On K_B every original coordinate has norm at most one. If |aᵢ| < 1, the cap equation forces bᵢ = 0. If |aᵢ| = 1, the exchange relation and the bounds on Pᵢ and Qᵢ give |bᵢ| ≤ 2. The ambient image of K_B is closed and bounded in finite-dimensional complex coordinate space. Pull compactness back through the actual subtype embedding. The open condition on frozen coordinates causes no gap because |a_f| = 1 on the cap.

## 3. Node charts and symplectic extension

For each independent zero set, invert coordinates outside it and show the relevant Qᵢ are units. Normalize b̃ᵢ = bᵢ/Qᵢ and use aᵢb̃ᵢ = 1 + qᵢ, qᵢ = Pᵢ/Qᵢ. Unimodularity must provide the necessary integral torus coordinates, including simultaneous rows. Construct the actual chart maps and inverses; then prove smooth transitions, density of the initial torus and nondegeneracy of the extended form.

## 4. Primitive and complete flow

Implement the manuscript's dominance cutoffs and correction H in α = AᵀB dθ − dH. Prove smooth extension at every simultaneous-zero stratum using the normalized node coordinates and analytic cancellation. Compute the vector field from this same primitive. Prove estimates on all strata sufficient for a two-sided complete flow. Upstream completeness results may be reused only after their specific hypotheses have been established.

## 5. Full skeleton identification

First prove K_B forward invariant, then use compactness for K_B ⊆ trappedSet. For the converse, exclude every outside point using the radial inequalities, the independent limiting zero set, eventual angular equations and ODE uniqueness. Include points starting on a zero stratum. Compactness of K_B alone proves neither this converse nor finite type.

The separate finite-type milestone uses backward control. Cap products, generalized cocores and HMS follow only after their own arguments are formalized.
