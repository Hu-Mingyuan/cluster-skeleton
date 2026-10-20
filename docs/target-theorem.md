# Target theorem: the cluster Liouville skeleton

**Status: specified, not proved.** The Lean proposition is [`ClusterSkeleton.FirstGeometricTarget`](../ClusterSkeleton/GeometryTarget.lean). Defining this proposition supplies no existence proof.

## Input and actual geometric space

Fix an integral skew-symmetric matrix B of size d with determinant one, and a subset of mutable vertices. Require the mutable directed graph, with an arrow i → j when Bᵢⱼ > 0, to be acyclic. All other vertices are frozen. The determinant condition concerns the entire matrix, including frozen vertices.

Let Pᵢ(a) = ∏ⱼ aⱼ^[Bᵢⱼ]₊ and Qᵢ(a) = ∏ⱼ aⱼ^[−Bᵢⱼ]₊. The carrier Y_B is the actual subset of ℂᵈ × ℂ^(mutable) given by

$$a_i b_i=P_i(a)+Q_i(a),\qquad a_f\ne0\ \text{for frozen }f.$$

Use its inherited topology. A smooth presentation must make the actual coordinate inclusion into this ambient vector space a smooth immersion and have real dimension 2d. The presentation is to be constructed, not supplied as a hypothesis on B.

## Required witnesses

Construct a smooth real one-form α on this presentation with nondegenerate exterior derivative. On the initial torus, require

$$d\alpha=\operatorname{Im}\!\left(\frac12\sum_{i,j}B_{ij}\,d\log a_i\wedge d\log a_j\right).$$

The initial torus must be dense. Construct a smooth vector field Z satisfying ι_Z dα = α and a jointly smooth flow Φ, defined for every real time, which solves this actual vector field's ODE. The native Mathlib definitions and Bohan Fang's pinned `CompleteLiouvilleFlow` specify these requirements.

Independently define

$$K_B=\{(a,b)\in Y_B:\ |a_f|=1,\ |a_i|\le1,\ (1-|a_i|^2)b_i=0\}.$$

Prove the literal equality, for this same Φ,

$$\{x\in Y_B:\overline{\{\Phi_t(x):t\ge0\}}\text{ is compact}\}=K_B.$$

## Quantifiers and boundary of this target

The order is: for every d and acyclic seed B, unimodularity implies the existence of the compatible smooth presentation, α, Z and Φ satisfying all the requirements above. Neither the flow nor the skeleton equality is assumed.

This target is the first Liouville/skeleton part of the manuscript's Theorem 2.1. Holomorphic extension of the complex form, finite type, the product description of individual caps, cocores and the categorical HMS statement have additional obligations and are not asserted by this proposition.

Source: [supplied manuscript](../references/acyclic_cluster_HMS.pdf), Section 2. For the dependency order and exact acceptance rules, see the [proof blueprint](proof-blueprint.md) and [roadmap](roadmap.md).
