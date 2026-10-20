# Cluster skeleton formalization

Use native Mathlib manifolds, tangent spaces, differential forms, and flows.
Reuse the pinned FsFltz geometric interfaces; do not replace derivatives or dynamics with arbitrary operations.
The mathematical source is acyclic_cluster_HMS.pdf (2026-10-20), Theorem 2.1 and Lemmas 2.2-2.5, Proposition 2.6.
The final target must use the actual complex points of the exchange equations, with their induced topology.
Frozen variables are nonzero variables, not specialized constants. The full integer matrix is skew-symmetric with determinant one; only the mutable quiver is acyclic.
Keep the coordinate cap set and the dynamical skeleton independently defined.
Do not introduce sorry, axioms, opaque proofs, or assumptions equivalent to the desired conclusion. State unresolved targets as definitions of propositions, never as proved theorems.
Do not weaken the target to obtain compilation. Report each compiled theorem and outstanding obligation accurately.
Keep all project source and dependencies on D: unless the user requests otherwise.
Do not change sources/ in the ChatGPT project mirror, the user's source PDF, or upstream FsFltz sources.
