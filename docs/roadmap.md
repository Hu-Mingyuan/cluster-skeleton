# Scope and completion criteria

The target is a Liouville form on the actual unimodular acyclic exchange space, with complete flow and the specified full skeleton.

1. Actual exchange points and a native Mathlib smooth manifold presentation.
2. Global real symplectic two-form with the prescribed torus restriction.
3. Smooth global primitive and its actual Liouville vector field.
4. Complete two-sided native flow of that field.
5. Both inclusions between its full trapped set and the independent coordinate cap.
6. Quantified existence theorem, source-bound build, axiom audit, and mathematical statement review.

The source chain ends with `FullSkeleton.firstGeometricTarget`. See the [proof-to-code map](proof-blueprint.md), [target statement](target-theorem.md), and [verification records](../verification/README.md).

Completion requires the actual final theorem and its dependencies to pass Lean, with no proof placeholders or extra geometric axioms. Mathematical review must also check that the definitions and quantifiers express the intended statement. Compiling a proposition definition or completing an agent session alone does not meet these criteria.

Finite type, cap products, cocores, and categorical HMS are outside this target.
