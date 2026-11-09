> Scope: this guide records the verified skew-symmetric (`D = I`) baseline. The current PDFs and [active objective](../docs/roadmap.md) specify the skew-symmetrizable generalization, which is not yet Lean-verified.

# Mathematical statement review

Date: 21 October 2026. Scope: independent reading of the final target, its constructed witnesses, the native geometric interfaces, and the corresponding geometric portion of the supplied manuscript. This review is separate from compilation and is not a claim of a line-by-line independent reproof of the entire Lean library.

## Outcome

No hidden theorem-equivalent premise, circular use of the desired skeleton equality, or weakening of the agreed first-stage real-geometric target was found.

- The carrier is the actual exchange-equation subtype with inherited topology. Frozen coordinates remain nonzero variables, and determinant one concerns the full matrix.
- The native real manifold has dimension `2*d`; the literal coordinate inclusion is proved smooth and immersive.
- The primitive is explicitly constructed and its native exterior derivative is proved equal to the separately constructed global symplectic form.
- The field is determined by contraction with that primitive. Actual native integral curves are extended in both time directions using proved finite-time confinement.
- The cap is defined by coordinate equations; the trapped set is defined by compact closure of forward orbits. The two inclusions concern the same constructed complete flow.
- `FullSkeleton.firstGeometricTarget` proves the original quantified proposition. The final theorem takes no supplied flow, cap invariance, completeness, or either set inclusion as a premise.
- Admissible cutoff parameters are instantiated by `(1,3,1)`; they do not specialize frozen coordinates.
- Nonemptiness is witnessed by `a=1, b=2`.

The reviewed mathematical files are bound to exact hashes in [`accepted-library.json`](accepted-library.json). The independent build and axiom evidence is [`publication-check.json`](publication-check.json).

## Exposition checks

The rewritten proof checks the full residual node block for nondegeneracy, the explicit smooth cutoffs, cancellation of the primitive at simultaneous zeros, zero persistence before completeness, finite-time bounds including positive frozen lower bounds, and both skeleton inclusions.

Cap invariance is proved by propagating the character equation and partner vanishing, rather than inferred solely from tangency to a potentially singular subset. The reverse inclusion treats nonzero interior coordinates and initially zero coordinates separately. Compactness for normalized partners is applied on the closed zero divisor, not assumed on an arbitrary open chart.

## Exact boundary

The theorem proves a real smooth Liouville structure with the prescribed torus form, a jointly smooth complete two-sided flow, and full trapped-set equality. It does not assert a separately assembled complex-manifold structure, algebraic smoothness, holomorphic extension, finite type, cap-product descriptions, generalized cocores, Weinstein structure, an affine Kähler comparison, or categorical HMS.

The global flow is chosen after proving existence. It is not advertised as an executable numerical flow algorithm.

The PDF is a mathematical exposition, not a machine-checked document. The kernel-checked statements are the Lean declarations whose exact source and dependency hashes are recorded by the verifier.
