# Active objective: the skew-symmetrizable skeleton theorem

## Required outcome

Generalize the existing complete skew-symmetric library in this same project to the full weighted theorem in `target-theorem.pdf` and `docs/tex/target-theorem.tex`, using the argument in `proof-blueprint.pdf` and `docs/tex/proof-blueprint.tex`. The previous objective restricted to D = I is superseded. The existing theorem was already complete in that special case; re-verifying it does not complete this task.

Input: an integral unimodular n by n matrix E, mutable indices M with acyclic mutable block, and arbitrary positive rational diagonal D = diag(d_i) such that K = E D is skew-symmetric. E itself need not be skew-symmetric. Frozen coordinates are variable nonzero complex numbers. Retain the unimodular completion hypothesis; do not restrict to principal coefficients. Use column exponents E_ji in the exchange equations, and K in the logarithmic symplectic form. If preserving an internal row convention, prove the exact convention equivalence, including the exchange space and form sign. Monomial interchange alone is insufficient when D is not the identity.

On the actual exchange-equation subtype with inherited topology, construct the smooth presentation, smooth primitive with nondegenerate actual exterior derivative, actual Liouville field, and jointly smooth native flow for all real times. Prove that the relatively compact forward-orbit set of this same flow equals the independently defined coordinate cap and the union of independent strata. Generalize the independent node charts and their torus dimension n - 2|I|. All quantifiers and witness obligations in the target PDF must be preserved.

## Reuse and division of work

Reuse the existing code, project, dependencies, caches, and verification pipeline. All Lean implementation, statement review, and proof verification belong to Archon. Claude Fable is the planner; Claude Opus handles proof and maintenance tasks. At most three Opus proof workers plus one Fable planner may run. Coordinate integration through the existing Archon publication workflow; use the managed build service and its existing build concurrency limit. Do not spawn native provider subagents. Use the existing commits as baseline; do not create another project or restart from an empty library.

The planner must inspect the weighted PDFs and audit every use of Seed.skew, integer inverses, row/column exponents and form coefficients before assigning tasks. Useful dependency boundaries are generalized seed and integer node charts; weighted forms and primitive; weighted field, bounds, complete flow and final skeleton assembly. Resolve real mathematical gaps rather than adding them as final hypotheses. Continue until the generalized theorem is accepted, or report an actual blocking mathematical issue precisely.

The key weighted identities are K e_i = d_i c_i, c_i = E e_i, and c_i^T K^{-1} = -e_i^T/d_i. The Hamiltonian correction has a factor d_i in each summand. These factors cancel from the radial flow equation. The PDF includes the weighted node nondegeneracy argument; density alone does not prove nondegeneracy at boundary points.

## Mandatory acceptance checks

1. A final theorem universally quantified over all admissible E and positive rational D, with no hidden assumption that E is skew-symmetric, D = I, or all weights agree. A structure definition alone is not the theorem.
2. A proved recovery of the old D = I theorem, preserving the actual geometry and convention/sign matching.
3. A consumer instantiating the final theorem on E = [[0,1,-1,0],[-2,0,0,-1],[1,0,0,0],[0,1,0,0]], D = diag(1,2,1,2), M = {0,1} in Lean's zero-based indexing. Check det E = 1, positivity, skew-symmetry of E D, acyclicity and failure of skew-symmetry of E. This consumer supplements, and never replaces, the universal theorem.
4. Full library build and final consumers on the pinned Lean/Mathlib/FsFltz versions. No sorry, extra axiom, unproved opaque geometric constant, modified dependency, dummy carrier, assumed complete flow, or assumed skeleton equality. Transitive axiom allowlist: propext, Classical.choice, Quot.sound.
5. Review the exact generalized theorem type and compare its input, space, logarithmic form, flow and conclusions with the PDFs. Audit all generalized modules and generated declarations, expanding the existing root list and module counts as needed. Update the accepted source manifest only after reviewed integration; keep verification checks substantive.
6. Produce new receipts and logs tied to the new accepted source. Existing receipts and the old G1/G2 audit certify only the skew-symmetric baseline. Do not label the new task complete based on those receipts.

## Documentation and publication

The existing root PDFs have already been overwritten with the weighted target and argument, with no visible document dates. Preserve these filenames. Update current proof maps, statement review and status as the generalized implementation is accepted. Do not create dated alternative PDFs or preserve obsolete task drafts. Preserve Git history. Do not change the weighted target back to D = I to get a successful build. The outer operator handles public GitHub publication; the worker should use the existing Archon publication records and report accepted commits and verified theorem types.
