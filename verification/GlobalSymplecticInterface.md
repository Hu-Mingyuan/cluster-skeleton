# Global symplectic composition

`ClusterSkeleton.GlobalSymplectic` imports the independently accepted Global
and B modules. Its only hypothesis beyond `S : Seed d` is `S.Unimodular`.
The manifold is exactly `(SmoothAtlas.presentation S hdet).manifold`, with
literal `S.Point`, inherited topology, and native tangent spaces.

- `nondegenerate_omega`: the kernel of `GlobalTwoForm.omega S hdet` is trivial
  at every actual point. The proof restricts that same form to the chart
  indexed by `p.zeroSet`, using full source membership and the accepted
  boundary kernel calculation.
- `isSymplecticOn_omega`: the pinned FsFltz `IsSymplecticOn` on `Set.univ`,
  combining the proved smoothness, actual exterior derivative vanishing, and
  the unconditional pointwise nondegeneracy above.
- `exists_symplectic_form`: an explicit existence theorem whose witness is
  exactly `GlobalTwoForm.omega S hdet`, with witness equality in the statement.

The combined consumer imports the accepted root and the new module. It checks
smoothness, closedness, kernel triviality, native nondegeneracy and symplecticity,
the exact local restriction and original-coordinate torus normalization, and
an inhabited determinant-one seed of dimension zero. The normalization retains
the factor `1/2`, full matrix `B`, wedge order, and complex imaginary part.

The accepted B consumer supplies an actual A2 boundary point with both node
coordinates zero. Its unchanged source and all per-root audit results are
carried in the delivery evidence. Verification consumers are standalone files,
outside the pinned Lake library's module target set; their definitions are not
duplicated here. The new kernel theorem applies to every such point.

The audit uses the native `Lean.collectAxioms` separately for each selected
root, without a replacement collector. It selects all declarations by defining
module for the new composition, Global, B, and NodeTwoForm, including private
and generated declarations; it also selects B namespace roots, every current
consumer declaration, and nine explicit attribution-sensitive supplements.
The full inherited manifests and exact duplicate-result reconciliation remain
part of the source-bound delivery artifact, including earlier standalone
consumer roots. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

No accepted file, root import, audit, dependency pin, PDF, or upstream source is
changed. The accepted Global tree and only the two accepted B additions form
the baseline. The official private publication is based on the immutable Global
commit, independently of stale local protected Git metadata.

The primitive, complete native Liouville flow, and full same-flow skeleton
remain open. No `GeometryTarget` witness or primitive witness is asserted.
