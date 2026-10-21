# Simultaneous primitive scalar localization

This delivery proves the scalar shrinking step of Lemma 2.4, manuscript
`references/acyclic_cluster_HMS.pdf`, pp. 9–11, especially (2.5)–(2.8).
It does not construct H, decompose the full primitive, discard residual terms,
prove primitive extension, completeness, or the full skeleton theorem.

## Inputs and ownership

The immutable parent is scalar commit
`1e5b37662fb2fa65c83f6522e14b97097351bae6`, tree
`aacf57f33738756ad956989583e478a86243c909`, with all 55 entries preserved.
The three exact `DominanceCutoff` module/consumer/interface files are borrowed
from `46af4784abd32701eb42cce5316fbd108484efee`. The only authored files are
this interface, `ClusterSkeleton/PrimitiveLocalization.lean`, and
`verification/PrimitiveLocalizationConsumer.lean`.
Root/successor62 owns shared integration. Retained node-cancellation files are
preserved locally; they are neither imported nor part of this publication.

## Mathematical contract

All points have type `S.Point`: the literal complex exchange-equation subtype
with its inherited topology. Frozen coordinates remain nonzero variables.
`rowLog` sums over **all** `Fin d`, using the full integer matrix row.
`angle` is the principal logarithm imaginary part of `-exchangeCharacter`;
`nodeLog` uses the accepted raw normalization `b_i / Q_i`. The angular cutoff
is the accepted periodic function, so this representative imposes no new
coordinate convention. No later symplectic coordinate change is used.

`neighborhood ε κ δ p` is the interior of an explicit finite intersection:

- the accepted dominance norm inequalities for every zero vertex;
- the actual independent chart locus selected by `p.zeroSet`;
- the slit-plane node domain, strict bounds `|Re Log| < 1` and
  `|Im Log| < angularRadius δ / 2`, and
  `norm(a_i) < exp(-radialLength ε κ - 2*ε)` for every zero index.

`region_mem_nhds` proves that this intersection is a neighborhood of p, using
continuity of the actual coordinates and normalized partners, the proved
nonvanishing of Q_i, the actual exchange equations, and finite filter
intersections. Hence its interior is open and contains p. No separation,
plateau, nonempty zero-set, or neighborhood witness is assumed.

`node_bridges` proves on this single neighborhood that Q_i is nonzero,
`-q_i = 1-a_i*(b_i/Q_i)`, both accepted node-domain and slit-plane membership,
and the angle identity. Its real-part bridge on the torus is proved from the
full Laurent product and logarithms of norms, including frozen indices.

For ε > 0, κ ≥ 2ε+1, and δ > 0, `plateaus` proves simultaneously on the torus
part dominance = 1, rho = 1, vartheta(T_i) = T_i, and radial(A_i) = A_i+κ.
The mission range 0 < δ < π is included. The proof permits the stronger δ > 0
range because the accepted angular radius is already capped by π/4.
`adjacent_dominance_zero` treats every mutable neighbor of any zero index.

`correction` is exactly one literal radial*dominance*rho*angular factor;
`affineCorrection` is `(A_i+κ)*Im(nodeLog_i)`. Their equality is established
on the torus part and then as native eventual equality at each such point.
`correction_mfderiv_eq` transports that germ equality to the actual Mathlib
manifold differential for `SmoothAtlas.charts S hdet`. The adjacent correction
is locally zero and has zero native differential. No equality involving the
radial affine tail is asserted at a zero coordinate itself.

## Consumers and verification

The consumer packages one open U for all indices and all cutoff/logarithm
equalities; it evaluates native differentials on arbitrary tangent vectors
simultaneously. It includes an actual A2 boundary point, proves it is outside
the torus and has zero set {0}, and uses accepted density to establish a
nonempty torus part of its neighborhood. It covers empty zero sets in every
dimension and an actual determinant-one all-frozen seed with arbitrary two
nonzero complex coordinates. General simultaneous zero sets are handled by
the universal finite-index statements without selecting a distinguished zero.

Managed module and consumer receipts and the full theorem inventory are in
the source-bound delivery artifact. The consumer uses unmodified native
`Lean.collectAxioms` for every selected declaration of all three combined
modules, all local consumer declarations, and nine mandatory attribution
supplements. It realizes the new definition equations explicitly. Private
and generated names are selected by defining module and namespace as well.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Complete inherited per-root evidence is carried with exact overlapping
name/result checks and unchanged source, import, dependency and checker
identities. The live audit and unadopted optimization candidate are untouched.
Independent mathematical/PDF/native-calculus acceptance is separate from
compilation and remains the maintainer’s decision.
