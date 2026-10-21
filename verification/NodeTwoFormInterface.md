# Node two-form interface

Mathematical base: accepted private commit `2718fde65076eb95f7d1b4f6016e5faf42046ee9`, publication `fb8e62b1-813b-4273-88ee-41e58f678549`. Objective revision 4: roadmap commit `4c28a63587f7e2778d84e03b3e2bca3f0121137a`. The publication receipt accompanying this file supplies the immutable delivery commit and source-bound managed checks. This file does not assert maintainer acceptance.

## Exact objects and domain

All names below are in `ClusterSkeleton.NodeTwoForm`. Let `S : Seed d`, `hdet : S.Unimodular`, `I : Finset (Fin d)`, and `hI : S.Independent I`. The manifold is exactly `(SmoothAtlas.presentation S hdet).manifold`, on `S.Point` with its inherited topology. No smooth presentation or extension witness is supplied as a premise.

Write `J = {j // j ∉ I}`, `K = IndependentRowBasisIndex S I = {i // i ∈ I} ⊕ IndependentNodeChart.Complement S I`, and `V = IndependentNodeChart.Vector S I`. A point of V is `x=((u_i,v_i),w)`. The domain is exactly the accepted `IndependentNodeChart.domain S I`: every `u_i*v_i ≠ 1` and every `w_k ≠ 0`. Neither node axis is removed. Put `z = rawParameters S I x`, so `z(inl i)=q_i=u_i*v_i-1`, `z(inr k)=w_k`.

`T = independentRowInverseMatrix S I hdet hI` has rows indexed by J and columns indexed by K. The accepted inverse chart is `a_j = ∏ k, z_k ^ T_jk`. `row_inverse` proves `∑ j, B_ij*T_jk = δ_(inl i),k`, hence **RT=[Id,0]** with these exact signs. The residual integer matrix is

`C = residualMatrix S I hdet hI = T.transpose * B[J,J] * T`.

Every coefficient is retained. In particular the q–q and q–w blocks generally remain present. No new choice of symplectic coordinates or diagonal residual matrix is assumed.

## Form and native tangent maps

`complexForm S I hdet hI x : V [⋀^Fin 2]→L[ℂ] ℂ` is

`Σ i, q_i⁻¹ (du_i ∧ dv_i) + (1/2) Σ k,l, C_kl (dlog z_k ∧ dlog z_l)`.

Here wedge has evaluation `a(v₀)*b(v₁)-a(v₁)*b(v₀)` with no additional factor. `logParameter` is `(v_i du_i + u_i dv_i)/q_i` on `inl i`, and `dw_k/w_k` on `inr k`. `hasFDerivAt_parameter` and `hasFDerivAt_rawOutside` identify these expressions with native derivatives. `residualMatrix_cast`, `matrixValue_congruence`, and `complexForm_apply` verify the basis transformation and its full outside-coordinate remainder.

`realForm` first restricts this complex continuous alternating map to real scalars and then applies `Complex.imCLM`. `contDiffAt_complexForm` proves native complex smoothness throughout the domain; `contDiffOn_realForm` proves native real smoothness of the form-valued coefficient map on that entire domain.

For `p : S.Point`, let `x = SmoothAtlas.rawChart S hdet I hI p`. The map

`tangentMap S I hdet hI p : (SmoothAtlas.presentation S hdet).manifold.Tangent p →L[ℝ] V`

is precisely `mfderiv 𝓘(ℝ,Model (2*d)) 𝓘(ℝ,V) (SmoothAtlas.rawChart S hdet I hI) p`. When `hp : p ∈ candidateChartLocus S I`, `tangentEquiv ... p hp` is a continuous real linear equivalence with exactly that underlying map. Its injectivity comes from the actual chart inverse and accepted immersion; its dimension equality comes from the accepted integral basis. The model-space tangent fiber is not silently identified with V.

`localForm S I hdet hI` pulls back `realForm x` by `tangentMap p`. Its intended geometric domain is `candidateChartLocus S I`; total values outside that set are immaterial. The local source and target are open by accepted theorems. `chart_smooth` and `originalLog_tangentMap` check smoothness and the native chain rule on the source.

`localForm_torus` proves, on the entire initial torus,

`evalTwo (localForm S I hdet hI) p a b = (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p a b`.

Thus this is the specified `Im ((1/2) Σ i,j B_ij dlog a_i ∧ dlog a_j)`, with the same B, normalization, manifold and native derivatives. Neither the restriction nor the extension formula is assumed.

## Boundary interface for line B

At `u_i=0` for every i, `q_i=-1` and `dlog(q_i)(t)=-v_i*t.u_i`. Define `L_x(t)=boundaryLog S I x t`, indexed by the same K as C. `complexForm_boundary` proves

`Ω_x(a,b) = -Σ i (a.u_i*b.v_i - b.u_i*a.v_i) + matrixValue C (L_x(a)) (L_x(b))`,

where `matrixValue` includes the factor one half and antisymmetrization. Its q entries are `-v_i*t.u_i`, and its w entries are `t.w_k/w_k`. `realForm_boundary` takes the imaginary part. `localForm_boundary` states exactly the same formula on the actual manifold tangent fiber, using `tangentMap` on both arguments. For geometric use, keep `p ∈ candidateChartLocus S I`; `tangentEquiv` then permits arbitrary V inputs without assuming a tangent identification.

`verification/NodeTwoFormConsumer.lean` specializes to `I=p.zeroSet`, using the accepted independence theorem and proving the point belongs to that chart. It also checks an inhabited `d=0` seed and the empty-node case. No positive dimension, nonempty independent set, nonzero v, or boundary nondegeneracy hypothesis is introduced.

## Open obligations and verification boundary

`LocalCompatibility` and `GlobalClosedExtension` are definitions of propositions, **not proved theorems and not assumptions used in the construction**. Compatibility of the local pullbacks on overlaps, construction and native smoothness of a globally glued form, and global closedness remain open. The accepted uniqueness/density machinery is available for future gluing. Proving closedness via density additionally needs smoothness/continuity of the actual exterior derivative and its vanishing on the torus; those steps are not claimed here. Density never supplies boundary nondegeneracy.

Boundary nondegeneracy belongs to line B. Global symplectic existence, a primitive, complete Liouville flow, and the full same-flow skeleton equality remain open. This delivery does not change root imports, the accepted audit, accepted mathematical sources, dependency pins, or source PDFs.

The consumer audits the entire defining module (including private/generated declarations), all current consumer declarations, and all named new namespace roots. Each root is passed to native `Lean.collectAxioms`; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The immutable evidence artifact records the exact declaration manifest, per-root transitive axiom sets, source hashes, managed receipts, publication, and preservation of the accepted old tree bytes and modes. The unchanged global audit is not rerun.
