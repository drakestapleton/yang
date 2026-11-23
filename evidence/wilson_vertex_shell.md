# Shared vertex gauges on the outer Wilson slab

A site-dependent gauge acts on the second replica by `V(x,i) ↦ h(x) V(x,i) h(x+i)⁻¹`. A link has one transformed value even when several plaquettes use it. This is not a choice of independent conjugators for plaquettes or for three-plaquette patches. Nonconstant transformations can change the mixed-replica exchange field in **both** SU(2) and compact U(1); the earlier U(1) identity control concerned *constant* conjugation only.

## Result on the matched `4⁴` runs

**Shared-link compatibility permits sign reversal on most sampled SU(2) pairs. The tested fixed average does not find it at either canyon coupling.** The table counts pairs, not configurations pooled across couplings. “Both signs” requires two feasible values outside `±1e−8`; “positive lower” uses the margin-adjusted binary64 dual. Otherwise the search is inconclusive. “Fixed both” uses only the four sample-independent fields. The last column is the base-ten logarithm of the measured inner-weighted loss fraction for those fields.

| Group | β | Start | Pairs | Both signs | Positive lower | Inconclusive | Fixed both | log₁₀ loss fraction |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| SU(2) | 2.3 | hot | 256 | 256 | 0 | 0 | 0 | −404.37 |
| SU(2) | 2.3 | cold | 256 | 256 | 0 | 0 | 0 | −415.44 |
| SU(2) | 4 | hot | 256 | 254 | 2 | 0 | 0 | −981.01 |
| SU(2) | 4 | cold | 256 | 256 | 0 | 0 | 0 | −987.88 |
| U(1) | 2.3 | hot | 256 | 0 | 254 | 2 | 0 | −597.21 |
| U(1) | 2.3 | cold | 256 | 212 | 44 | 0 | 0 | −593.76 |
| U(1) | 4 | hot | 256 | 4 | 252 | 0 | 0 | −1149.84 |
| U(1) | 4 | cold | 256 | 3 | 253 | 0 | 0 | −882.52 |
| SU(2) | 0.1 | hot | 64 | 63 | 0 | 1 | 30 | −0.31 |
| SU(2) | 0.1 | cold | 64 | 64 | 0 | 0 | 23 | −0.37 |

The canyon cancellation gain was zero in the fixed sample averages, **not** a statement that the loss was literally zero. At β = 0.1 those same four fixed fields produced measurable sign cancellation, contributing 0.15308 (hot) and 0.08251 (cold) of the preceding weight. The U(1) start dependence at β = 2.3 is large: these are finite-run comparisons, not equilibrium probabilities or a non-Abelian criterion.

Next question: how much **gauge-orbit measure** lies on the opposite-sign side, weighted by the preceding shell? A strict feasible reversal persists in a neighborhood by continuity but supplies no useful lower bound on that neighborhood's mass. A normalized integration over the boundary gauges could use favorable configurations to guide quadrature only if the integration weights are retained. No such mass estimate, multi-separation rate or continuum result follows here.

## Which average is a covariance estimator?

Work in the original, unpinned product Wilson law. For **each fixed** vertex field, the transformation preserves that law. The difference product `D=(F(U)−F(V))(G(U)−G(V))` for two plaquette traces is unchanged, because every original closed-loop trace is gauge invariant. Apply the transformation to the entire signed exchange estimator, then average over a finite nonempty list of fields chosen independently of the pair. Its expectation still equals twice the covariance. Taking the absolute value **after** the average gives a bound. A gauge chosen by minimizing the exchange field on the observed pair is *not* a member of such a fixed list by virtue of being a valid gauge transformation. We use that minimization only to ask which signs are attainable.

For each split temporal plaquette, let `b` be the top spatial link, from `x` to `y`, and `p` the three-link path with the same endpoints. In quaternion coordinates the unexchanged trace sum is `p₀·b₀ + p₁·b₁`. The exchanged trace sum is

`p₀·(hₓ b₁ hᵧ⁻¹) + b₀·(hₓ p₁ hᵧ⁻¹)`.

All intermediate vertex gauges cancel. Thus allowing arbitrary vertex gauges on the **top sheets of the outer boundary** explores its full relative vertex-gauge orbit; gauges elsewhere do not enter that field. The inner slab uses disjoint top sheets. With all other vertices set to the identity, the inner field is unchanged. This support argument uses the geometry of these two masks, not an assumption of independence between shell factors.

## Fixed fields and loss accounting

We test four fields: identity, a checkerboard center sign, a spatially varying unit-quaternion pattern (circle-valued for U(1)), and its product with the center sign. The auxiliary pattern seed is separate from the chain RNG. All three nontrivial fields are identity off the outer top sheets. Each nearest spatial neighbor has opposite checkerboard parity, so the sign switch negates every mixed dot product without changing the two original traces. The two pairs of outer fields therefore have the same midpoint before `tanh`.

For `a=|tanh J_inner|` and `t_h=tanh J_outer(h)`, the total loss on this second shell is `a(1−|mean_h t_h|)`. It consists of `a mean_h(1−|t_h|)` plus the cancellation gain `a(mean_h |t_h|−|mean_h t_h|)`. The first term is evaluated in log space via `1−|tanh j|=2 exp(−2|j|)/(1+exp(−2|j|))`; the second uses twice the smaller of the positive and negative means (including zeros). The reported loss fraction is the sum of per-pair losses divided by the sum of preceding weights, **not** the mean of per-pair log losses. The covariance identity includes `D`; the loss diagnostic compares shell factors, not endpoint observables.

## Testing whether *any* shared rotation can reverse the sum

On each outer top sheet, partition the spatial vertices by parity. The formula above is bilinear in the even and odd quaternion coordinates because quaternion multiplication by a fixed element and quaternion conjugation are real-linear. Including `−β/2` in the mixed terms gives `J=C+rᵀBb` per sheet. `C` is the unexchanged crossing action in `β/2` units; each vertex block of `r` and `b` has unit norm. SU(2) uses four real coordinates per vertex and U(1) uses two. See the [symbolic cross-check](wilson_vertex_algebra.txt).

Alternately align each parity class against its local gradient (choose the negative unit gradient; keep the old value at zero). Start at identity and at a fixed generic field, keeping the best feasible result on each sheet. The sheets have no common vertices, so their two winners can be combined. A negative feasible value and a positive value on the same pair establish both signs. Every negative optimization witness is checked by transforming the full lattice and recomputing both complete actions. A positive witness alone establishes nothing about the minimum.

For a lower bound put `q=(r,b)`, `H=[[0,B],[Bᵀ,0]]/2`, and let `N` count vertices on the sheet. For arbitrary block multipliers `λᵥ`, `K=H−diag(λᵥ I)` gives

`C + qᵀHq ≥ C + Σᵥ λᵥ + N λ_min(K)`,

since `qᵀq=N`. Choose `λᵥ=qᵥ·(Hq)ᵥ` at the feasible witness, subtract `128 ε (N d) max(1, |β|, ‖K‖∞)` from the computed eigenvalue (`d` is the block dimension), then add the two sheet bounds. This is a binary64 lower-bound diagnostic with a safety margin, **not** an interval certificate. A bound above the sign tolerance excludes reversal numerically; a lower bound below zero without an opposite-sign witness is unresolved.

## Reproduction

CPU binary64: Python 3.14.6, NumPy 2.5.3, Apple arm64. These commands reuse the previous spectrum run's pair sampler, seeds, warmup and stride. The earlier diagnostic measured **tree-framed** rigid fields. Here the measurements are **unframed**; row identifiers match configurations, not numerical identity fields. Each row is one Markov-chain sample pair, not an independent orientation draw. Keep hot and cold starts separate; no thermalization or autocorrelation correction is implicit.

```sh
export VECLIB_MAXIMUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 scripts/replica_shell_probe.py --vertex-shell --beta 2.3 4 --samples 256 --warmup 256 > su2.tsv
python3 scripts/replica_shell_probe.py --vertex-shell --group U1 --beta 2.3 4 --samples 256 --warmup 256 > u1.tsv
python3 scripts/replica_shell_probe.py --vertex-shell --beta 0.1 --samples 64 --warmup 64 > beta01.tsv
python3 scripts/summarize_vertex_shell.py su2.tsv u1.tsv beta01.tsv
```

[SU(2) pairs](wilson_vertex_su2.tsv) · [compact U(1) pairs](wilson_vertex_u1.tsv) · [low-β SU(2) control](wilson_vertex_beta01.tsv).

The theorem [`plaquette_vertex_slab_covariance`](../proofs/WilsonReplicaVertex.lean) specializes the fixed-field identity and bound to two spatial plaquette traces, for any number of concentric shells up to their cyclic separation. The new module compiled on Spark against the previous pinned bridge oleans (Lean 4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`). All five printed declarations used only `propext`, `Classical.choice`, `Quot.sound`. Dropping nonemptiness with constant observables in the general integral identity left the false goal `False`. The full bridge build recipe is `sh scripts/build_and_run_spark.sh openai_bridge`; only the new module and legacy color module were compiled in this investigation.
