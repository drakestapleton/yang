# What does a smaller middle exchange surface buy?

**Smaller did not mean unsaturated.** On paired SU(2) runs at β = 2.3 and 4, a minimum-face cut increased the weighted loss by many orders of magnitude relative to a time slab. But even its largest measured loss fraction was only about `5.0 × 10⁻²²`. One pair supplied more than 95% of that cut's loss numerator in each of the four runs. These are observations on finite chains, not upper bounds on equilibrium loss. At β = 0.1 the same comparison gave 68–69% loss for the cut and 12–14% for the slab.

| Group | β | Start | Pairs | log₁₀ weighted cut loss | log₁₀ weighted slab loss | Largest cut share |
|---|---:|---|---:|---:|---:|---:|
| SU(2) | 2.3 | hot | 128 | −21.30 | −881.98 | 0.9543 |
| SU(2) | 2.3 | cold | 128 | −23.31 | −882.38 | 0.9999 |
| SU(2) | 4 | hot | 128 | −35.08 | −1661.10 | 0.9961 |
| SU(2) | 4 | cold | 128 | −34.39 | −1534.32 | 0.9561 |
| U(1) | 2.3 | hot | 128 | −6.80 | −830.67 | 1.0000 |
| U(1) | 2.3 | cold | 128 | −5.77 | −568.87 | 0.9997 |
| U(1) | 4 | hot | 128 | −10.83 | −1472.90 | 0.9671 |
| U(1) | 4 | cold | 128 | −8.61 | −665.69 | 0.5136 |
| SU(2) | 0.1 | hot | 64 | −0.17 | −0.92 | 0.0609 |
| SU(2) | 0.1 | cold | 64 | −0.16 | −0.86 | 0.0671 |

The table is rounded; the reducer below also reports the range of the signed field. The direction of improvement is shared by compact U(1), so the geometry comparison does not isolate a non-Abelian effect. It does not test whether a sequence of middle masks pays a loss proportional to physical spacing.

Change the links exchanged, not the Wilson action or the distribution of gauges. The lattice is a periodic `6⁴` torus. The observables are elementary spatial 0–1 plaquette traces at the spatial origin and times 0 and 3. For each replica, fix a spanning tree before measurement: from each nonroot vertex, step backwards in its first nonzero coordinate. The coordinate sum decreases until the origin, so the chosen links form a tree. Parallel transport sets those links to the identity; no configurations are rejected. The same projected replica pair is used for both mask families.

**What is minimized.** Keep the source and target endpoint masks fixed, each exchanging just the unpinned links of its observed plaquette. A middle mask must contain the full free source support, avoid the free target support and split no face already split by either endpoint. A face is split only if it has free links on both sides of the mask: the replicas agree exactly on a pinned link, so exchanging it does nothing. [The integer flow and cut](wilson_face_cut.md) minimize the number of split plaquettes over this entire class. One minimizing mask is selected without looking at any Wilson pair. This is not a minimization over fields, trees, or estimated losses. Compare it with the mask exchanging every free link based at times 5, 0 or 1, with exactly the same endpoint factors. “Middle” means the third distinct surface between the endpoint masks in this identity, not necessarily a flat sheet halfway between the plaquettes.

**The minimum is unique on free links, and it hugs the target.** The time slab splits 866 effective faces. The minimum splits 50. Each endpoint contains just one free link and splits five faces. All 14 free links on the target's forced neighborhood must be excluded. The returned source side contains *every other free link*, as checked in the probe. Why does that establish uniqueness? In a maximum-flow residual graph, every vertex reachable from the source belongs to the source side of every minimum cut: a minimum cut has no outgoing positive residual arc. The solver returns precisely that reachable set. Every admissible minimizing mask extends to a network minimum cut, so it contains the returned mask; the forced exclusions prevent it from containing anything larger. Pin labels are irrelevant. Swapping the complement is equivalent up to interchanging the replicas globally, so the optimal boundary is that of a small patch around the target, not a new sheet filling the intervening time slice.

**Three separating factors are the most possible here.** Follow the free spatial link in the source plaquette forward in time to its parallel copy at the target. Consecutive links lie on the same temporal plaquette; none of these four parallel links is pinned. Any endpoint-separating mask must change label somewhere on this path and hence split one of its three plaquettes. Pairwise disjoint split-face sets allow at most three such masks. Both families attain that count. This is a path argument for the stated frame and separation, not a bound on the size of any factor.

**What is measured.** Write `J = (log w − log w_swapped)/2` for each individual mask; `w` is the joint Boltzmann weight. If `A=|tanh J_source|`, the fraction lost on adding the middle factor is

```
sum_pairs A (1 − |tanh J_middle|) / sum_pairs A .
```

This is a ratio of sums, not an equally weighted average of per-pair log-losses. The last target factor still appears in the full signed identity. It is not part of the preceding weight above. The reducer evaluates the numerator with log-sum-exp, without subtracting near-unit floating-point numbers. “Largest share” is the fraction of that numerator carried by its largest contributing pair; a large value warns against extrapolation from a finite chain. All chain estimates use binary64. Hot and cold starts are separate chains; neither independent samples within a chain nor equilibrium are assumed.

**A deterministic bound, separate from the data.** A mixed face contributes at most `2|β|` to `|J|`: its defect is `β/2` times a signed sum of four normalized real traces in `[−1,1]`. Unmixed faces contribute zero. With `n` mixed faces this gives `1−|tanh J| ≥ 2/(1+exp(4|β|n))`, even before sampling. The estimate holds on this geometry but can be very small; it does not establish a rate along a continuum trajectory. Wolfram Language cross-checks (real variables): `Maximize[{Abs[(a+b-c-d)/2],And@@Thread[-1<={a,b,c,d}],And@@Thread[{a,b,c,d}<=1]},{a,b,c,d}][[1]]` → `2`; `FullSimplify[1-Tanh[a]==2/(1+Exp[2a]),a>=0]` → `True`.

## Reproduction

Run from the project root with Python 3 and NumPy. Row identifiers and the two endpoint fields are shared by the two middle geometries. No auxiliary sampling or optimization advances the Wilson chain. The compact U(1) chain uses the same bare parameters, not matched physical scales.

```bash
export PYTHONDONTWRITEBYTECODE=1 VECLIB_MAXIMUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 scripts/face_min_cut.py
p=scripts/replica_shell_probe.py
python3 "$p" --middle-cut --side 6 --samples 128 --warmup 128 --beta 2.3 4 > su2.tsv
python3 "$p" --middle-cut --side 6 --samples 128 --warmup 128 --beta 2.3 4 --group U1 > u1.tsv
python3 "$p" --middle-cut --side 6 --samples 64 --warmup 64 --beta 0.1 > beta01.tsv
python3 scripts/summarize_middle_cut.py su2.tsv u1.tsv beta01.tsv
```

At scheduled samples both eight-element exchange orbits are recomputed with all plaquettes of the lattice. The checks compare the full action shift with the sum of the individual fields, the sign of the endpoint difference product with the parity of the chosen exchanges, and the orbit-weighted estimator with the predicted product. Projected traces are compared to the original plaquette traces, including those on wrapped faces. [SU(2) pairs](wilson_middle_su2.tsv) · [U(1) pairs](wilson_middle_u1.tsv) · [low-β control](wilson_middle_beta01.tsv) · [Lean proof and verification scope](lean_wilson_free_shell.txt).
