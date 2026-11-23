# Protecting local neighborhoods instead of whole time slices

**Local protection greatly increased measured attenuation relative to whole slices. It did not produce a minimum-area surface in the middle of the interval.** With the narrow protection the two optimal boundaries surround the two endpoints. At β = 2.3 and 4 the largest observed joint loss from that pair was about `3.72 × 10⁻²⁰` and `1.85 × 10⁻³⁴`, respectively. Widening the neighborhoods gave still smaller losses. By contrast, at β = 0.1 the narrow pair removed 90.57% (hot) and 91.96% (cold) of the incoming weight.

Joint loss is the fraction of the source weight removed by both middle factors together. The table reports its **base-ten logarithm**; closer to zero means greater loss. Each row uses the same 64 measured replica pairs for all three columns.

| β | Start | Narrow local | Wide local | Whole slices |
|---:|---|---:|---:|---:|
| 0.1 | hot | −0.043 | −0.113 | −1.157 |
| 0.1 | cold | −0.036 | −0.180 | −1.424 |
| 2.3 | hot | −27.46 | −146.55 | −2124.72 |
| 2.3 | cold | −19.43 | −134.78 | −2237.40 |
| 4 | hot | −42.05 | −288.11 | −4398.75 |
| 4 | cold | −33.73 | −221.25 | −4030.72 |

At the two higher couplings, **each** measured narrow stage had at least 78% of its loss numerator supplied by one pair. All its sampled middle fields were positive: these absolute-factor losses do not demonstrate sign cancellation. They are finite-chain diagnostics, not bounds on the equilibrium ensemble. A distinct next test would increase the time separation, require an additional exchange between the two collars, and measure its loss after the preceding factors. Counting the endpoint contributions again would not demonstrate decay with distance.

## Where the optimal cuts went

| Protected region | Free links protected per endpoint | Split faces, first + second | Minimum combined area |
|---|---:|---:|---:|
| Narrow | 14 | 51 + 50 | 101 |
| Wide | 66 | 187 + 186 | 373 |
| Whole endpoint slices, earlier flat pair | all free spatial links on each slice | 2,050 + 2,050 | 4,100 |

For the narrow buffers the smaller mask was **exactly the protected source neighborhood**. The complement of the larger mask, restricted to free links, was **exactly the protected target neighborhood**. Exchanging the larger mask gives the same boundary as exchanging that complement; a simultaneous global exchange only relabels the two replicas. For the wide buffers the selected smaller mask again contained only the source neighborhood, and the complement of the larger mask contained the target neighborhood plus two links. The two unmodified wide collars also attain the same total area. Thus the wide minimum is not unique; the chain results below refer to the solver's fixed choice, not the best loss among tied cuts.

The optimizer returns the least source side on its two threshold layers: the vertices reachable from the source in the final residual graph are contained in every minimum cut, and every optimum geometric labelling extends to a minimum graph cut. Reversing the two protected sets and taking free-link complements in reverse order gives the greatest optimum. The threshold masks at the two extremes differ on **zero** links for narrow protection and on **two links per threshold** for wide protection. In particular no nested optimum can differ from the measured wide geometry on more than those two links at either threshold. This is a finite geometry result, not a bound on their contribution to the Wilson action.

**For the narrow buffers the endpoint geometry is forced, not a tie-breaking artifact.** Even before sorting the two masks, the only undecided links would be the 12,261 in the height-one region (between the two thresholds). A height-one link belongs to exactly one of the unsorted masks. If two such links share a face they must belong to the same mask, or both masks split that face. The executable incidence walk reached all 12,261 from a single link. Hence the assignment is constant on that region. Up to swapping the two masks, reversing their orientations, and ignoring pins, there is no other narrow minimum. This conclusion is about the minimum-area class; it does not exclude more expensive cuts with greater loss.

At side ten and separation five, directly using the two endpoint collars still costs 101 or 373 faces, respectively, with four disjoint boundaries including the endpoints. That is a feasibility check, **not** an optimization or a chain measurement on side ten. Increasing separation need not increase the cost of two fixed endpoint exchanges; it also does not turn them into a sequence of factors through the intervening time interval.

## What was tested

Keep the same `8⁴` periodic lattice, tree, plaquettes at times 0 and 4, and Wilson pairs as the [whole-slice experiment](wilson_interior_shells.md). Change only the protected links. In the free-link graph, two links are neighbors when they share an actual plaquette; pinned links do not transmit a neighborhood label.

- **Narrow:** protect the free support of each observed plaquette and every free link sharing a face with that support.
- **Wide:** first grow the support by one step using only spatial plaquettes on its endpoint slice; then apply the same all-face neighborhood step. Neither protection is an entire slice.

For **both** middle exchanges, require source protection inside and target protection outside. A split requires an inside and an outside free link on the same face. The middle boundaries cannot split the same face. The neighborhood closure also prevents either middle boundary from sharing a split face with a single-plaquette endpoint exchange. These are constraints on the exchange, not conditions imposed on sampled configurations.

The [integral flow certificate](wilson_nested_face_cut.md) minimizes the **sum of the two boundary sizes**. Two nested masks can be encoded by a height on free links: 2 inside both, 1 inside only the larger one, 0 outside both. The prohibition on splitting a face twice is precisely that its free heights have range at most one. [Lean verification](lean_wilson_uncross.txt) addresses why nesting does not increase the minimum: orient both exchanges with source inside, then replace them by their intersection and union. On a face split by at most one original mask, this sorting retains the split count and cannot create a shared split. It keeps both protected regions fixed. This does **not** say sorting preserves individual exchange fields, signed products pointwise, or measured losses. The objective is area, not attenuation; no mask is selected using Wilson fields.

## Measurement and replay

The two families each have four exchanges, ordered local source, smaller middle mask, larger middle mask, local target. The existing pinned signed covariance identity applies to each family separately. At scheduled samples the probe directly recomputes full joint Wilson actions, endpoint signs, and the sixteen-member weighted orbit for **each** family. Its output is a list of exchange fields, not a direct estimate of the physical mass.

Writing `A`, `B`, `C` for the absolute hyperbolic tangents of the source and respective middle fields, the successive loss fractions are `Σ A(1−B)/Σ A` and `Σ AB(1−C)/Σ AB`. Joint loss relative to the source budget is `Σ A[(1−B)+B(1−C)]/Σ A`. We evaluate the losses in log space even when a hyperbolic tangent rounds to one. The second stage starts with the surviving weight for **its own** first stage. The local target appears in the full signed identity but not in these three loss diagnostics. Zero incoming weight gives an undefined fraction.

CPU binary64, Python 3.14.6 and NumPy 2.5.3 on Apple arm64. Sixty-four warmup sweeps followed by 64 measured replica pairs at stride two for each SU(2) hot/cold run at each coupling. One invocation per β as in the earlier experiment; the comparator checks all chain/sample identifiers, both endpoint fields and both endpoint face counts against the archived whole-slice rows. These finite chains do not supply independent equilibrium samples or a continuum trajectory.

```bash
export PYTHONDONTWRITEBYTECODE=1 VECLIB_MAXIMUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 scripts/nested_face_cut.py
python3 scripts/local_neighborhood.py
for beta in 0.1 2.3 4; do
  python3 scripts/replica_shell_probe.py --local-neighborhoods --side 8 --warmup 64 --samples 64 --beta "$beta" > "$beta.tsv"
  case "$beta" in 0.1) s=01;; 2.3) s=23;; 4) s=4;; esac
  python3 scripts/compare_local_neighborhoods.py "$beta.tsv" "evidence/wilson_interior_beta$s.tsv"
done
python3 scripts/summarize_middle_cut.py 0.1.tsv 2.3.tsv 4.tsv
```

Local raw data: [β = 0.1](wilson_local_beta01.tsv), [β = 2.3](wilson_local_beta23.tsv), [β = 4](wilson_local_beta4.tsv). The per-stage reducer reports signed-field ranges, base-ten log losses, and the share of the loss numerator from the single largest contributing pair.
