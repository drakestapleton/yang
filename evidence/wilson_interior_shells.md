# Two consecutive interior exchanges at separation four

**Both interior shells can be placed, but neither appreciably attenuated the product on the measured SU(2) chains at β = 2.3 or 4.** Each shell attains the minimum of 2,050 split plaquettes for whole-slice separation in this frame. Even the largest measured loss at those couplings was below `10⁻²¹²⁴` of its incoming weight. That is a statistic of these chains, not an upper bound on the equilibrium loss. At β = 0.1, by contrast, the two successive losses together removed 6.96% of the source weight on the hot start and 3.77% on the cold start.

| β | Start | log₁₀ first interior loss fraction | log₁₀ second interior loss fraction |
|---:|---|---:|---:|
| 0.1 | hot | −1.24 | −1.88 |
| 0.1 | cold | −1.51 | −2.16 |
| 2.3 | hot | −2124.72 | −2181.39 |
| 2.3 | cold | −2237.40 | −2256.09 |
| 4 | hot | −4398.75 | −4449.79 |
| 4 | cold | −4030.72 | −4081.89 |

The small losses come from large positive exchange fields *before* applying the hyperbolic tangent, not from an inability to resolve a tiny difference from one. At β = 2.3 and 4, the largest contributing pair supplied at least 70% of each loss numerator. A sharp lower bound on boundary size is not a lower bound on the exchange field: it does not rule out cancellations or rare, low-cost pairs. Nor do two radii at one lattice spacing determine a physical rate. A narrower next question is whether excluding only a **local neighborhood of each observed loop**, rather than its entire time slice, allows successive low-cost exchanges as separation grows.

## What changes from the side-six experiment?

The [earlier minimum cut](wilson_middle_cut.md) could surround one endpoint. Here the two spatial plaquettes sit at times 0 and 4 on a periodic `8⁴` lattice. The middle masks separate **every free spatial link** on one endpoint time slice from its parallel copy on the other. They exchange links based within cyclic time distance one or two of time zero, respectively. Neither middle boundary has a face incident to time 0 or time 4. The two endpoint masks still exchange only the free links of the observed plaquettes. Links pinned by the same first-nonzero-coordinate tree as before are ignored throughout. No Wilson action or sampling rule changes.

The [path certificate](wilson_interior_geometry.md) concerns the **number of split faces**, not their Wilson action. The [Lean proof record](lean_wilson_path_packing.txt) separates the general counting lemma from its finite lattice inputs. Pairwise disjoint effective boundaries and opposite endpoint labels are the hypotheses of the previously verified [signed covariance identity](../proofs/WilsonReplicaFreeShell.lean). On scheduled pairs the probe independently recomputes all sixteen combined exchanges, including the full action shifts, the endpoint signs and the orbit-weighted signed estimator.

## What is measured?

On each pair let `A`, `B`, `C` be the absolute hyperbolic tangents of the source, radius-one and radius-two exchange fields. Each field is half the joint log-weight before exchange minus half the joint log-weight afterward. The two reported loss fractions are

```
x = Σ A(1−B) / Σ A
y = Σ AB(1−C) / Σ AB .
```

These are ratios of sums within a single chain. The second denominator includes survival through the first interior shell; the target endpoint factor and the plaquette difference product are part of the signed covariance estimator, not these shell losses. No shell independence is assumed. Together the two middle factors remove the fraction `x + (1−x)y` of the source weight. When a denominator is zero the corresponding fraction is undefined. The reducer evaluates `log(1−|tanh J|) = log 2 − logaddexp(0,2|J|)` and sums weighted losses in log space, even when ordinary binary64 subtraction would report zero. Wolfram Language, `Assuming[And@@Thread[{a,b,c}>=0],{FullSimplify[1-Tanh[b]==2/(1+Exp[2b])],FullSimplify[Tanh[a](1-Tanh[b] Tanh[c])==Tanh[a](1-Tanh[b])+Tanh[a] Tanh[b](1-Tanh[c])]}]` → `{True,True}`.

## Reproduce

CPU, Python 3.14.6, NumPy 2.5.3, Apple arm64. Each invocation uses the existing sampler's hot and cold starts, separately, with two Wilson replicas per chain, 64 warmup sweeps and 64 measured pairs at stride two. Seeds are recorded per row; separate β invocations reuse the same start seeds. Neither independent pairs within a chain nor equilibration are assumed. The boundary choice does not depend on the fields.

```bash
export PYTHONDONTWRITEBYTECODE=1 VECLIB_MAXIMUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
p=scripts/replica_shell_probe.py
for beta in 0.1 2.3 4; do
  python3 "$p" --interior-shells --side 8 --warmup 64 --samples 64 --beta "$beta" > "$beta.tsv"
done
python3 scripts/summarize_middle_cut.py 0.1.tsv 2.3.tsv 4.tsv
```

Raw SU(2) pairs: [β = 0.1](wilson_interior_beta01.tsv), [β = 2.3](wilson_interior_beta23.tsv), [β = 4](wilson_interior_beta4.tsv). The reducer also reports the range of the signed field and the fraction of the loss numerator carried by its largest contributing pair.
