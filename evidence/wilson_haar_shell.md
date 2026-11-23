# How much of the boundary gauge orbit cancels?

Condition on one pair of **unframed** Wilson configurations. Put independent normalized Haar gauges on the two outer top sheets and the identity everywhere else. This leaves the inner exchange field unchanged. In the notation of the [vertex experiment](wilson_vertex_shell.md), write the outer field as `J=C+X`, with `X` the sum of the two checkerboard bilinear forms. A simultaneous center flip on one parity class sends `X` to `−X` and preserves its Haar distribution. The center `C` need not equal the field at the identity gauge.

**The sign-reversing gauges are accessible, but carry very little Haar weight on the measured SU(2) canyon chains.** No negative field appeared in the direct draws at β = 2.3 or 4. More importantly, even the analytic ceiling on the preceding-weighted Haar loss fraction is below `3.2 × 10⁻⁶⁹` at β = 2.3 and `8.0 × 10⁻⁸³` at β = 4 on both starts. These are binary64 evaluations for these recorded pairs, **not** upper confidence bounds on an equilibrium Wilson ensemble. At β = 0.1 negative fields were common and the direct loss fraction was about 0.45–0.47.

Each canyon row covers 256 Wilson pairs; each control row covers 64. “Negative” counts unweighted original draws only. The last four columns are base-ten logarithms of chain-weighted fractions, rounded for display. The floor and ceilings bound the exact normalized Haar quantity in real arithmetic; the last column is a finite-draw estimate, not a bound.

| Group | β | Start | Negative / draws | Loss floor | Negative-mass ceiling | Loss ceiling | Draw loss |
|---|---:|---|---:|---:|---:|---:|---:|
| SU(2) | 2.3 | hot | 0 / 32768 | −445.04 | −69.15 | −68.85 | −397.60 |
| SU(2) | 2.3 | cold | 0 / 32768 | −431.28 | −68.80 | −68.50 | −381.77 |
| SU(2) | 4 | hot | 0 / 32768 | −1042.65 | −82.82 | −82.52 | −926.57 |
| SU(2) | 4 | cold | 0 / 32768 | −1037.35 | −82.40 | −82.10 | −947.72 |
| U(1) | 2.3 | hot | 0 / 32768 | −662.71 | −47.30 | −47.00 | −567.85 |
| U(1) | 2.3 | cold | 0 / 32768 | −663.48 | −43.66 | −43.36 | −572.60 |
| U(1) | 4 | hot | 0 / 32768 | −1219.94 | −45.55 | −45.25 | −1047.71 |
| U(1) | 4 | cold | 0 / 32768 | −1234.96 | −45.87 | −45.57 | −1049.08 |
| SU(2) | 0.1 | hot | 1688 / 8192 | −0.42 | −0.28 | −0.16 | −0.33 |
| SU(2) | 0.1 | cold | 1376 / 8192 | −0.45 | −0.32 | −0.15 | −0.35 |

The [Lean theorem](../proofs/WilsonReplicaHaar.lean) proves that this normalized boundary average of the full signed slab product preserves the finite-volume SU(2) plaquette covariance identity. It does not prove the determinant estimate or the numerical table. [Lean verification](lean_wilson_haar_shell.txt) · [SU(2) pairs](wilson_haar_su2.tsv) · [U(1) pairs](wilson_haar_u1.tsv) · [control pairs](wilson_haar_beta01.tsv).

## Weight, not just reachability

The normalized signed outer factor is `m=E_h tanh(C+X)`; the per-pair loss is `L=1−|m|`. This is not the absolute factor at an optimized gauge. If `a=|tanh J_inner|`, the reported loss fraction on a chain is `Σ aL / Σ a`. The denominator and numerator refer to the *same pairs*. The negative-side probability is `Pr_h(J<0)`, not the probability of finding a sign change in a search. These are properties of a particular gauge law and a particular exchange mask; they are not upper bounds on the true Wilson covariance loss for other constructions.

For paired `±X` the signed mean is `sinh(2C)/(cosh(2C)+cosh(2X))`. Hence `m` has the sign of `C` (zero at zero), and `|m| ≤ tanh |C|`. This gives the floor `L ≥ 2/(1+exp(2|C|))`. It also removes the bias from taking an absolute value of a noisy signed estimate: average `1−sign(C) tanh(C±X)` directly, using the logistic form in log space. Antithetic partners count toward that average but **not** as additional independent draws. The analytic sign and loss ceilings use the [Haar moment bound](wilson_haar_bound.md), not extrapolation from a histogram.

Symbolic checks (Wolfram Language, real `c,x`):

```wl
FullSimplify[(Tanh[c+x]+Tanh[c-x])/2 == Sinh[2c]/(Cosh[2c]+Cosh[2x]), Element[{c,x},Reals]] (* True *)
FullSimplify[Tanh[c]-Sinh[2c]/(Cosh[2c]+Cosh[2x]) == Tanh[c](Cosh[2x]-1)/(Cosh[2c]+Cosh[2x]), Element[{c,x},Reals]] (* True *)
FullSimplify[{1-Tanh[x]==2/(1+Exp[2x]),1+Tanh[x]==2/(1+Exp[-2x])},Element[x,Reals]] (* {True,True} *)
```

### Why choosing another fixed distribution is not automatically better

At the level of the **exact Wilson ensemble**, full subgroup Haar averaging minimizes the averaged absolute bound among all configuration-independent distributions on that subgroup. To see this, write `Aν Q(z)=∫ Q(gz) dν(g)`. For normalized Haar `H`, the substitution `h ↦ gh` gives `A_H Aν Q = A_H Q`. Therefore `|A_H Q| ≤ A_H |Aν Q|`. Multiply by any nonnegative subgroup-invariant weight and integrate against the invariant replica law: the right side integrates to the weighted mean of `|Aν Q|`. This applies both to the invariant endpoint weight and, for the two masks here, to the preceding inner factor. The bounded continuous observables make the exchanges of integrals valid.

This comparison is **not pairwise**: a fixed distribution might perform better on a particular pair. A limit on the Haar loss for a finite chain is not an ensemble bound. But if the effect persists in the Wilson ensemble, retuning the weights on the same independent rotations cannot beat full Haar there. Changing the exchange mask or coupling would be a genuinely different test.

## Reproduction

```sh
export VECLIB_MAXIMUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
p=scripts/replica_shell_probe.py
python3 "$p" --haar-shell --samples 256 --warmup 256 --beta 2.3 4 > su2.tsv
python3 "$p" --haar-shell --samples 256 --warmup 256 --beta 2.3 4 --group U1 > u1.tsv
python3 "$p" --haar-shell --samples 64 --warmup 64 --beta 0.1 > beta01.tsv
for g in su2 u1 beta01; do
  python3 scripts/summarize_haar_shell.py "$g.tsv" "evidence/wilson_vertex_$g.tsv"
done
```

The sampler uses 128 normalized-Gaussian product draws per pair, on the unit quaternion sphere for SU(2) and the unit circle for U(1). Its auxiliary RNG never advances the Wilson chains. The reducer checks the chain identifiers and both identity-gauge fields against the archived pairs. Hot and cold starts are separate correlated runs, not independent samples from a verified equilibrium law. The draw-based loss can be unrepresentative when rare negative draws dominate it; only the analytic bounds constrain the exact Haar average for these pairs. The numerical evaluations are binary64, not outward-rounded interval certificates.
