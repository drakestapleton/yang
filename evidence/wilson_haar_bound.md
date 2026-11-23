# Conditional product-Haar ceilings for the outer slab

Contract row 2, base `c73bf92caeb1c1a495edc5207d1f5e8eee603018`; contract SHA256 `e7d2749da6183f3cd684bbb0ed2c178fbb8ae138493afd248a7b77f2c92a5ebe`.

This is a conditional, finite-lattice bound, not an orbit-volume estimate from an optimization witness. Fix the Wilson pair and its real bilinear field

\[
J=C+X,\qquad X=\sum_{s=1}^2 r_s^T B_s b_s.
\]

Every consecutive block of `dim=d` real coordinates in each vector is independently uniform on the unit sphere in ambient dimension `d`. All red and blue blocks on both sheets are independent. For SU(2) this is the unit-quaternion Haar law (`d=4`); for compact U(1) it is the circle Haar law (`d=2`). These are vertex variables, not independent plaquette conjugations. The analytic sign event is strictly `J<0`, including proper treatment of atoms at zero. `C` is the *sum* of the two sheet constants. Conditioning fixes `C,B`; it does not assume Wilson-chain pairs are independent.

## Real-arithmetic derivation

For a uniform sphere vector `u`, rotational invariance and the beta marginal give

\[
\mathbb E(u\cdot v)^{2k}=\|v\|^{2k}\frac{(1/2)_k}{(d/2)_k}
\le \|v\|^{2k}\frac{(2k-1)!!}{d^k}.
\]

The ratio of consecutive sphere moments is `(2k+1)/(d+2k)`, no greater than the Gaussian ratio `(2k+1)/d`; odd moments vanish. Thus `E exp(u·v) <= exp(||v||²/(2d))`. For `d=1` the sphere is the two signs and the same comparison follows from `cosh(a)<=exp(a²/2)`. Multiplying this inequality across independent blocks proves the corresponding vector inequality, even though coordinates *within* a sphere block are dependent.

First integrate the red blocks, then introduce one independent standard Gaussian vector `g_s` per sheet, then integrate blue blocks:

\[
\begin{aligned}
\mathbb E e^{-tX}
&\le \mathbb E_b\exp\bigg[\frac{t^2}{2d}\sum_s\|B_sb_s\|^2\bigg]\\
&=\mathbb E_{b,g}\exp\bigg[\frac{t}{\sqrt d}\sum_s g_s^TB_sb_s\bigg]\\
&\le \mathbb E_g\exp\bigg[\frac{t^2}{2d^2}\sum_s\|B_s^Tg_s\|^2\bigg]\\
&=\prod_{s,k}\left(1-(t\sigma_{sk}/d)^2\right)^{-1/2}.
\end{aligned}
\]

Here `sigma_sk` are all singular values of `B_s`, including multiplicities. Tonelli applies to the nonnegative integrands. The last equality is the Gaussian quadratic integral, finite when `|t| max(sigma)/d < 1`. The same calculation works for rectangular matrices. Consequently

\[
\log\mathbb E e^{-tJ}\le F_C(t):=-tC-\tfrac12\sum_{s,k}\log\left(1-(t\sigma_{sk}/d)^2\right).
\]

For any **positive** admissible `t`, Markov's inequality gives `P(J<0)<=min(1,exp(F_C(t)))`: on `J<0` the nonnegative random variable `exp(-tJ)` exceeds one. The sign in `-tC` is important. `t=0` supplies the trivial bound one. For `C<=0` the implementation returns this trivial sign ceiling, rather than reflecting the event.

For `0<=t<=2`, pointwise on the entire real line,

\[
1-\tanh j=\frac{2}{1+e^{2j}}\le2e^{-tj}.
\]

Indeed `e^{tj}<=1` if `j<=0`, and `e^{tj}<=e^{2j}` if `j>=0`. Therefore

\[
1-|\mathbb E\tanh J|\le\mathbb E(1-\tanh J)\le2\mathbb E e^{-tJ}.
\]

The law of `X` is symmetric: simultaneously negate every red block. Apply the preceding inequality to `J` if `C>=0` and to `-J` otherwise; `|E tanh J|` is unchanged. The loss ceiling thus uses `F_|C|(t)`, with both determinant-domain and `t<=2` restrictions, and is capped at one. This reflection is **not** used for `P(J<0)`. At `C=0`, symmetry makes the actual loss one.

Independence and isotropic covariance `I/d` also give the exact conditional variance

\[
\operatorname{Var}(J)=\sum_s\|B_s\|_F^2/d^2.
\]

All these inequalities are exact mathematics under the specified product law; the Python evaluations below are ordinary binary64.

## Deterministic implementation and interface

```python
from haar_slab_bound import bounds
variance, log_p_upper, log_loss_upper = bounds(constant, B, dim)
```

`scripts/haar_slab_bound.py` accepts a finite real scalar `constant`, two real matrices in `B.shape == (2,nred,nblue)`, and a positive integer `dim` dividing both coordinate axes. Both coordinate axes must be nonempty. The outputs are the variance and **natural logarithms** of the negative-sign probability ceiling and absolute-tanh-loss ceiling. All log ceilings are nonpositive; `-inf` represents an exact zero. No random draws, optimizer witnesses, lattice imports, or chain RNG are involved.

Let `s=max(sigma)/d`, `q_sk=(sigma_sk/max(sigma))²`, `n=sum(q)`, `h=|C|/s`, and `x=t*s`. Convexity in `q` gives

\[
-\log(1-qx^2)\le q[-\log(1-x^2)],\quad 0\le q\le1,
\]

so `F_|C|(t) <= -h*x - n*log(1-x²)/2`. A minimizer of this one-dimensional *upper envelope* is

\[
x_* = \frac{h}{n/2+\operatorname{hypot}(n/2,h)}.
\]

The code uses `x=min(0.99,x_*)`, safely inside the pole, and evaluates the **tighter singular-value determinant sum** there with `log1p`. The loss uses `min(x,2*s)`, so its actual tilt cannot exceed two. A minimizing tilt is not necessary for validity; these choices can only weaken the ceilings compared with a better admissible choice. The envelope supplies a cheap tilt without iterative root solving; retaining the two matrix SVDs gives a tighter ceiling than replacing the whole determinant by the Frobenius/operator envelope. No claim of optimal Chernoff bounds is made.

Zero matrices bypass SVD. For a deterministic `J=C`, the strict sign probability is exactly zero if `C>=0` and one otherwise; the exact loss is evaluated stably as

\[
\log(1-|\tanh C|)=\log2-2|C|-\log(1+e^{-2|C|})
=-|C|-\log\cosh|C|.
\]

The small-offset form uses `cosh(a)=1+2 sinh(a/2)²` to avoid cancellation. This is stronger than the exponential bound and includes `C=0` without special sign tolerances.

Wrong shape, incomplete vertex blocks, non-real or nonfinite inputs, and invalid dimensions raise `ValueError`. A nonzero slab whose singular scale, variance, or normalized offset over/underflows representable binary64 raises `OverflowError`; constant-field log losses outside binary64 also raise it. SVD failure propagates. There is no silent finite fallback. SVD, variance, logs, and reference quadrature are not directed-rounded interval arithmetic: even an output called an upper bound is a floating diagnostic of a real-arithmetic upper bound, **not a certified floating inequality**. Very small nonzero log corrections can round away. The reported variance likewise evaluates the exact formula but is not an interval enclosure.

## Focused deterministic controls

Run the complete file (requires only Python and NumPy):

```sh
OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 OMP_NUM_THREADS=1 \
  python3 -W error scripts/haar_slab_bound.py
```

Executed with Python `3.14.6`, NumPy `2.5.3`, arm64. The self-controls compare:

* Actual U(1) Haar: one nonzero sheet block `B=2 I_2`, `d=2`, `C=19/10`. Then `J=19/10+2 cos(theta)` for a uniform angle. The exact strict sign probability is `acos(19/20)/pi`; the tanh loss is a Wolfram 40-digit integration reference, not an elementary exact formula.
* The full two-sheet, `d=1`, two-block-per-color model `B_1=B_2=I_2`, `C=3`. Its field is three plus four independent signs. Direct finite enumeration has sign probability `1/16`; the exact loss expression is below.
* Positive rescaling of `(C,B)` through small and large amplitudes: sign ceiling invariant and variance scaled quadratically. Reflection changes the sign ceiling to one but preserves the loss ceiling. A small-amplitude case exercises the `t<=2` loss cap; a large-offset case keeps the log loss finite past ordinary exponential underflow.
* `C=0`, `B=0`, positive/negative constant fields, and invalid input shape/dimension/nonfinite/complex cases. Invalid input is checked as refusal, not converted to a vacuous numeric result.

Final raw control output:

```text
2026-11-23T13:05:34Z
OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 OMP_NUM_THREADS=1 python3 -W error scripts/haar_slab_bound.py
U1 circle: var=2 p=0.101082624104 log_p_upper=-0.693759684235 loss=0.286466359744 log_loss_upper=-0.00061250367551
two sheets: var=4 p=0.0625 log_p_upper=-0.930625185867 loss=0.171578366001 log_loss_upper=-0.237478005307
scaling, reflection, t<=2, zero, log-range and invalid-domain controls: PASS
exit=0
3.14.6 2.5.3 arm64
```

The bounds are visibly loose even in small models; they are ceilings, not fitted probabilities. An initial control run exited zero but emitted a warning while *constructing* its nonfinite negative fixture by multiplying zero by infinity. The final fixture directly allocates infinity; the full file then passed with warnings treated as errors. No dispatcher or sampler was changed by this row.

## Retained Wolfram math-check records

Queries and returned results are retained here for fresh-clone audit; each can be replayed as `mcp__wolfram_wolframlanguageevaluator '<query>'`. The separate Alpha command is not mounted; its capability probe was run through the evaluator's `WolframAlpha` function and returned an exact fact. The context tool was called before evaluator use. Each evaluation below exited zero. These symbolic controls check the displayed identities and ingredients, not a formal machine proof of the whole argument.

**Capability probes:**

```wl
Integrate[x^2,{x,0,1}]
(* Out[1]= 1/3 *)
WolframAlpha["sqrt(27)/2",{{"Result",1},"ComputableData"}]
(* Out[1]= Hold[(3*3^(1/2))/2] *)
```

**Sphere moment comparison:**

```wl
FullSimplify[{Beta[k+1/2,(d-1)/2]/Beta[1/2,(d-1)/2]==Pochhammer[1/2,k]/Pochhammer[d/2,k],(Pochhammer[1/2,k+1]/Pochhammer[d/2,k+1])/(Pochhammer[1/2,k]/Pochhammer[d/2,k])==(2k+1)/(d+2k),(2k+1)/(d+2k)<=(2k+1)/d},Assumptions->d>1&&k>=0&&Element[k,Integers]]
(* Out[1]= {True, True, True} *)
```

**Gaussian determinant factor:**

```wl
Integrate[Exp[-(1-z^2)g^2/2]/Sqrt[2Pi],{g,-Infinity,Infinity},Assumptions->0<=z<1]
(* Out[1]= 1/Sqrt[1 - z^2] *)
```

**Loss cases and constant field:**

```wl
FullSimplify[{Reduce[0<=t<=2&&j<=0&&t j>0,{j,t},Reals],Reduce[0<=t<=2&&j>=0&&t j>2 j,{j,t},Reals],1-Tanh[j]==2/(1+Exp[2 j])},Assumptions->Element[j,Reals]]
(* Out[1]= {False, False, True} *)
FullSimplify[{Log[2]-2a-Log[1+Exp[-2a]]==-a-Log[Cosh[a]], Cosh[a]==1+2Sinh[a/2]^2},Assumptions->a>=0]
(* Out[1]= {True, True} *)
```

The earlier query `FullSimplify[{1-Tanh[j]==2/(1+Exp[2j]),Exp[t j]<=1+Exp[2j]/.j->0,Exp[t j]<=1,Exp[-t j]>=1},Assumptions->j<=0&&0<=t<=2]` returned `{True, True, E^(j*t) <= 1, E^(j*t) <= 1}`; it left the inequalities unevaluated. The `Reduce` query above resolved both required sign cases explicitly instead of treating unevaluated output as verification.

**Envelope curvature and stationary tilt:**

```wl
FullSimplify[D[-Log[1-y x^2],{y,2}],Assumptions->0<x<1&&0<y<1]
(* Out[1]= x^4/(-1 + x^2*y)^2 *)
FullSimplify[D[-h x-n Log[1-x^2]/2,x]/.x->h/(n/2+Sqrt[(n/2)^2+h^2]),Assumptions->n>0&&h>0]
(* Out[1]= 0 *)
```

**Small models:**

```wl
With[{c=19/10,a=2}, {Integrate[Boole[c+a Cos[x]<0],{x,0,2Pi}]/(2Pi),NIntegrate[(1-Tanh[c+a Cos[x]])/(2Pi),{x,0,2Pi},WorkingPrecision->40],Integrate[(a Cos[x])^2,{x,0,2Pi}]/(2Pi)}]
(* Out[1]= {(Pi - ArcCos[-19/20])/Pi, 0.2864663597440133315488234397552599538840219509379339019396`40., 2} *)
With[{x=Total/@Tuples[{-1,1},4],c=3}, {Count[x,v_/;c+v<0]/Length[x],1-Abs[Mean[Tanh[c+x]]],Mean[x^2]}]
(* Out[1]= {1/16, 1 + (-3*Tanh[1] - 6*Tanh[3] - 4*Tanh[5] - Tanh[7])/16, 4} *)
```

Local raw logs live under `/tmp/yang-haar.JaWMI9/`; the queries/replies above retain the substantive Wolfram record in the repository. `bound-controls-final.log` is reproduced in full above. The initial warning-bearing control log is historical, not the final check. Record fields: command as given in each query block or control block, exit zero, timestamp UTC, log path and SHA256:

| Log basename | Timestamp (2026-11-23 UTC) | SHA256 |
|---|---|---|
| bound-integral.log | 13:02:23 | `057cd629835217d3308189ac4dfd383e9f1d535c005e5ff4171edbf845940699` |
| bound-alpha.log | 13:02:23 | `23f146dd41279cbfc43acea895ed8bf5b2f4ba52e47105824d5eeba3eae6f498` |
| bound-moment.log | 13:03:16 | `08307d264c39b7f6b06f7940ccb24e6abf69d38edb482af1e5e80942b0313141` |
| bound-gaussian.log | 13:03:17 | `2b601bdc0d587e9c962f044564ccbe6e67209e376a6be746432b48512638a1cd` |
| bound-loss.log | 13:03:17 | `b4e1c7c6b07187f47adeb46dc59c40761964d80ab59d5e563c58e44c055a6194` |
| bound-tilt.log | 13:03:18 | `6457977b110508ec56f0fe21d7be5b0ed127c9bac3754920593124ec09d8d934` |
| bound-circle.log | 13:03:18 | `009e13f620cb38ff0deb535dfc6f6d8877cd039919e5b262d2a8e8495033d7f2` |
| bound-signs.log | 13:03:18 | `14cb467b0f63a305c1f16b9d048534174c2a924669364b412e24082c878d9fe4` |
| bound-losscases.log | 13:03:46 | `bc2c7727c07c19257515f2dd38aa3b4c64d854f90c8a8aa6c5e2ff15a3776c85` |
| bound-envelope.log | 13:03:46 | `9c97a242223d6f98f31b44d2f525a225a5b397f36689d18bea9138e966a414d7` |
| bound-constant.log | 13:04:54 | `3ba2f04c79465bef4e510889a2fd8a520ffdc9867e425fc820a6701fda98c60f` |
| bound-controls.log | 13:04:54 | `c17e1ae99ca0036e85443a7227f81d846321552128a3534a041dd65f6b7ee8a3` |
| bound-controls-final.log | 13:05:34 | `e1739182cb4817916c0cad63d93cacd9a4bad22ad38520ccc013e45396362f96` |

The checked source `scripts/haar_slab_bound.py` SHA256 is `8ac9d49fb4c5bee878b03d8b7d7512067e7a1a27801771aae1a86d04dd6dd220`. The only bound call site observed in the shared worktree was `scripts/haar_shell_probe.py`, passing `orbit.constant.sum(), orbit.B, orbit.dim`, consistent with this interface. That independently owned integration was not edited or executed by this row.

## Limits

No optimized sign witness enters the measure or bound. No finite-draw count is a lower bound or estimate supplied by this analytic routine. Weighting these conditional ceilings by preceding shell magnitudes is a separate accounting step and does not make chain samples independent. This row establishes no uniform-in-configuration decay rate, certified floating arithmetic, adaptive gauge integration scheme, continuum result, or mass gap. Product-Haar normalization and its fixed-law signed estimator identity are separate from this exponential-moment calculation.
