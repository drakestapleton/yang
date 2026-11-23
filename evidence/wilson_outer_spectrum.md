# Can any rigid relative color reverse the outer slab?

No on the archived canyon samples. The four rotations did not miss a narrow sign-changing region: minimizing the *unclipped signed field* over the entire SU(2) color orbit still left it positive on every sampled pair. Some individual boundary patches can reverse sign. What fails is making the sum reverse.

## Measurement

Periodic `4^4`, time separation two, radius-one outer slab, same spanning-tree frame and sampled configurations as the `--colors` canyon runs at `85ea05d`. The field is `J = (log w_before − log w_exchanged)/2`, so the signed shell factor is `tanh J`. One sample is one pair of configurations after the specified sweep stride, not four independent orientation draws. Ranges below are extrema in the saved samples (hot and cold combined), not confidence intervals or bounds on the population.

| SU(2) β | Sample pairs | Range of the minimum rigid J | Range of the sum of site minima | Pairs with negative sum of face minima |
|---:|---:|---:|---:|---:|
| 2.3 | 512 | 341.251 to 457.449 | 34.084 to 130.958 | 512/512 |
| 4 | 512 | 435.474 to 703.374 | 93.208 to 255.465 | 493/512 |

Even allowing a separate orientation for each boundary base site (shared by its three crossing plaquettes) leaves the total positive on these samples. Allowing each crossing plaquette its own orientation can instead drive the sum through zero in the cases in the last column. **Neither relaxation is a new exchange identity.** Faces share links; independently minimizing their contributions does not construct a single gauge transformation on either replica. Configuration-dependent minimization is not the fixed-orientation signed average in the Lean theorem. The result locates the loss of cancellation; it does not improve the correlation bound.

At β = 0.1 the rigid field straddled zero on 87 of 128 SU(2) pairs, so the diagnostic can detect a sign change. For compact U(1) the recorded rigid minimum, maximum, and identity fields coincide at both canyon couplings. Internal conjugation in that subgroup cannot change a link. Bare-coupling matching does not match the physical scales of the two theories.

## Why the optimization covers every rigid orientation

Only temporal plaquettes that cross a slab boundary contribute. Write `b` for the top spatial link and `p` for the three-link path between the same vertices. Its normalized plaquette trace is the Euclidean quaternion dot product `p·b`. Swapping one link versus swapping the other three gives the same *sum* of the two replica traces. After conjugating the second replica by a unit quaternion `q`, the exchanged sum on a crossing face is

`p₀·(q b₁ q⁻¹) + b₀·(q p₁ q⁻¹)`.

For three-vectors `a,b` and `q=(w,v)`, the vector part of `q (0,b) q⁻¹` is `(w²−v·v)b + 2(v·b)v + 2w(v×b)`. Dotting with `a` gives a symmetric quadratic form in `(w,v)`; the invariant scalar part and pre-exchange action are multiples of the identity since `q·q=1`. Thus each face has a real symmetric matrix `M_f` for its contribution to `J`. The smallest and largest eigenvalues of `Σ M_f` are the two extrema on the unit sphere. This uses a binary64 symmetric eigensolver, not a grid of rotations or an interval certificate. For U(1) restrict each form to the real–i plane *before* optimizing.

The TSV stores one row per pair: identity field, minimum over the original internal orientations, extrema of the whole matrix, sums of independently minimized site and face fields, and the count of sites whose local field takes both signs. The site grouping is by the base of the temporal plaquette, separately on the two boundary sheets; it is not a star at a gauge-transformation vertex. Every 32nd measurement checks the two optimizing quaternions and a generic off-axis quaternion against a full rotate–exchange–retrace evaluation; these checks do not use the reduced field to compute the reference action.

## Replay (CPU; Python 3.14.6, NumPy 2.5.3)

```sh
python3 scripts/replica_shell_probe.py --outer-spectrum --beta 2.3 4 --warmup 256 --samples 256 > su2.tsv
python3 scripts/replica_shell_probe.py --outer-spectrum --group U1 --beta 2.3 4 --warmup 256 --samples 256 > u1.tsv
python3 scripts/replica_shell_probe.py --outer-spectrum --beta 0.1 --warmup 64 --samples 64 > beta01.tsv
```

[SU(2) pairs](wilson_outer_spectrum_su2.tsv) · [U(1) pairs](wilson_outer_spectrum_u1.tsv) · [Low-β control](wilson_outer_spectrum_beta01.tsv) · [Previous signed identity and product-loss criterion](lean_wilson_replica_exchange.txt).

Next test: construct a local transformation on **shared link variables**, establish the law and exchange identity in its chosen frame, then measure its signed, product-weighted shell loss. The negative face minima do not establish that such a transformation exists. No larger separation, spacing trajectory, uniform mass, or continuum spectral comparison was tested here.
