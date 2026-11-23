# Phase IV one-link energy bounds and the periodic Wilson obstruction

Lean proves both normalized trial energies are at most $1/12$ throughout $0\le r\le6\beta$ for $\beta\le7/25$. At $r=0$ both equal $1/12$. The following argument covers zero and positive fields together. [Lean proof](../proofs/OneLinkTransport.lean)

The analytic endpoint theorem now also covers β = 0.288, with a squared degree-12 trial coefficient of at most 0.995328. A second proof checks both continuous energies against the executable integer entries on the full angular and field grid. [Field-box enclosure](../proofs/DyadicEnergyReplay.lean) · [Numerical comparison and scope](finite_probe_results.md)

## Analytic bound

Write $p=\sin^2\theta\,e^{r\cos\theta}$, $Z=\int p$, $m=\int p\cos\theta/Z$ and $F(t)=\int_0^t p(\cos\theta-m)$. For the polar energy put $K=F/\sin^2\theta$. L’Hôpital’s rule gives $K=0$ by continuous extension at both poles. Differentiate
$$F(\cos\theta-m)-K^2 e^{-r\cos\theta}\sin\theta(3\cos\theta-3r\sin^2\theta/5).$$
The derivative equals $3F^2/(2p)-p\sin^2\theta/6$ plus three nonnegative terms written explicitly in Lean. Its primitive vanishes at both ends. Thus $\int F^2/p\le\int p\sin^2\theta/9$. Pairing $\theta$ with $\pi-\theta$ and integrating the derivative of $\sin^3\theta\cos\theta\cosh(r\cos\theta)$ gives $\int p\sin^2\theta\le3Z/4$ for $r\ge0$.

For the transverse field take $x=\cos\theta$ and $B=x^2/27+(2/3)(1/3-r(1-x^2)x/6)^2$. On the half interval $0\le x\le1$, pairing the excess $p(B-1/12)$ reduces the estimate to $rx(1-x^2)\cosh(rx)\le(7/2)\sinh(rx)$. Here $rx\le42/25<7/4$, $rx\le\sinh(rx)$ and $\cosh(rx)\le7/2$. The remaining derivative integrates to zero.

## Lattice and continuum conditions

The verified incidence count is 12. On the period-2 torus the assignment fixes both directed links between $(0,0,0,0)$ and $(0,0,0,1)$. If vertex gauges send both link values $u,v$ to the identity, multiplication gives $uv=1$. Periodic configurations with nontrivial loop holonomy therefore require another treatment. [Lean cycle and group proofs](../proofs/PhaseFourBridge.lean)

The conditional continuum theorem consumes a volume-uniform degree-12 shell estimate using the two trial energies. Taking the spectral limit transfers the recurrence to all integer physical times. Forward spectral support bounds the Laplace transform between adjacent shells. The proof uses W0/W1 and a vacuum strip-support premise. Establishing that the actual Wilson heat-bath transport and reconstructed observables satisfy those hypotheses remains open. [Finite-volume transfer](../proofs/DobrushinShlosman.lean) · [Spectral interpolation](../proofs/OpenAiYmBridge.lean)

## Historical numerical cross-check

The table below was computed with NumPy. The Lean theorem above uses continuous real integrals.

## What the quantities are

1-link conditional law on `S³` in the polar angle `θ ∈ [0, π]` with staple field `r ≥ 0`:
`p_r(θ) = (2/π) sin²θ e^{r cos θ} / Z(r)`, `m(r) = E_r[cos θ]`.

- Parallel (Benamou–Brenier) speed: `L_par(r)² = ∫_0^π F_r(θ)² / p_r(θ) dθ`,
  `F_r(θ) = ∫_0^θ (cos t − m) p_r(t) dt` (the polar flux functional).
- Transverse bound: `L_perp(r)² ≤ E_r[cos²θ]/27 + (2/3) E_r[(1/3 − r sin²θ cos θ / 6)²]`
  (the transverse trial-field cost).

## Exact at `r = 0` (hand computation)

- `p_0 = (2/π) sin²θ`, `m = 0`, `F_0 = (2/π) sin³θ / 3`, so
  `L_par(0)² = (2/π)(1/9) ∫_0^π sin⁴θ dθ = (2/π)(1/9)(3π/8) = 1/12`.
- `E_0[cos²θ] = 1/4`, so the transverse bound is `1/108 + (2/3)(1/9) = 1/108 + 8/108 = 1/12`.

## Numeric values for `r > 0` (2,000,001-point Simpson outer integrals, trapezoidal flux integrated inward from both ends)

| r | L_par² | L_par² − 1/12 | transverse bound² | − 1/12 |
|---|---|---|---|---|
| 0 | 0.08333333 | −3.2e−14 | 0.08333333 | −1.4e−17 |
| 0.01 | 0.08333168 | −1.65e−06 | 0.08333267 | −6.66e−07 |
| 0.1 | 0.08316863 | −1.65e−04 | 0.08326684 | −6.65e−05 |
| 0.3 | 0.08186714 | −1.47e−03 | 0.08273874 | −5.95e−04 |
| 0.6 | 0.07767800 | −5.66e−03 | 0.08100607 | −2.33e−03 |
| 1.0 | 0.06887171 | −1.45e−02 | 0.07718496 | −6.15e−03 |
| 1.5 | 0.05529946 | −2.80e−02 | 0.07072839 | −1.26e−02 |
| 2.0 | 0.04190910 | −4.14e−02 | 0.06347266 | −1.99e−02 |
| 3.0 | 0.02198312 | −6.14e−02 | 0.05016524 | −3.32e−02 |
| 5.0 | 0.00620911 | −7.71e−02 | 0.03707992 | −4.63e−02 |
| 10.0 | 0.00078344 | −8.25e−02 | 0.04890692 | −3.44e−02 |
| 20.0 | 0.00009601 | −8.32e−02 | 0.08497202 | +1.64e−03 |

Leading behaviour near `r = 0` (fit): `L_par² ≈ 1/12 − 0.0165 r²`, transverse `≈ 1/12 − 0.00666 r²`.
The transverse bound increases between the samples at 5 and 10. At 20, direct quadrature gives
`0.08497202232 > 1/12`. This concerns the cost of the chosen transverse field. The optimal
transverse speed could be smaller. Phase IV only uses fields through `6β`.

## Independent transverse check

Wolfram Language query and result (dimensionless)

```wolfram
With[{r=20}, With[{w=Sin[t]^2 Exp[r (Cos[t]-1)]},
  NIntegrate[w (Cos[t]^2/27+2/3 (1/3-r Sin[t]^2 Cos[t]/6)^2),
    {t,0,Pi},WorkingPrecision->30] / NIntegrate[w,{t,0,Pi},WorkingPrecision->30]]]
(* 0.0849720223224379671806835459049431371109937664715871780584`29.69897000433602 *)
```

## Reproduce

```python
import numpy as np
N=2000001; th=np.linspace(0,np.pi,N); dt=th[1]-th[0]; h=N//2
S=lambda y: dt/3*(y[0]+y[-1]+4*y[1:-1:2].sum()+2*y[2:-1:2].sum())
for r in [0,0.01,0.1,0.3,0.6,1.0,1.5,2.0,3.0,5.0,10.0,20.0]:
    w=(2/np.pi)*np.sin(th)**2*np.exp(r*(np.cos(th)-1)); p=w/S(w); m=S(np.cos(th)*p)
    g=(np.cos(th)-m)*p; inc=(g[1:]+g[:-1])/2*dt
    Ff=np.concatenate([[0],np.cumsum(inc)]); Fb=-np.concatenate([np.cumsum(inc[::-1])[::-1],[0]])
    F=np.where(np.arange(N)<=h,Ff,Fb); q=np.zeros(N); q[1:-1]=F[1:-1]**2/p[1:-1]
    d=1/3-r*np.sin(th)**2*np.cos(th)/6
    print(r, S(q), S(np.cos(th)**2*p)/27+(2/3)*S(d*d*p))
```
