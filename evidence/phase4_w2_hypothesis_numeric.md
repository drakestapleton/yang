# Status of the `L_par² ≤ 1/12`, `L_perp² ≤ 1/12` hypotheses of `s3_w2_orthogonality_bound`

Date: 2026-11-22. Status: **NOT PROVED** (exact at `r = 0`, sampled at positive fields).
This note is offline floating-point quadrature (python3 + numpy on the Mac). It is evidence,
not a certificate, and it is not on the OM-2 execution path.

## What the quantities are

1-link conditional law on `S³` in the polar angle `θ ∈ [0, π]` with staple field `r ≥ 0`:
`p_r(θ) = (2/π) sin²θ e^{r cos θ} / Z(r)`, `m(r) = E_r[cos θ]`.

- Parallel (Benamou–Brenier) speed: `L_par(r)² = ∫_0^π F_r(θ)² / p_r(θ) dθ`,
  `F_r(θ) = ∫_0^θ (cos t − m) p_r(t) dt` (this is what `pass2W2Par` encloses).
- Transverse bound: `L_perp(r)² ≤ E_r[cos²θ]/27 + (2/3) E_r[(1/3 − r sin²θ cos θ / 6)²]`
  (this is what `pass1Box` encloses).

## Exact at `r = 0` (hand computation)

- `p_0 = (2/π) sin²θ`, `m = 0`, `F_0 = (2/π) sin³θ / 3`, so
  `L_par(0)² = (2/π)(1/9) ∫_0^π sin⁴θ dθ = (2/π)(1/9)(3π/8) = 1/12`.
- `E_0[cos²θ] = 1/4`, so the transverse bound is `1/108 + (2/3)(1/9) = 1/108 + 8/108 = 1/12`.

The parallel speed and the transverse upper bound both equal `1/12` at zero.
A box that straddles this equality has no slack for the current upper-endpoint test.
A proof could treat zero exactly and enclose the change from zero over the field range of interest.

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

## What this means for the claims

- The Lean W₂ windows (`√3/9`, `√3/7`, `√3/6`) remain **conditional** on these two hypotheses.
- A sufficient next result would bound both quantities throughout the required finite field range.
  In the variable `x = cos θ`, `L_par² = Cov_r(φ, x)` where `φ` solves
  `(1 − x²) φ'' + (r(1 − x²) − 3x) φ' = −(x − m)`; at `r = 0`, `φ = x/3` gives `Var_0(x)/3 = 1/12`.
- The separate numerical verifier reports the rows
  (`0.180`, `0.240`, `0.280`), which use the enclosed constant, not `1/(2√3)`.

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
