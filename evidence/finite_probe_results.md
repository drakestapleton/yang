# Finite tests of the proposed RG changes

## The temporal-gauge score at β = 2.30

On the archived 32⁴ step-three fit, the fundamental term is 1.22041 in the isotropic score. The open-time count gives 0.94921 in total variation and 0.77534 for the geodesic trial constant $14\sqrt{(8/(9\pi))^2+(3\pi/32)^2}\,|\beta_F|$. Dividing the coupling by the sufficient threshold 0.170 gives 0.79765. The two computations answer different questions.

| Trial score with five fitted operators | Fundamental | Remaining four | Total |
|---|---:|---:|---:|
| Temporal TV | 0.94921 | 0.72418 | 1.67339 |
| Temporal geodesic $W_1$ | 0.77534 | 0.72418 | 1.49952 |
| Temporal $W_2$ | 0.54802 | 0.72418 | 1.27220 |

The four terms are 0.15198 (adjoint), 0.17532 (rectangle), 0.06388 (2×2 square) and 0.33300 (crown). All totals set the unknown remainder to zero. The TV and $W_1$ rows reuse the favorable coefficient 14 on the adjoint as a numerical screen. The last row is the expression in `temporal_gauge_multiloop_w2_open_ball`. Periodic time leaves a holonomy after fixing a tree. Applying an open-time row count to the actual periodic action would require controlling that seam, the discarded operators and the transport hypotheses. An isotropic replay from the six-decimal couplings agrees with the archived scores within their rounding tolerance on all 23 rows. [Rescored table](check10_temporal_scores.tsv) · [Lean constants](../proofs/WilsonPolymerBridge.lean)

## Negative bare adjoint coupling

Check 9 defines $dAdj_{nonW}$ as the observed adjoint trace minus a matched Wilson reference. Its value −0.0380 at β = 2.50 is an observable residual. Check 10 estimates an action coefficient by solving the five-operator system. To test an actual deformation, we set the *bare* coefficient of $(4P^2-1)/3$ to −0.038, with $P=\mathrm{Re}\,\mathrm{Tr}(U_p)/2$. Eight independently seeded paired chains per coupling on periodic 4⁴ boxes compare the Wilson and deformed laws. A Wilson heat-bath proposal has a Metropolis correction using the exact change in the six incident adjoint plaquettes. The same random numbers couple the two marginals. Each chain had 96 warmup and 128 measured sweeps, with four hot and four cold starts per coupling. [Original Check 9 definition](../src/ufbi_check9_gb10.om) · [Raw chain moments](mixed_action_pairs.tsv)

| $\beta_F$ | Change in mean $P$ | Change in $6L^4\,\mathrm{Var}(\bar P)$ |
|---|---:|---:|
| 2.0 | −0.00903 ± 0.00080 | −0.0059 ± 0.0172 |
| 2.3 | −0.01309 ± 0.00153 | +0.0762 ± 0.0241 |
| 2.5 | −0.00801 ± 0.00043 | −0.0046 ± 0.0115 |

The susceptibility is the response of the average plaquette to $\beta_F$ at fixed $\beta_A$. The squared one-point subtraction uses distinct chain IDs. Each quoted error uses independent paired chains. The proxy increased at β = 2.3 in this small box. These three unmatched bare couplings cannot locate the crossover peak, establish universality or determine the blocked rectangle and crown. [Reduction](finite_probe_summary.tsv)

There is an exact transfer-positivity obstruction for this example. At $(\beta_F,\beta_A)=(2.3,-0.038)$ the first negative SU(2) character coefficient occurs at spin 19/2. After removal of the positive constant $e^{\beta_A/3}$ it is approximately $-2.12790262597\times10^{-19}$. On the unit circle, expand the nonconstant action as $(\beta_F/2)(z+z^{-1})+(\beta_A/3)(z^2+z^{-2})$. The difference between Laurent coefficients $n$ and $n+2$ gives the Haar character coefficient. The replay bounds the omitted exponential series after degree 110 by a geometric tail with exact rational arithmetic. This rules out the usual nonnegative-character argument for the one-link transfer factor at this bare action. The positive Monte Carlo weight still defines a finite-volume probability measure. [Exact sign check](../scripts/check_negative_adjoint.py) · [Bhanot and Creutz on the mixed action](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.24.3212)

## Residual gauge alignment on the archived replicas

The 51- and 50-face masks were measured after fixing an entire spanning tree. Their quoted $3.5\times10^{-28}$ was a fraction of incoming source weight removed on the hot chain. A Metropolis exchange has a distinct acceptance statistic.

We replayed the two β = 2.3 chains and matched all 256 single-mask fields to the archive. For each mask, determine a proper three-dimensional rotation from the vector parts of the *unswapped* exterior links on its split faces. It maximizes their least-squares overlap. Apply it by quaternion conjugation to each link moving from replica B to A and use its inverse for A to B. The exterior stays fixed. Applying the operation twice returns both configurations. Conditional on the exterior, conjugation and swapping preserve product Haar. A completely exchanged plaquette has the same trace. We verified these identities numerically and compared the change in the entire action with the change on the split faces every eighth observation. A gauge optimizer that also sees links it subsequently replaces needs its own reverse-map and measure argument. [Replay code](../scripts/replay_aligned_cut.py) · [Raw fields](check_aligned_cut.tsv)

| Start and split faces | $\log_{10}$ mean swap acceptance, archived frame | With exterior alignment |
|---|---:|---:|
| Hot, 51 | −27.79 | −20.85 |
| Hot, 50 | −29.01 | −21.11 |
| Cold, 51 | −19.78 | −23.14 |
| Cold, 50 | −29.14 | −14.63 |

These are single-mask empirical averages of $\min(1,e^{-2J})$ on 64 recorded pairs per start. The largest gain was 14.51 orders of magnitude; one mask on the cold chain became worse. None had appreciable overlap. The alignment uses the residual global conjugation allowed by the pinned tree. The two fitted frames may depend on different exteriors, so multiplying their observed reduction factors would require a new joint-orbit identity. [Single-mask reductions](finite_probe_summary.tsv) · [Original source-weight definition](wilson_local_neighborhoods.md)

## A finite collar test

Freeze the tangential links on the entire boundary of an open $L^4$ box. Compare the identity collar with one central boundary link multiplied by −1. The measured interior operator averages the four central 01 plaquettes at the two middle spectator coordinates. The two copies use exact single-link Wilson heat-bath marginals coupled through common radial rejection draws and a common tangent direction. Eight independent pairs per geometry use 64 warmup and 128 measured sweeps, alternating between hot and cold interiors. At β = 0 the distinct collars give identical updated interiors, and an identical-collar β = 2.3 control coalesces exactly from identical interiors. [Sampler](../scripts/probe_open_collar.py) · [Raw pair means](open_collar_pairs.tsv)

| $L$ | β | Center change | Mean absolute paired change |
|---:|---:|---:|---:|
| 4 | 2.0 | −0.0170 ± 0.0057 | 0.1461 ± 0.0050 |
| 4 | 2.3 | −0.0181 ± 0.0039 | 0.1239 ± 0.0025 |
| 6 | 2.0 | +0.0040 ± 0.0079 | 0.1791 ± 0.0041 |
| 6 | 2.3 | +0.0101 ± 0.0050 | 0.1456 ± 0.0036 |

Exactly independent equilibrium marginals would give $|\Delta\langle P\rangle|\le W_1\le\mathbb E|P'-P|$ for the **one-dimensional laws of this scalar observable**, using its absolute-difference metric. The numbers are finite-run estimates for one pair of collars. Inferring a DS contraction requires the appropriate block metric and influence sum, an upper bound over all allowed exterior perturbations, and control of sampling or convergence error. Inferring a physical rate also requires the bound to scale with the lattice spacing. Neither the exact worst-case mixing time nor a minimum certifying box size follows from these measurements.

## Many-cell expansion and continuous quadrature

Lean proves the finite Mayer expansion over bridge plaquettes and the identity $Z_{12}/(Z_1Z_2)=1+\mathbb E[e^{-V_{12}}-1]$ for two independent normalized cell measures with an integrable bond. The two-cell bridge activity feeds the repository’s Kotecký–Preiss theorem directly. For one hard-core bond, choosing polymer weight parameter $a=1$ gives the condition $e|z|\le 1$ and a boundary-ratio bound. For $k$ shifted Wilson bridge plaquettes the elementary activity estimate is $|z|\le 1-e^{-2\beta k}$. It suffices only through $\beta k\le-\tfrac12\log(1-e^{-1})\approx0.22934$. At β = 12 and $k=1$ the upper bound on $e|z|$ is 2.71828. To use the single-star bracket in the existing polymer theorem one must choose genuinely disjoint variables, assign crossing plaquettes, use inter-star concentration, and sum connected activities over their supports. The single-star estimate alone supplies no such uniform sum. [Mayer identities](../proofs/StarMayer.lean)

For each tabulated field box, Lean bounds both normalized continuous energies by the same integer pair printed by the replay. The proof integrates outward-rounded density and signed cosine-moment bounds over the 2,048 angular cells, then bounds the flux from the nearer pole. It treats the two pole cells directly and checks the lower density is strictly positive on every interior cell throughout the field range. The executable theorem identifies both running sums, the cached cell lookups and the rounded final normalization. All 2,048 field-box pairs reproduce the archived Omega output. This closes the continuous quadrature step for these one-link energies. The star-cell integrals with padded binary64 are a separate calculation. [Continuous cell enclosures](../proofs/DyadicPartition.lean) · [Polar flux and end cells](../proofs/DyadicPolarFlux.lean) · [Executable field bound](../proofs/DyadicEnergyReplay.lean)

At β = 0.288 the degree-12 bound from the rounded energy table is 1.014752. A separate analytic proof bounds the squared trial coefficient by $15552/15625=0.995328$ at that coupling. Applying this one-link result to the periodic four-dimensional Wilson measure still requires a block comparison controlling the geometry and holonomy. [Analytic endpoint](../proofs/OneLinkTransport.lean)
