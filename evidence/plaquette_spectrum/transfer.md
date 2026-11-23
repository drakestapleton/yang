# One spatial plaquette in the Wilson transfer matrix

Use spatial volume `(Z/L)³` and periodic time `Z/N`. Omega sets `L = 8`, `N = 8, 16`, and β = 2.3. On slice U the operator A multiplies a wavefunction by

```math
P(U)=L^{-3}\sum_{x}\tfrac12\operatorname{Re}\operatorname{Tr}
 [U_0(x)U_1(x+\hat 0)U_0(x+\hat 1)^{-1}U_1(x)^{-1}].
```

Directions 0 and 1 are spatial. Time is direction 3. The two insertions have separately summed spatial positions. Omega's `sliceP` and Lean's `plaquette01` use exactly this orientation and normalization. A unit quaternion's scalar component equals the real normalized fundamental trace by `normalizedTrace_scalar`. Omega multiplies quaternion components in binary32 and accumulates each slice in binary64. Lean uses exact real integration.

## A finite time circle

Let S(U) sum the three spatial face actions and V(U,W,h) sum the three temporal face actions between the two slices, each with the convention 1 − ½ Re tr. The temporal links h have independent normalized Haar prior. The one-step kernel is

```math
K(U,W)=\int dh\,\exp\{-\beta[(S(U)+S(W))/2+V(U,W,h)]\}.
```

Multiplying around the circle counts each face once. Independent integration of the temporal links gives the product of K. Cut the circle at slice zero and integrate its two arcs by Fubini. For a separation d = 0,…,N−1 this gives the finite formula

```math
C_N(d)=\frac{\operatorname{Tr}(A K^d A K^{N-d})}{\operatorname{Tr}(K^N)}
       -\left(\frac{\operatorname{Tr}(A K^N)}{\operatorname{Tr}(K^N)}\right)^2.
```

Lean realizes the finite trace as a diagonal integral with one closing bond kept explicit (`cutTrace`). The theorem `wilson_plaquette_periodic_trace` starts from the rectangular link array and proves this equality for the actual Wilson operator at every real coupling. The closing bond is one time step, so the formal index satisfies N = d + r + 1. The spatial slice integration is normalized product Haar. `positive_partition` licenses division, and `wilson_time_shift` licenses averaging over source times. The partition ratio cancels any positive overall transfer normalization. A finite circle has a thermal one-point expectation at its own N, which is also the target of the cross-chain subtraction in the measurement.

For the state swap and transfer diag(1,q), Lean's `swap_regression` computes (q³ + q⁵)/(1 + q⁸) at N = 8 and d = 3. The vacuum matrix element is q³. `swap_wrap_excess` proves the finite answer is strictly larger for 0 < q < 1.

## Positive energies at fixed spatial volume

Time reversal and invariance of Haar under inversion give `kernel_symmetric`. Gauge transformations on the source slice can be absorbed into the temporal links. Thus `operator_physical` puts every output in the physical subspace, and `face_gauge` shows multiplication by P preserves that subspace. The inner products in `operator_symmetric` use the actual spatial Haar measure.

Strict positivity of the quadratic form requires more than positivity of the Boltzmann density. In `WilsonPlaquettePositivity`, normalized trace of a link times an inverse link becomes the Euclidean scalar product of their four quaternion coordinates. On gauge-invariant functions the temporal gauge can be absorbed by changing integration variables. After multiplication by positive spatial action factors, the remaining kernel is the exponential of β times a sum of coordinate scalar products. Its nth Taylor coefficient integrates to a sum of squared polynomial moments. These coordinates separate the spatial link configurations. Stone–Weierstrass and the full support of Haar give strict positivity on every nonzero continuous physical function at β > 0. These statements hold for the concrete kernel in this experiment.

The Haar integral operator is compact on the real slice Hilbert space $L^2(dU)$. Its kernel sends bounded sets in $L^2$ to equicontinuous bounded families of continuous functions. Compactness and self-adjointness give the orthogonal eigenspace decomposition. The pointwise positive kernel sends each nonzero nonnegative continuous function to a strictly positive function. A top eigenfunction has no nodes, and comparing two top eigenfunctions at a single configuration proves simplicity. The resulting unit vacuum $\Omega$ exists for every positive integer spatial side and every $\beta>0$. [Concrete operator and vacuum](../../proofs/WilsonPlaquetteHilbert.lean)

Set $S=K/\|K\|$ and $v=(P-\langle\Omega,P\Omega\rangle)\Omega$. In the closed physical subspace, a zero-transfer mode has zero overlap with every spatially weighted coordinate polynomial, so density forces it to vanish. Centering removes the simple top mode. For projection $\Pi_r$ onto eigenvalue $r$ of $K$, the remaining weights give the finite measure

```math
\mu_P=\sum_{0<r<\|K\|}\|\Pi_r v\|^2\,\delta_{-\log(r/\|K\|)},\qquad
\lim_{N\to\infty} C_N(d)=\langle v,S^d v\rangle=\int e^{-dE}\,d\mu_P(E).
```

The occupied modes form an at most countable set. At fixed $d$, increasing the other arc projects the normalized transfer powers onto the vacuum. A smoothing step and dominated convergence carry this limit through the cut diagonal integral and the normalization by the finite partition function. The limiting one-point subtraction becomes vacuum centering. Lean proves the result for every integer $d\ge0$, including the total mass at $d=0$, and proves $\mu_P(({-\infty},0])=0$. The final theorem takes the spatial side, the positive coupling and the separation as inputs. Its axiom audit lists `propext`, `Classical.choice` and `Quot.sound`. [Vacuum limit and energy measure](../../proofs/WilsonPlaquetteVacuum.lean)

This supplies a positive spectral measure for one lattice observable at fixed spatial volume. Yang's theorem `word_laplace_limit_of_translation_match` takes finite measures on spacetime whose characteristic functions converge to the continuum word correlations. Here the measure is on energy alone. Matching the spatial momenta and field-word translations, and controlling the change in lattice spacing and volume, are further steps. Those are open. [Existing word hypotheses](../lean_wilson_cyclic_gap.txt)

The analytic starting point is Lüscher's construction of the positive Wilson transfer matrix. [Original paper](https://bib-pubdb1.desy.de/record/396349) · [Finite Wilson trace](../../proofs/WilsonPlaquetteTransfer.lean) · [Wilson quadratic-form positivity](../../proofs/WilsonPlaquettePositivity.lean)
