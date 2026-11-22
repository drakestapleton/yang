# `yang`: Pure Seeded-OM-2 + Native GB10 (SM121) UFBI Yang–Mills Mass Gap Falsification, `CentralObs` Discovery & Formal Bridge Suite

Connected repo of [`omega-mv`](https://interplane.io/drakestapleton/omega-mv) (pinned at `3f2c70dc5`, `seed/out/omc` SHA-256 `708fdc0f81866594ed6df2f492b7a8a6bc7456f2d733a838b7f840549ebba6c3`).

Zero C, zero Python, zero Rust, zero `libcuda.so.1` on the execution path: every host driver and native SM121 GPU SASS kernel is compiled directly by `seed/out/omc` into static AArch64 ELF binaries running over `/dev/nvidia*` on DGX Spark GB10.

## Engines & Formal Bridge

1. **Check #1 (`src/ufbi_check1_gb10.om` + `src/ufbi_check1_kernels.om`)**: 4D massive free scalar UV-divergence test ($L \in \{8, 16, 32, 64\}$, fixed physical $m_{\text{phys}}\ell$), cross-checked against an exact 4D DST-I spectral oracle on $L=8$. Confirms unrestricted all-site Schur-complement TV diverges as $O(L)$ (`TV_raw = 1.0`), whereas smeared `CentralObs` contracts. Evidence: `evidence/check1_gb10_run.tsv`.
2. **`CentralObs` Synthesizer Wave-1 (`src/ufbi_obs_synth.om`) & Wave-2 (`src/ufbi_obs_synth_w2.om`)**: Ports `omega-mv`'s pure-OM-2 Observational-Equivalence search (`INV-1` BFS depth barriers, `INV-2` `MAX_PROBES=32` + 70% occupancy cutoff, `INV-3` branchless validity), **Physics Operator Prior** (`ratio > sub > mul > add`), and **Wake-Sleep Depth-2 Combinator Mining** to 4D $SU(2)$ lattice gauge-invariant observables.
   - Wave-2 result (`evidence/obs_synth_w2_run.tsv`): `3,463` unique ASTs (`2,304` equiv-pruned, `246` INV-3 guards, `max_probes=4`, `2/2` non-gauge-invariant controls killed). Top Depth-2 candidate `ratio(ratio(ADJ_PLAQ_S0, PLAQ1x1_S2), chi1(ADJ_PLAQ_S0))` reaches `uv_score = 41.033` at exact `gauge_err = 0.000000` (`5.9x` over Wave-1's `6.96`, `16.8x` over bare plaquette `2.44`).
3. **Check #3 (`src/ufbi_check3_gb10.om` + `src/ufbi_check3_kernels.om`)**: Native SM121 quaternion-packed 4D $SU(2)$ lattice Monte Carlo (Kennedy–Pendleton heatbath + exact 4-FMA quaternion overrelaxation on even/odd checkerboard) + Two-Stage Trickster adversarial twisted-collar search with held-out confirmation. Evidence: `evidence/check3_gb10_run.tsv`.
4. **Check #4 (`src/ufbi_check4_gb10.om` + `src/ufbi_check3_kernels.om`)**: Live GB10 out-of-sample validation of 8 `CentralObs` functionals (including 2-step APE smeared Wilson loops, `W2_CHAMP`, and smeared `CREUTZ_2x2` ratio) across:
   - **Experiment 4A (`decay_b230`)**: Fixed $\beta = 2.30$, $L \in \{6, 8, 10, 12, 16\}$ (`C0_cold` vs `C3_hot_haar` & `C5_nonab_twist`). Smeared `W2_2` and `CREUTZ_2x2` decay exponentially with boundary-to-core distance $R = L/2 - 1$: `a * m_eff = 0.402` (`8.9x` drop on `C3_hot_haar`) and `0.504–0.515` (`16.2x–17.2x` drop on `C5_nonab_twist`).
   - **Experiment 4B (`fixed_ell`)**: Exact 2-loop $SU(2)$ fixed-physical-box continuum scaling ladder ($L \cdot a(\beta) = 4.731 \times 10^{-2}$ constant: `(L=8, beta=2.300000) -> (L=12, beta=2.461245) -> (L=16, beta=2.575210)`). Pole-free smeared `CREUTZ_2x2` drops **`97.97x`** (`0.141369 -> 0.001443`, `9.38σ -> 0.20σ`) on `C3_hot_haar` and **`64.16x`** (`0.111824 -> 0.001743`, `6.27σ -> 0.30σ`) on `C6_trick_vort`; smeared `W2_2` drops **`113.33x`** / **`26.99x`**. Meanwhile `W2_CHAMP` exposes a real denominator-pole hazard ($\chi_1(0.5) = 0$) at strong coupling $\beta=2.30$, motivating strictly positive denominator constraints in future synthesis waves.
   - Evidence: `evidence/check4_gb10_run.tsv`, `evidence/check4_gb10_receipt.json` (`window_id: 20261122T202905Z-68a2cb`, `58.913 s`, `exit: 0`, `nvrm_errors_delta: 0`).
5. **Formal Lean 4 Bridge (`proofs/UfbiMassGap.lean`)**: Pure zero-dependency Lean 4.36.0 machine-checked proof bridge (`evidence/lean_ufbi_bridge.txt`, `0` errors, `0` warnings, `0` `sorryAx`, standard axioms `[propext, Classical.choice, Quot.sound]` only):
   - `ast_gauge_invariant` (every `CentralObs` AST synthesized from gauge-invariant primitives is exactly gauge-invariant) + negative control `raw_link_not_gauge_invariant`.
   - `ufbi_implies_connected_clustering` (conditional bridge: uniform boundary contraction implies connected exponential clustering).
   - `exponential_decay_implies_spectral_gap` (discrete-time transfer-matrix exponential decay $\implies$ strict spectral mass gap $\Delta \ge m > 0$) + negative control `massless_mode_violates_decay`.
   - `schur_uv_divergence_unbounded` (formalizes the Check #1 UV-divergence obstruction for unrestricted all-site boundary norms).

> **Scientific scope note:** `proofs/UfbiMassGap.lean` proves the *conditional* mathematical bridge (`UFBI contraction -> connected clustering -> spectral gap > 0`) and exact AST gauge invariance over explicit models; Checks #1–#4 provide live GB10 empirical lattice evidence for continuum-stable `CentralObs` contraction. Proving the continuum 4D $SU(N)$ UFBI contraction bound unconditionally as $a \to 0$ remains the open Clay Millennium Problem.

## Build & Run (Spark AArch64 + GB10)

```sh
sh scripts/build_and_run_spark.sh check1
sh scripts/build_and_run_spark.sh obs_synth
sh scripts/build_and_run_spark.sh obs_synth_w2
sh scripts/build_and_run_spark.sh check3
sh scripts/build_and_run_spark.sh check4
sh scripts/build_and_run_spark.sh proofs
```
