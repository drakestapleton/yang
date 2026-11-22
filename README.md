# `yang`: Pure Seeded-OM-2 + Native GB10 (SM121) UFBI Yang–Mills Mass Gap Falsification, `CentralObs` Discovery & Formal Bridge Suite

Connected repo of [`omega-mv`](https://interplane.io/drakestapleton/omega-mv) (pinned at `3f2c70dc5`, `seed/out/omc` SHA-256 `708fdc0f81866594ed6df2f492b7a8a6bc7456f2d733a838b7f840549ebba6c3`).

Zero C, zero Python, zero Rust, zero `libcuda.so.1` on the execution path: every host driver and native SM121 GPU SASS kernel is compiled directly by `seed/out/omc` into static AArch64 ELF binaries running over `/dev/nvidia*` on DGX Spark GB10.

## Engines, Audits & Formal Bridge

1. **Check #1 (`src/ufbi_check1_gb10.om` + `src/ufbi_check1_kernels.om`)**: 4D massive free scalar UV-divergence test ($L \in \{8, 16, 32, 64\}$, fixed physical $m_{\text{phys}}\ell$), cross-checked against an exact 4D DST-I spectral oracle on $L=8$. Confirms unrestricted all-site Schur-complement TV diverges as $O(L)$ (`TV_raw = 1.0`), whereas smeared `CentralObs` contracts. Evidence: `evidence/check1_gb10_run.tsv`.
2. **Check #2 (`evidence/check2_openai_ym_audit.md`)**: Direct line-referenced Lean 4 audit of [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028) (`PublicTheory.lean`, `ChallengeSpec.lean`, `HierarchyBridge.lean`, `PublicWilson.lean`). Verdict: **COMPATIBLE** — identifies the two exact open seams where continuum UFBI plugs in (`Hierarchy.Character` / `phaseMeasure` phase collapse, and `EnergyMomentumMeasure.projection` exclusion of `{p ∈ forwardCone | p ≠ 0 ∧ minkowskiSquare p < Δ²}`).
3. **`CentralObs` Synthesizers — Wave-1 (`src/ufbi_obs_synth.om`), Wave-2 (`src/ufbi_obs_synth_w2.om`), & Wave-3 INV-4 (`src/ufbi_obs_synth_w3.om`)**:
   - Ports `omega-mv`'s pure-OM-2 Observational-Equivalence search (`INV-1` BFS depth barriers, `INV-2` `MAX_PROBES=32` / 70% occupancy cutoff, `INV-3` bounded outputs), **Physics Operator Prior** (`ratio > sub > mul > add`), and **Wake-Sleep Depth-2 Combinator Mining** to 4D $SU(2)$ lattice gauge-invariant observables.
   - **Wave-3 (`INV-4` Pole-Free Guard, `evidence/obs_synth_w3_run.tsv`)**: Evaluates 16 independent MC snapshots across $\beta \in \{2.30, 2.50\}$ (`cold` vs `twist`), rejecting any ratio denominator unless strictly sign-definite with margin $\tau = 0.15$ and condition ratio $\le 4.0$ (`3,752` ASTs, `2,547` equiv-pruned, **`230` pole-prone denominators killed**, `2/2` non-gauge-invariant controls killed). Top winner is the pole-free Symanzik-like polynomial `sub(PLAQ1x1_S1, sub(RECT1x2_S0, CHAIR6_S2))` (`gauge_err = 0.000000`, `dTw/sig = 0.045`, `uv_score = 16.153`), followed by strictly positive-denominator Creutz-like ratio `ratio(mul(RECT1x2_S0, ADJ_PLAQ_S0), sq(PLAQ1x1_S0_T))` (`dTw/sig = 0.113`).
4. **Check #3 (`src/ufbi_check3_gb10.om` + `src/ufbi_check3_kernels.om`)**: Native SM121 quaternion-packed 4D $SU(2)$ lattice Monte Carlo (Kennedy–Pendleton heatbath + exact 4-FMA quaternion overrelaxation on even/odd checkerboard) + Two-Stage Trickster adversarial twisted-collar search with held-out confirmation. Evidence: `evidence/check3_gb10_run.tsv`.
5. **Check #4 (`src/ufbi_check4_gb10.om`) & Erratum**: Live GB10 validation (`evidence/check4_gb10_run.tsv`, `evidence/check4_gb10_receipt.json`, `WID=20261122T202905Z-68a2cb`, `nvrm_errors_delta=0`). Exposed Wave-2's `chi1(ADJ_PLAQ_S0)` zero-denominator pole at $\beta=2.30$. **Erratum on Experiment 4B:** The apparent `64x–113x` drop from `(L=8, β=2.300)` to `(L=16, β=2.575)` in Check #4 was inflated by three lattice artifacts: (i) 2-step APE + `2x2` loop smearing contact with the frozen collar at $L=8$, (ii) fixed-lattice $a^4$ operator shrinkage as $a \to 0$, and (iii) 2-loop asymptotic scaling overshooting measured non-perturbative $a\sqrt{\sigma}$ scaling ($\beta=2.50$, not $2.575$). **Superseded by Check #5 below.**
6. **Check #5 (`src/ufbi_check5_gb10.om`) — Referee-Proof Contact-Free Decay & Physically-Scaled Continuum Test**:
   - **Runtime `ZERO_CONTACT_ASSERT`:** Verified `max_direct_err = 0.000000 status=PASS` on all 9 `(L, r_loop, n_s)` geometries by swapping the frozen collar on a fixed interior configuration prior to MC.
   - **Experiment 5A (`decay_b230_clean`, $\beta=2.30$, $L \in \{8, 10, 12, 14, 16\}$, 160 sweeps):** Dropping contact-contaminated $L=6$ raises contact-free exponential decay rates on `C5_nonab_twist` to $a m_{\text{eff}} = 0.587$ (`P1x1_S0`, `13.3x` drop), $0.599$ (`P1x1_S1`), and **`0.763`** (`AdjP_S1`, `13.7x` drop, `R_bulk: 0.426 -> 0.031`).
   - **Experiment 5B (`phys_scaled_su2`, non-perturbative $a\sqrt{\sigma}$ matching $\ell\sqrt{\sigma} \approx 2.95 \to 2.98$):** Scales loop size ($r \propto L$) and APE smearing ($n_s \propto L^2$) together: `(L=8, β=2.30, r=1, n_s=1)` $\to$ `(L=16, β=2.50, r=2, n_s=4)`. Physical mean matches within `2.4%` (`0.853 -> 0.833`) with non-shrinking bulk fluctuation (`σ_bulk: 0.0325 -> 0.0468`). Dimensionless `R_bulk = δ/σ_bulk` remains cleanly bounded with zero UV blow-up (`C3_hot_haar`: `0.413 -> 0.033`, `0.13σ`; `C6_trick_vort`: `0.389 -> 0.247`, `0.85σ`).
   - **Experiment 5C (`gapless_ctrl_b6`, weak-coupling negative control $\beta=6.00$, $\xi \gg L$):** Exact same physically scaled operator pair shows `R_bulk` **growing `1.93x`** (`0.156 -> 0.301`, `1.36σ -> 1.75σ`) on the coherent vortex collar `C6_trick_vort`, refuting trivial $a^4$ operator decoupling (while random Haar collar `C3_hot_haar` averages down `0.512 -> 0.136`).
   - Evidence: `evidence/check5_gb10_run.tsv`, `evidence/check5_gb10_receipt.json` (`window_id: 20261122T204733Z-5ee744`, `103.841 s`, `exit: 0`, `nvrm_errors_delta: 0`).
7. **Formal Lean 4 Bridge (`proofs/UfbiMassGap.lean`)**: Pure zero-dependency Lean 4.36.0 machine-checked proof bridge (`evidence/lean_ufbi_bridge.txt`, `0` errors, `0` warnings, `0` `sorryAx`, standard axioms `[propext, Classical.choice, Quot.sound]` only): `ast_gauge_invariant`, `raw_link_not_gauge_invariant`, `ufbi_implies_connected_clustering`, `exponential_decay_implies_spectral_gap`, `massless_mode_violates_decay`, and `schur_uv_divergence_unbounded`.

> **Scientific scope note:** `proofs/UfbiMassGap.lean` proves the *conditional* mathematical bridge (`UFBI contraction -> connected clustering -> spectral gap > 0`) and exact AST gauge invariance over explicit models; Checks #1, #3, #4, and #5 provide live GB10 empirical lattice evidence. Proving the continuum 4D $SU(N)$ UFBI contraction bound unconditionally as $a \to 0$ remains the open Clay Millennium Problem.

## Build & Run (Spark AArch64 + GB10)

```sh
sh scripts/build_and_run_spark.sh check1
sh scripts/build_and_run_spark.sh obs_synth
sh scripts/build_and_run_spark.sh obs_synth_w2
sh scripts/build_and_run_spark.sh obs_synth_w3
sh scripts/build_and_run_spark.sh check3
sh scripts/build_and_run_spark.sh check4
sh scripts/build_and_run_spark.sh check5
sh scripts/build_and_run_spark.sh proofs
```
