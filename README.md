# `yang`: Pure Seeded-OM-2 + Native GB10 (SM121) UFBI Yang–Mills Mass Gap Falsification, `CentralObs` Discovery & Formal Bridge Suite

Connected repo of [`omega-mv`](https://interplane.io/drakestapleton/omega-mv) (pinned at `3f2c70dc5`, `seed/out/omc` SHA-256 `708fdc0f81866594ed6df2f492b7a8a6bc7456f2d733a838b7f840549ebba6c3`).

Zero C, zero Python, zero Rust, zero `libcuda.so.1` on the execution path: every host driver and native SM121 GPU SASS kernel is compiled directly by `seed/out/omc` into static AArch64 ELF binaries running over `/dev/nvidia*` on DGX Spark GB10.

## Engines, Audits & Formal Bridges

1. **Check #1 (`src/ufbi_check1_gb10.om` + `src/ufbi_check1_kernels.om`)**: 4D massive free scalar UV-divergence test ($L \in \{8, 16, 32, 64\}$, fixed physical $m_{\text{phys}}\ell$), cross-checked against an exact 4D DST-I spectral oracle on $L=8$. Confirms unrestricted all-site Schur-complement TV diverges as $O(L)$ (`TV_raw = 1.0`), whereas smeared `CentralObs` contracts. Evidence: `evidence/check1_gb10_run.tsv`.
2. **Check #2 (`evidence/check2_openai_ym_audit.md`)**: Direct line-referenced Lean 4 audit of [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028) (`PublicTheory.lean`, `ChallengeSpec.lean`, `HierarchyBridge.lean`, `PublicWilson.lean`). Verdict: **COMPATIBLE** — identifies the two exact open seams (`Hierarchy.Character`/`phaseMeasure` and `EnergyMomentumMeasure.projection`).
3. **`CentralObs` Synthesizers — Wave-1 (`src/ufbi_obs_synth.om`), Wave-2 (`src/ufbi_obs_synth_w2.om`), & Wave-3 INV-4 (`src/ufbi_obs_synth_w3.om`)**:
   - Ports `omega-mv`'s pure-OM-2 Observational-Equivalence search (`INV-1` BFS depth barriers, `INV-2` `MAX_PROBES=32` / 70% occupancy cutoff, `INV-3` bounded outputs), **Physics Operator Prior** (`ratio > sub > mul > add`), and **Wake-Sleep Depth-2 Combinator Mining** to 4D $SU(2)$ lattice gauge-invariant observables.
   - **Wave-3 (`INV-4` Pole-Free Guard, `evidence/obs_synth_w3_run.tsv`)**: Evaluates 16 independent MC snapshots across $\beta \in \{2.30, 2.50\}$, rejecting any denominator unless strictly sign-definite with margin $\tau = 0.15$ and condition ratio $\le 4.0$ (`3,752` ASTs, `2,547` equiv-pruned, **`230` pole-prone denominators killed**, `2/2` non-gauge-invariant controls killed). Top winner: pole-free Symanzik-like polynomial `sub(PLAQ1x1_S1, sub(RECT1x2_S0, CHAIR6_S2))` (`gauge_err = 0.000000`, `dTw/sig = 0.045`, `uv_score = 16.153`).
4. **Check #3 (`src/ufbi_check3_gb10.om` + `src/ufbi_check3_kernels.om`)**: Native SM121 quaternion-packed 4D $SU(2)$ lattice Monte Carlo (Kennedy–Pendleton heatbath + exact 4-FMA quaternion overrelaxation on even/odd checkerboard) + Two-Stage Trickster adversarial twisted-collar search with held-out confirmation. Evidence: `evidence/check3_gb10_run.tsv`.
5. **Check #4 (`src/ufbi_check4_gb10.om`) & Erratum**: Live GB10 validation (`evidence/check4_gb10_run.tsv`, `evidence/check4_gb10_receipt.json`, `WID=20261122T202905Z-68a2cb`, `nvrm_errors_delta=0`). Exposed Wave-2's `chi1(ADJ_PLAQ_S0)` zero-denominator pole at $\beta=2.30$. **Erratum on Experiment 4B:** The apparent `64x–113x` drop from `(L=8, β=2.300)` to `(L=16, β=2.575)` in Check #4 was inflated by three lattice artifacts: (i) $L=8$ smearing contact with the frozen collar, (ii) fixed-lattice $a^4$ operator shrinkage as $a \to 0$, and (iii) 2-loop asymptotic scaling overshooting measured non-perturbative $a\sqrt{\sigma}$ scaling ($\beta=2.50$, not $2.575$). **Superseded by Checks #5 and #6.**
6. **Check #5 (`src/ufbi_check5_gb10.om`)**: Contact-free $\beta=2.30$ exponential decay ($L \in \{8, 10, 12, 14, 16\}$, 160 sweeps, `ZERO_CONTACT_ASSERT max_direct_err = 0.000000` on 9/9 geometries) raising fitted decay rates on `C5_nonab_twist` to $a m_{\text{eff}} = 0.587$ (`P1x1_S0`), $0.599$ (`P1x1_S1`), and **`0.763`** (`AdjP_S1`, `13.7x` drop), plus initial 2-point scaled ladder. Evidence: `evidence/check5_gb10_run.tsv`, `evidence/check5_gb10_receipt.json` (`WID=20261122T204733Z-5ee744`, `103.841 s`, `nvrm_errors_delta=0`).
7. **Check #6 (`src/ufbi_check6_gb10.om`) — High-Stats 512-Sweep 3-Point Scaled Continuum Ladder & Out-of-Sample Wave-3 Test**:
   - **3-Point Non-Perturbative $a\sqrt{\sigma}$ Matched Ladder ($\ell\sqrt{\sigma} \approx 2.95$):** `(L=8, β=2.300, 1x1, n_s=1)` $\to$ `(L=12, β=2.426, 1x2, n_s=2)` $\to$ `(L=16, β=2.500, 2x2, n_s=4)`, `512` measurements (`1024` GPU sweeps/arm, 16-block jackknife), `ZERO_CONTACT_ASSERT max_direct_err = 0.000000` on all 6/6 geometries. Physical observable mean stays flat within `1.8%` (`0.862 -> 0.853 -> 0.846`).
   - **Continuum Plateau Confirmed (`> 3.2σ`):** On `C6_trick_vort`, `W_phys` (`O0`) settles to a statistically resolved, flat continuum plateau: `L=12: R_bulk = 0.344 ± 0.107 (3.21σ)` vs `L=16: R_bulk = 0.414 ± 0.109 (3.78σ)` (`0.45σ` flat agreement; zero UV divergence). On `C3_hot_haar`, `R_bulk` drops `0.994 -> 0.254 -> 0.173 (1.92σ)`.
   - **Wave-3 Symanzik Observable (`O2 = P(t1) - (R1x2(0) - Chair6(t2))`, exact physical flow-time matched across $L=8, 12, 16$):** Survives out-of-sample scaling — suppresses confining collar leakage by `9x` relative to `W_phys` at $L=16$ (`C3_hot_haar`: `0.199 -> 0.079 -> 0.016 [0.33σ]`; `C6_trick_vort`: `0.002 -> 0.087 -> 0.046 [0.70σ]`), while **growing monotonically `3.1x`** to **`0.181 (3.09σ)`** on `C3_hot_haar` in the $\beta=6.00$ weak-coupling negative control (`2.20σ` direct $L=16$ split).
   - **Honest high-stats correction on `6C` (`C6_trick_vort` at $\beta=6.00$):** At 512 sweeps, `O0` on `C6_trick_vort` at $\beta=6.00, L=16$ settled to `0.062 (0.76σ)` (showing Check #5's 160-sweep `1.75σ` was finite-sample noise; `C6`'s checkerboard parity alternates at $k=\pi/a$ and is UV-damped in weak coupling, whereas `C3_hot_haar` carries $k=0$ IR power and reaches `3.09σ` on `O2`).
   - Evidence: `evidence/check6_gb10_run.tsv`, `evidence/check6_gb10_receipt.json` (`WID=20261122T210003Z-207467`, `358.502 s`, `exit: 0`, `nvrm_errors_delta: 0`).
8. **Formal Lean 4 Bridges:**
   - **Standalone zero-dependency bridge (`proofs/UfbiMassGap.lean`, Lean `4.36.0`):** `evidence/lean_ufbi_bridge.txt` (`0` errors, `0` warnings, `0` `sorryAx`, `[propext, Classical.choice, Quot.sound]`). Proves `ast_gauge_invariant`, `raw_link_not_gauge_invariant`, `ufbi_implies_connected_clustering`, `exponential_decay_implies_spectral_gap`, `massless_mode_violates_decay`, and `schur_uv_divergence_unbounded`.
   - **Mathlib-linked bridge directly over `OpenAI-YM-20261028` (`proofs/OpenAiYmBridge.lean`, Lean `4.32.0` + cached Mathlib `81a5d257c8e4...`):** Imports `OpenAI-YM-20261028`'s actual `ChallengeSpec.lean` / `PublicWilson.lean` / `PublicTheory.lean` (`WilsonPublic` builds in `12.6 s` with cached `.olean`s; `OpenAiYmBridge.lean` builds in **`2.9 s`**). Evidence: `evidence/lean_openai_ym_bridge.txt` (`0` errors, `0` warnings, `0` `sorryAx`, strictly `[propext, Classical.choice, Quot.sound]`). Proves:
     - `ufbi_collapses_phase_mixture` & `ufbi_collapses_character_space` (`UniformPhaseInsensitivity T` $\implies$ `T.correlation none = T.correlation (some T.selected)`, `Subsingleton T.Character`, and `T.phaseMeasure = Measure.dirac T.selected`),
     - `exponential_decay_kills_energy_strip_measure` & `uniform_decay_implies_energy_gap` (`UniformSpectralDecay T.theory Δ` $\implies$ `T.theory.energyMomentum.projection {p | 0 < time p ∧ time p < Δ} = 0`),
     - `part1_conditional_mass_gap_over_openai_ym` (unified Part I theorem over `ChallengeSpec.Hierarchy`).

> **Scientific scope note:** `proofs/UfbiMassGap.lean` and `proofs/OpenAiYmBridge.lean` prove the *conditional* Part I mathematical bridge (`UFBI / exponential decay -> phase collapse + spectral projection gap > 0`) directly over `OpenAI-YM-20261028`'s verified existence interface; Checks #1, #3, #4, #5, and #6 provide live GB10 empirical lattice evidence. Proving the continuum 4D $SU(N)$ UFBI contraction bound unconditionally as $a \to 0$ (Part II) remains the open Clay Millennium Problem.

## Build & Run (Spark AArch64 + GB10)

```sh
sh scripts/build_and_run_spark.sh check1
sh scripts/build_and_run_spark.sh obs_synth
sh scripts/build_and_run_spark.sh obs_synth_w2
sh scripts/build_and_run_spark.sh obs_synth_w3
sh scripts/build_and_run_spark.sh check3
sh scripts/build_and_run_spark.sh check4
sh scripts/build_and_run_spark.sh check5
sh scripts/build_and_run_spark.sh check6
sh scripts/build_and_run_spark.sh proofs
sh scripts/build_and_run_spark.sh openai_bridge
```
