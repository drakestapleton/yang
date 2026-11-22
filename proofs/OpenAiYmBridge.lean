-- SPDX-License-Identifier: Apache-2.0
-- proofs/OpenAiYmBridge.lean:
-- Mathlib-linked Part I Conditional Yang-Mills Mass Gap & Phase-Collapse Bridge
-- directly over `yang-mills-group/OpenAI-YM-20261028`'s actual public interface
-- (`PublicTheory.lean`, `PublicWilson.lean`, `ChallengeSpec.lean`).
--
-- Scope (explicit scientific honesty):
--   This module machine-checks Part I (the conditional bridge):
--     (A) Uniform phase insensitivity (UFBI on `Hierarchy.correlation`) collapses the
--         extremal-phase mixture `Hierarchy.phaseMeasure` so the unselected Wilson limit
--         `T.correlation none` equals the selected pure phase `T.correlation (some T.selected)`,
--         and under phase extensionality collapses `T.Character` to a singleton with
--         `T.phaseMeasure = Measure.dirac T.selected`.
--     (B) Uniform exponential decay of the Euclidean energy-Laplace transform
--         `∫ p, exp (-t * time p) ∂(energyMomentum.diagonal ψ) ≤ C * exp (-Δ * t)`
--         on vacuum-orthogonal states implies exact vanishing of OpenAI-YM-20261028's
--         actual spectral projection operator:
--           `theory.energyMomentum.projection {p | 0 < time p ∧ time p < Δ} = 0`.
--   Part II (proving uniform continuum UFBI / exponential decay unconditionally for 4D SU(N)
--   Yang-Mills as lattice spacing a -> 0) remains the open Clay Millennium Problem.

import ChallengeSpec

set_option autoImplicit false

noncomputable section

namespace YangMills.UfbiBridge

open MeasureTheory Set Filter Function
open scoped Topology InnerProductSpace

/-! ## Seam 1: UFBI Collapses `Hierarchy.phaseMeasure` and `Hierarchy.Character` -/

/-- Continuum Uniform Finite-Box Insensitivity (UFBI) stated directly on
`OpenAI-YM-20261028`'s local observable hierarchy: every separated correlation
is independent of the extremal phase `i : T.Character`. -/
def UniformPhaseInsensitivity {g : GaugeGroup} {C : WilsonFamily g}
    (T : Hierarchy C) : Prop :=
  ∀ {n : ℕ} (a : Fin n → T.Tag) (x : Points n),
    x ∈ WilsonFamily.separated n →
    ∀ i j : T.Character,
      T.correlation (some i) a x = T.correlation (some j) a x

/-- Phase extensionality: distinct extremal characters are distinguished by at
least one separated local correlation. -/
def CharacterExtensional {g : GaugeGroup} {C : WilsonFamily g}
    (T : Hierarchy C) : Prop :=
  ∀ i j : T.Character,
    (∀ {n : ℕ} (a : Fin n → T.Tag) (x : Points n),
      x ∈ WilsonFamily.separated n →
      T.correlation (some i) a x = T.correlation (some j) a x) →
    i = j

/-- **Theorem 1A (UFBI Phase-Mixture Collapse):**
Under `T.Reconstructed`, `UniformPhaseInsensitivity T` implies that the
unselected Wilson continuum limit `T.correlation none` coincides everywhere on
separated configurations with the selected extremal phase `T.correlation (some T.selected)`. -/
theorem ufbi_collapses_phase_mixture {g : GaugeGroup} {C : WilsonFamily g}
    (T : Hierarchy C) (hRec : T.Reconstructed) (hUfbi : UniformPhaseInsensitivity T)
    {n : ℕ} (a : Fin n → T.Tag) (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    T.correlation none a x = T.correlation (some T.selected) a x := by
  haveI : IsProbabilityMeasure T.phaseMeasure := hRec.normalized
  rw [← hRec.mixture a x hx]
  have hconst : (fun i : T.Character => T.correlation (some i) a x) =
      fun _ => T.correlation (some T.selected) a x := by
    funext i
    exact hUfbi a x hx i T.selected
  rw [hconst, MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]

/-- **Theorem 1B (UFBI Singleton Character & Dirac `phaseMeasure`):**
If extremal characters are separated by local correlations (`CharacterExtensional T`),
then `UniformPhaseInsensitivity T` forces `Subsingleton T.Character` and collapses
`T.phaseMeasure` to `Measure.dirac T.selected`. -/
theorem ufbi_collapses_character_space {g : GaugeGroup} {C : WilsonFamily g}
    (T : Hierarchy C) (hRec : T.Reconstructed)
    (hExt : CharacterExtensional T) (hUfbi : UniformPhaseInsensitivity T) :
    Subsingleton T.Character ∧ T.phaseMeasure = Measure.dirac T.selected := by
  have hSub : Subsingleton T.Character :=
    ⟨fun i j => hExt i j (fun a x hx => hUfbi a x hx i j)⟩
  refine ⟨hSub, ?_⟩
  haveI : Subsingleton T.Character := hSub
  haveI : IsProbabilityMeasure T.phaseMeasure := hRec.normalized
  ext s hs
  by_cases hmem : T.selected ∈ s
  · have huniv : s = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      rwa [Subsingleton.elim y T.selected]
    rw [huniv, measure_univ, measure_univ]
  · have hemp : s = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      rwa [Subsingleton.elim y T.selected]
    rw [hemp, measure_empty, measure_empty]

/-! ## Seam 2: Exponential Laplace Decay Implies Vanishing of `EnergyMomentumMeasure.projection` -/

/-- The open positive-energy strip `0 < p₀ < Δ` in Minkowski momentum space. -/
def energyGapStrip (Δ : ℝ) : Set Spacetime :=
  {p : Spacetime | 0 < YangMills.time p ∧ YangMills.time p < Δ}

/-- Closed sub-strip `0 < p₀ ≤ Δ - ε` used to exhaust `energyGapStrip Δ`. -/
def energySubStrip (Δ ε : ℝ) : Set Spacetime :=
  {p : Spacetime | 0 < YangMills.time p ∧ YangMills.time p ≤ Δ - ε}

/-- Strict spectral energy gap `Δ > 0` stated directly on `OpenAI-YM-20261028`'s
`EnergyMomentumMeasure.projection`. -/
def HasEnergyGap {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (energyGapStrip Δ) = 0

/-- Exponential decay with rate `Δ` of the Euclidean time-translation Laplace
transform of `theory.energyMomentum.diagonal ψ`. -/
def StateLaplaceDecay {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (Δ : ℝ) (ψ : H.carrier) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
    ∫ p, Real.exp (-t * YangMills.time p) ∂(theory.energyMomentum.diagonal ψ) ≤
      C * Real.exp (-Δ * t)

/-- Uniform exponential Laplace decay on all vacuum-orthogonal states, together
with vacuum zero-energy support (`diagonal Ω (energyGapStrip Δ) = 0`). -/
structure UniformSpectralDecay {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop where
  gapPos : 0 < Δ
  vacNoStrip :
    theory.energyMomentum.diagonal theory.fields.vacuum.1 (energyGapStrip Δ) = 0
  orthDecay : ∀ ψ : H.carrier,
    inner ℂ theory.fields.vacuum.1 ψ = 0 → StateLaplaceDecay theory Δ ψ

private lemma continuous_time : Continuous YangMills.time := by
  unfold YangMills.time
  exact PiLp.continuous_apply 2 (fun _ : Axis => ℝ) YangMills.timeAxis

private lemma measurable_time : Measurable YangMills.time :=
  continuous_time.measurable

private lemma measurableSet_forwardCone : MeasurableSet YangMills.forwardCone := by
  have hcont_sp : Continuous YangMills.spatial := by
    unfold YangMills.spatial
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => PiLp.continuous_apply 2 (fun _ : Axis => ℝ) i.castSucc)
  exact isClosed_le hcont_sp.norm continuous_time |>.measurableSet

private lemma measurableSet_energyGapStrip (Δ : ℝ) : MeasurableSet (energyGapStrip Δ) := by
  unfold energyGapStrip
  exact (isOpen_lt continuous_const continuous_time).measurableSet.inter
    (isOpen_lt continuous_time continuous_const).measurableSet

private lemma measurableSet_energySubStrip (Δ ε : ℝ) : MeasurableSet (energySubStrip Δ ε) := by
  unfold energySubStrip
  exact (isOpen_lt continuous_const continuous_time).measurableSet.inter
    (isClosed_le continuous_time continuous_const).measurableSet

/-- From `W0.positiveEnergy`, the diagonal spectral measure `diagonal ψ` assigns
measure zero to `forwardConeᶜ`. -/
lemma diagonal_forwardCone_compl_eq_zero {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0) (ψ : H.carrier) :
    theory.energyMomentum.diagonal ψ YangMills.forwardConeᶜ = 0 := by
  have hId := theory.energyMomentum.diagonalIdentity measurableSet_forwardCone.compl ψ
  rw [hW0.positiveEnergy] at hId
  simp only [zero_apply, inner_zero_right] at hId
  have hreal : (theory.energyMomentum.diagonal ψ).real YangMills.forwardConeᶜ = 0 := by
    exact_mod_cast hId
  have hfin : theory.energyMomentum.diagonal ψ YangMills.forwardConeᶜ ≠ ⊤ :=
    measure_ne_top _ _
  rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hreal
  exact hreal.resolve_right hfin

/-- On `forwardCone`, `0 ≤ time p`. -/
lemma time_nonneg_of_mem_forwardCone {p : Spacetime} (hp : p ∈ YangMills.forwardCone) :
    0 ≤ YangMills.time p :=
  le_trans (norm_nonneg _) hp

/-- Every sub-strip `0 < p₀ ≤ Δ - ε` (`0 < ε < Δ`) has zero `diagonal ψ` measure
whenever `ψ` satisfies `StateLaplaceDecay theory Δ ψ`. -/
lemma diagonal_subStrip_eq_zero {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0)
    {Δ ε : ℝ} (hε : 0 < ε) {ψ : H.carrier}
    (hDec : StateLaplaceDecay theory Δ ψ) :
    theory.energyMomentum.diagonal ψ (energySubStrip Δ ε) = 0 := by
  set μ := theory.energyMomentum.diagonal ψ
  haveI : IsFiniteMeasure μ := theory.energyMomentum.finite ψ
  obtain ⟨C, hC0, hBound⟩ := hDec
  have hSubMeas : MeasurableSet (energySubStrip Δ ε) := measurableSet_energySubStrip Δ ε
  have hComplZero : μ YangMills.forwardConeᶜ = 0 :=
    diagonal_forwardCone_compl_eq_zero theory hW0 ψ
  have hAeNonneg : ∀ᵐ p ∂μ, 0 ≤ YangMills.time p := by
    have hAeMem : ∀ᵐ p ∂μ, p ∈ YangMills.forwardCone := by
      rwa [ae_iff]
    exact hAeMem.mono fun p hp => time_nonneg_of_mem_forwardCone hp
  have hRealLe : ∀ t : ℝ, 0 ≤ t → μ.real (energySubStrip Δ ε) ≤ C * Real.exp (-ε * t) := by
    intro t ht
    have hInt : Integrable (fun p => Real.exp (-t * YangMills.time p)) μ := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_time)).aestronglyMeasurable
      · refine hAeNonneg.mono fun p hp => ?_
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hSetLe :
        Real.exp (-t * (Δ - ε)) * μ.real (energySubStrip Δ ε) ≤
        ∫ p in energySubStrip Δ ε, Real.exp (-t * YangMills.time p) ∂μ := by
      have hConst :
          ∫ _ in energySubStrip Δ ε, Real.exp (-t * (Δ - ε)) ∂μ =
            μ.real (energySubStrip Δ ε) * Real.exp (-t * (Δ - ε)) := by
        rw [setIntegral_const, smul_eq_mul]
      rw [mul_comm, ← hConst]
      refine setIntegral_mono_on (integrableOn_const (hs := measure_ne_top _ _))
        hInt.integrableOn hSubMeas ?_
      intro p hp
      exact Real.exp_le_exp.mpr (by nlinarith [hp.2])
    have hMono :
        ∫ p in energySubStrip Δ ε, Real.exp (-t * YangMills.time p) ∂μ ≤
        ∫ p, Real.exp (-t * YangMills.time p) ∂μ :=
      setIntegral_le_integral hInt (ae_of_all μ fun p => (Real.exp_pos _).le)
    have hChain :
        Real.exp (-t * (Δ - ε)) * μ.real (energySubStrip Δ ε) ≤ C * Real.exp (-Δ * t) :=
      le_trans (le_trans hSetLe hMono) (hBound t ht)
    have hExpPos : 0 < Real.exp (t * (Δ - ε)) := Real.exp_pos _
    have hMul := mul_le_mul_of_nonneg_left hChain hExpPos.le
    have hLhs :
        Real.exp (t * (Δ - ε)) * (Real.exp (-t * (Δ - ε)) * μ.real (energySubStrip Δ ε)) =
          μ.real (energySubStrip Δ ε) := by
      rw [← mul_assoc, ← Real.exp_add]
      have hz : t * (Δ - ε) + -t * (Δ - ε) = 0 := by ring
      rw [hz, Real.exp_zero, one_mul]
    have hRhs :
        Real.exp (t * (Δ - ε)) * (C * Real.exp (-Δ * t)) = C * Real.exp (-ε * t) := by
      calc
        Real.exp (t * (Δ - ε)) * (C * Real.exp (-Δ * t))
            = C * (Real.exp (t * (Δ - ε)) * Real.exp (-Δ * t)) := by ring
        _ = C * Real.exp (t * (Δ - ε) + -Δ * t) := by rw [← Real.exp_add]
        _ = C * Real.exp (-ε * t) := by congr 2; ring
    linarith
  have hRealZero : μ.real (energySubStrip Δ ε) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    have hTend : Tendsto (fun t : ℝ => C * Real.exp (-ε * t)) atTop (𝓝 (C * 0)) := by
      refine tendsto_const_nhds.mul ?_
      have hNeg : Tendsto (fun t : ℝ => -ε * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      exact Real.tendsto_exp_atBot.comp hNeg
    rw [mul_zero] at hTend
    exact ge_of_tendsto hTend (eventually_atTop.mpr ⟨0, hRealLe⟩)
  have hfin : μ (energySubStrip Δ ε) ≠ ⊤ := measure_ne_top _ _
  rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hRealZero
  exact hRealZero.resolve_right hfin

/-- **Theorem 2 (Continuous-Measure Exponential Decay ⇒ Strip Nullity):**
If `ψ` obeys `StateLaplaceDecay theory Δ ψ` with `Δ > 0`, then
`theory.energyMomentum.diagonal ψ (energyGapStrip Δ) = 0`. -/
theorem exponential_decay_kills_energy_strip_measure {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0)
    {Δ : ℝ} (hΔ : 0 < Δ) {ψ : H.carrier}
    (hDec : StateLaplaceDecay theory Δ ψ) :
    theory.energyMomentum.diagonal ψ (energyGapStrip Δ) = 0 := by
  have hUnion :
      energyGapStrip Δ = ⋃ n : ℕ, energySubStrip Δ (Δ / ((n : ℝ) + 2)) := by
    ext p
    simp only [energyGapStrip, energySubStrip, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, hlt⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (Δ / (Δ - YangMills.time p))
      refine ⟨n, h0, ?_⟩
      have hpos : 0 < Δ - YangMills.time p := sub_pos.mpr hlt
      have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hdiv : Δ / ((n : ℝ) + 2) < Δ - YangMills.time p := by
        rw [div_lt_iff₀ hn2]
        have h1 : Δ < (n : ℝ) * (Δ - YangMills.time p) := (div_lt_iff₀ hpos).mp hn
        nlinarith
      linarith
    · rintro ⟨n, h0, hle⟩
      have hpos : 0 < Δ / ((n : ℝ) + 2) := by positivity
      exact ⟨h0, by linarith⟩
  rw [hUnion]
  refine measure_iUnion_null fun n => ?_
  exact diagonal_subStrip_eq_zero theory hW0 (by positivity) hDec

/-- Helper: an orthogonal projection `P` with `inner ℂ ψ (P ψ) = 0` kills `ψ`. -/
private lemma projection_apply_eq_zero_of_diagonal_zero
    {H : HilbertSpace} (E : EnergyMomentumMeasure H)
    {S : Set Spacetime} (hS : MeasurableSet S) (ψ : H.carrier)
    (hZero : E.diagonal ψ S = 0) :
    E.projection S ψ = 0 := by
  have hId := E.diagonalIdentity hS ψ
  have hReal : (E.diagonal ψ).real S = 0 := by
    simp [Measure.real, hZero]
  rw [hReal, Complex.ofReal_zero] at hId
  have hSelf : (E.projection S).adjoint = E.projection S := E.selfAdjoint hS
  have hIdem : (E.projection S).comp (E.projection S) = E.projection S := by
    simpa [Set.inter_self] using E.intersection hS hS
  have hNormSq : inner ℂ (E.projection S ψ) (E.projection S ψ) = 0 := by
    calc
      inner ℂ (E.projection S ψ) (E.projection S ψ)
          = inner ℂ ψ ((E.projection S).adjoint (E.projection S ψ)) := by
            rw [ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ ψ (((E.projection S).comp (E.projection S)) ψ) := by
            rw [hSelf]; rfl
      _ = inner ℂ ψ (E.projection S ψ) := by rw [hIdem]
      _ = 0 := hId.symm
  exact inner_self_eq_zero.mp hNormSq

/-- **Theorem 3 (Uniform Exponential Decay ⇒ Exact Operator Spectral Mass Gap):**
Under `theory.W0`, `theory.W1`, and `UniformSpectralDecay theory Δ`, the actual
joint energy-momentum projection `theory.energyMomentum.projection` vanishes
identically on the open energy strip `0 < p₀ < Δ`. -/
theorem uniform_decay_implies_energy_gap {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0) (hW1 : theory.W1)
    {Δ : ℝ} (hDec : UniformSpectralDecay theory Δ) :
    HasEnergyGap theory Δ := by
  refine ⟨hDec.gapPos, ?_⟩
  have hStripMeas : MeasurableSet (energyGapStrip Δ) := measurableSet_energyGapStrip Δ
  have hVacKill : theory.energyMomentum.projection (energyGapStrip Δ) theory.fields.vacuum.1 = 0 :=
    projection_apply_eq_zero_of_diagonal_zero theory.energyMomentum hStripMeas
      theory.fields.vacuum.1 hDec.vacNoStrip
  ext ψ
  rw [zero_apply]
  set Ω := theory.fields.vacuum.1
  set c : ℂ := inner ℂ Ω ψ
  set ψPerp : H.carrier := ψ - c • Ω
  have hNormΩ : ‖Ω‖ = 1 := hW1.domain.normalizedVacuum
  have hInnerΩ : inner ℂ Ω Ω = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hNormΩ]
    norm_num
  have hOrth : inner ℂ Ω ψPerp = 0 := by
    simp only [ψPerp, inner_sub_right, inner_smul_right, hInnerΩ, mul_one, c, sub_self]
  have hPerpNull :
      theory.energyMomentum.diagonal ψPerp (energyGapStrip Δ) = 0 :=
    exponential_decay_kills_energy_strip_measure theory hW0 hDec.gapPos
      (hDec.orthDecay ψPerp hOrth)
  have hPerpKill : theory.energyMomentum.projection (energyGapStrip Δ) ψPerp = 0 :=
    projection_apply_eq_zero_of_diagonal_zero theory.energyMomentum hStripMeas ψPerp hPerpNull
  have hDecomp : ψ = ψPerp + c • Ω := by
    simp [ψPerp]
  rw [hDecomp, map_add, map_smul, hPerpKill, hVacKill, smul_zero, add_zero]

/-! ## Unified Part I Conditional Theorem Directly Over `OpenAI-YM-20261028` -/

/-- **Headline Part I Theorem over `OpenAI-YM-20261028` (`ChallengeSpec.Hierarchy`):**
Given any reconstructed Yang-Mills continuum hierarchy `T : Hierarchy C` (as produced
by `YangMills.jointExistence`), if:
  1. `UniformPhaseInsensitivity T` (UFBI on the local algebra),
  2. `CharacterExtensional T`, and
  3. `UniformSpectralDecay T.theory Δ`,
then:
  - every separated Wilson continuum correlation equals the selected pure-phase correlation,
  - `T.Character` is a singleton and `T.phaseMeasure = Measure.dirac T.selected`, and
  - `T.theory` has a strict spectral energy gap `Δ > 0` (`projection {0 < p₀ < Δ} = 0`). -/
theorem part1_conditional_mass_gap_over_openai_ym
    {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (hRec : T.Reconstructed)
    (hExt : CharacterExtensional T)
    (hUfbi : UniformPhaseInsensitivity T)
    {Δ : ℝ} (hDec : UniformSpectralDecay T.theory Δ) :
    (∀ {n : ℕ} (a : Fin n → T.Tag) (x : Points n),
      x ∈ WilsonFamily.separated n →
      T.correlation none a x = T.correlation (some T.selected) a x) ∧
    (Subsingleton T.Character ∧ T.phaseMeasure = Measure.dirac T.selected) ∧
    HasEnergyGap T.theory Δ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n a x hx
    exact ufbi_collapses_phase_mixture T hRec hUfbi a x hx
  · exact ufbi_collapses_character_space T hRec hExt hUfbi
  · exact uniform_decay_implies_energy_gap T.theory hRec.axioms.w0 hRec.axioms.w1 hDec

#print axioms ufbi_collapses_phase_mixture
#print axioms ufbi_collapses_character_space
#print axioms exponential_decay_kills_energy_strip_measure
#print axioms uniform_decay_implies_energy_gap
#print axioms part1_conditional_mass_gap_over_openai_ym

end YangMills.UfbiBridge
