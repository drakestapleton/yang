-- SPDX-License-Identifier: Apache-2.0
-- proofs/OpenAiYmBridge.lean:
-- Mathlib-linked Part I Conditional Relativistic Yang-Mills Mass Gap & Phase-Collapse Bridge
-- directly over `yang-mills-group/OpenAI-YM-20261028`'s actual public interface
-- (`PublicTheory.lean`, `PublicWilson.lean`, `ChallengeSpec.lean`).
--
-- Scope (explicit scientific honesty):
--   This module machine-checks Part I (the conditional bridge) with ZERO extra axioms:
--     (A) Seam 1 (`Hierarchy.phaseMeasure` & `Hierarchy.Character`):
--         Uniform phase insensitivity (UFBI on `Hierarchy.correlation`) collapses the
--         extremal-phase mixture so `T.correlation none = T.correlation (some T.selected)`,
--         and under phase extensionality forces `Subsingleton T.Character` and
--         `T.phaseMeasure = Measure.dirac T.selected`.
--     (B) Seam 2 (`EnergyMomentumMeasure.projection` — Exact Relativistic Mass Hyperboloid):
--         Uniform exponential decay of the Euclidean energy-Laplace transform on
--         vacuum-orthogonal states implies:
--           1. Energy-strip gap: `projection {p | 0 < time p ∧ time p < Δ} = 0`, AND
--           2. Exact Lorentz-invariant relativistic mass hyperboloid gap (derived purely
--              from `W0.spectralRepresentation`, `W1`, and `PoincareAction` via explicit
--              proper orthochronous Lorentz boosts + `Measure.ext_of_charFun`):
--                `projection {p ∈ forwardCone | p ≠ 0 ∧ minkowskiSquare p < Δ^2} = 0`.
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

/-! ## Seam 2A: Exponential Laplace Decay Implies Energy-Strip Gap (`0 < p₀ < Δ`) -/

/-- The open positive-energy strip `0 < p₀ < Δ` in Minkowski momentum space. -/
def energyGapStrip (Δ : ℝ) : Set Spacetime :=
  {p : Spacetime | 0 < YangMills.time p ∧ YangMills.time p < Δ}

/-- Closed sub-strip `0 < p₀ ≤ Δ - ε` used to exhaust `energyGapStrip Δ`. -/
def energySubStrip (Δ ε : ℝ) : Set Spacetime :=
  {p : Spacetime | 0 < YangMills.time p ∧ YangMills.time p ≤ Δ - ε}

/-- The exact Lorentz-invariant relativistic mass-gap region in `PublicTheory.lean`:
all non-zero momentum vectors in the closed forward light cone with invariant mass
squared strictly below `Δ^2` (covering both massless `p^2 = 0, p ≠ 0` and sub-gap
massive `0 < p^2 < Δ^2` states). -/
def massGapHyperboloid (Δ : ℝ) : Set Spacetime :=
  {p : Spacetime | p ∈ YangMills.forwardCone ∧ p ≠ 0 ∧ YangMills.minkowskiSquare p < Δ ^ 2}

/-- Strict spectral energy-strip gap `Δ > 0`. -/
def HasEnergyGap {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (energyGapStrip Δ) = 0

/-- Exact Lorentz-invariant relativistic Clay Mass Gap stated directly on
`OpenAI-YM-20261028`'s `EnergyMomentumMeasure.projection`. -/
def HasRelativisticMassGap {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧ theory.energyMomentum.projection (massGapHyperboloid Δ) = 0

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

private lemma continuous_spatial : Continuous YangMills.spatial := by
  unfold YangMills.spatial
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => PiLp.continuous_apply 2 (fun _ : Axis => ℝ) i.castSucc)

private lemma continuous_minkowskiSquare : Continuous YangMills.minkowskiSquare := by
  unfold YangMills.minkowskiSquare
  exact (continuous_time.pow 2).sub (continuous_spatial.norm.pow 2)

private lemma measurableSet_forwardCone : MeasurableSet YangMills.forwardCone :=
  (isClosed_le continuous_spatial.norm continuous_time).measurableSet

private lemma isOpen_energyGapStrip (Δ : ℝ) : IsOpen (energyGapStrip Δ) := by
  unfold energyGapStrip
  exact (isOpen_lt continuous_const continuous_time).inter
    (isOpen_lt continuous_time continuous_const)

private lemma measurableSet_energyGapStrip (Δ : ℝ) : MeasurableSet (energyGapStrip Δ) :=
  (isOpen_energyGapStrip Δ).measurableSet

private lemma measurableSet_energySubStrip (Δ ε : ℝ) : MeasurableSet (energySubStrip Δ ε) := by
  unfold energySubStrip
  exact (isOpen_lt continuous_const continuous_time).measurableSet.inter
    (isClosed_le continuous_time continuous_const).measurableSet

private lemma measurableSet_massGapHyperboloid (Δ : ℝ) :
    MeasurableSet (massGapHyperboloid Δ) := by
  unfold massGapHyperboloid
  have hne : MeasurableSet {p : Spacetime | p ≠ 0} :=
    (isClosed_singleton (x := (0 : Spacetime))).isOpen_compl.measurableSet
  have hlt : MeasurableSet {p : Spacetime | YangMills.minkowskiSquare p < Δ ^ 2} :=
    (isOpen_lt continuous_minkowskiSquare continuous_const).measurableSet
  exact measurableSet_forwardCone.inter (hne.inter hlt)

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

/-- Translation covariance fixes the normalized vacuum. Its characteristic function
is identically one, so its energy–momentum measure is the point mass at zero. -/
theorem vacuum_diagonal_eq_dirac {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2) :
    T.energyMomentum.diagonal T.fields.vacuum.1 = Measure.dirac 0 := by
  haveI := T.energyMomentum.finite T.fields.vacuum.1
  apply Measure.ext_of_charFun
  funext x
  rw [hW0.spectralRepresentation, ← T.translationCompatibility,
    hW2.vacuumInvariant, inner_self_eq_norm_sq_to_K, hW1.domain.normalizedVacuum]
  simp [charFun_dirac]

theorem vacuum_diagonal_energyGapStrip {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2) (Δ : ℝ) :
    T.energyMomentum.diagonal T.fields.vacuum.1 (energyGapStrip Δ) = 0 := by
  rw [vacuum_diagonal_eq_dirac T hW0 hW1 hW2, Measure.dirac_apply' _ (measurableSet_energyGapStrip Δ)]
  simp [energyGapStrip,YangMills.time]

#print axioms vacuum_diagonal_eq_dirac
#print axioms vacuum_diagonal_energyGapStrip

/-- Positivity of the diagonal spectral measure bounds the mass in a low-energy
strip using a single Euclidean time. -/
theorem diagonal_subStrip_le_laplace {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0) (ψ : H.carrier)
    (Δ ε t : ℝ) (ht : 0 ≤ t) :
    (theory.energyMomentum.diagonal ψ).real (energySubStrip Δ ε) ≤
      Real.exp ((Δ-ε)*t) * ∫ p, Real.exp (-t * YangMills.time p) ∂(theory.energyMomentum.diagonal ψ) := by
  set μ := theory.energyMomentum.diagonal ψ
  haveI : IsFiniteMeasure μ := theory.energyMomentum.finite ψ
  have hSubMeas : MeasurableSet (energySubStrip Δ ε) := measurableSet_energySubStrip Δ ε
  have hComplZero : μ YangMills.forwardConeᶜ = 0 :=
    diagonal_forwardCone_compl_eq_zero theory hW0 ψ
  have hAeNonneg : ∀ᵐ p ∂μ, 0 ≤ YangMills.time p := by
    have hAeMem : ∀ᵐ p ∂μ, p ∈ YangMills.forwardCone := by
      rwa [ae_iff]
    exact hAeMem.mono fun p hp => time_nonneg_of_mem_forwardCone hp
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
  have he := mul_le_mul_of_nonneg_left (hSetLe.trans hMono) (Real.exp_pos ((Δ-ε)*t)).le
  rwa [← mul_assoc, ← Real.exp_add, show (Δ-ε)*t + -t*(Δ-ε) = 0 by ring,
    Real.exp_zero, one_mul] at he

private theorem energyGapStrip_eq_iUnion {Δ : ℝ} (hΔ : 0 < Δ) :
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

/-- Exponential upper bounds are sufficient along any sequence of times going
to infinity. The prefactor and the time sequence may depend on the vector. -/
theorem sparse_decay_kills_energy_strip {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0) (ψ : H.carrier)
    {Δ C : ℝ} (hΔ : 0 < Δ) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hbound : ∀ᶠ j in atTop, (∫ p, Real.exp (-t j * YangMills.time p) ∂(theory.energyMomentum.diagonal ψ))
      ≤ C * Real.exp (-Δ*t j)) :
    theory.energyMomentum.diagonal ψ (energyGapStrip Δ) = 0 := by
  rw [energyGapStrip_eq_iUnion hΔ]
  apply measure_iUnion_null
  intro n
  let ε := Δ/((n:ℝ)+2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let μ := theory.energyMomentum.diagonal ψ
  have vanish : Tendsto (fun j => C * Real.exp (-ε*t j)) atTop (𝓝 (C*0)) :=
    tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (neg_neg_of_pos hε)))
  rw [mul_zero] at vanish
  have hz : μ.real (energySubStrip Δ ε) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    apply ge_of_tendsto vanish
    filter_upwards [ht.eventually_ge_atTop 0, hbound] with j hj hb
    apply (diagonal_subStrip_le_laplace theory hW0 ψ Δ ε (t j) hj).trans
    calc _ ≤ Real.exp ((Δ-ε)*t j) * (C * Real.exp (-Δ*t j)) :=
           mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
         _ = C * Real.exp (-ε*t j) := by
           rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  haveI : IsFiniteMeasure μ := theory.energyMomentum.finite ψ
  rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hz
  exact hz.resolve_right (measure_ne_top _ _)

/-- Every closed sub-strip below the decay rate has zero diagonal measure. -/
lemma diagonal_subStrip_eq_zero {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0)
    {Δ ε : ℝ} (hε : 0 < ε) {ψ : H.carrier}
    (hDec : StateLaplaceDecay theory Δ ψ) :
    theory.energyMomentum.diagonal ψ (energySubStrip Δ ε) = 0 := by
  by_cases hΔ : 0 < Δ
  · obtain ⟨C,_,hb⟩ := hDec
    have hz := sparse_decay_kills_energy_strip theory hW0 ψ hΔ (fun j => (j:ℝ))
      tendsto_natCast_atTop_atTop (.of_forall fun j => hb _ (Nat.cast_nonneg j))
    have hsub : energySubStrip Δ ε ⊆ energyGapStrip Δ :=
      fun _ hp => ⟨hp.1,lt_of_le_of_lt hp.2 (sub_lt_self Δ hε)⟩
    exact measure_mono_null hsub hz
  · have hempty : energySubStrip Δ ε = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro p ⟨hp,hp'⟩
      linarith
    rw [hempty, measure_empty]

/-- Exponential decay of a state's Laplace transform excludes the open energy strip. -/
theorem exponential_decay_kills_energy_strip_measure {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0)
    {Δ : ℝ} (hΔ : 0 < Δ) {ψ : H.carrier}
    (hDec : StateLaplaceDecay theory Δ ψ) :
    theory.energyMomentum.diagonal ψ (energyGapStrip Δ) = 0 := by
  obtain ⟨C,_,hb⟩ := hDec
  exact sparse_decay_kills_energy_strip theory hW0 ψ hΔ (fun j => (j:ℝ))
    tendsto_natCast_atTop_atTop (.of_forall fun j => hb _ (Nat.cast_nonneg j))

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

/-- **Theorem 3 (Uniform Exponential Decay ⇒ Energy-Strip Projection Gap):**
Under `theory.W0`, `theory.W1`, and `UniformSpectralDecay theory Δ`, the
spectral projection vanishes on `energyGapStrip Δ`. -/
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

/-! ## Seam 2B: Relativistic Boost Upgrade (`energyGapStrip Δ` ⇒ `massGapHyperboloid Δ`) -/

/-- Reconstruct a `Spacetime` vector from `(time, spatial)` components. -/
private def mkSpacetime (t : ℝ) (s : Space) : Spacetime :=
  WithLp.toLp 2 (Fin.lastCases (motive := fun _ => ℝ) t s.ofLp)

private lemma time_mkSpacetime (t : ℝ) (s : Space) :
    YangMills.time (mkSpacetime t s) = t := by
  dsimp only [YangMills.time, mkSpacetime, YangMills.timeAxis]
  exact Fin.lastCases_last

private lemma spatial_mkSpacetime (t : ℝ) (s : Space) :
    YangMills.spatial (mkSpacetime t s) = s := by
  ext i
  dsimp only [YangMills.spatial, mkSpacetime]
  exact Fin.lastCases_castSucc i

private lemma mkSpacetime_eta (v : Spacetime) :
    mkSpacetime (YangMills.time v) (YangMills.spatial v) = v := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · exact time_mkSpacetime (YangMills.time v) (YangMills.spatial v)
  · intro j
    exact congrArg (fun s : Space => s.ofLp j)
      (spatial_mkSpacetime (YangMills.time v) (YangMills.spatial v))

private lemma mkSpacetime_add (t₁ t₂ : ℝ) (s₁ s₂ : Space) :
    mkSpacetime (t₁ + t₂) (s₁ + s₂) = mkSpacetime t₁ s₁ + mkSpacetime t₂ s₂ := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · exact (time_mkSpacetime (t₁ + t₂) (s₁ + s₂)).trans
      (by rw [← time_mkSpacetime t₁ s₁, ← time_mkSpacetime t₂ s₂]; rfl)
  · intro j
    have hL := congrArg (fun s : Space => s.ofLp j) (spatial_mkSpacetime (t₁ + t₂) (s₁ + s₂))
    have h1 := congrArg (fun s : Space => s.ofLp j) (spatial_mkSpacetime t₁ s₁)
    have h2 := congrArg (fun s : Space => s.ofLp j) (spatial_mkSpacetime t₂ s₂)
    change (YangMills.spatial (mkSpacetime (t₁ + t₂) (s₁ + s₂))).ofLp j =
      (YangMills.spatial (mkSpacetime t₁ s₁)).ofLp j + (YangMills.spatial (mkSpacetime t₂ s₂)).ofLp j
    rw [hL, h1, h2]; rfl

private lemma mkSpacetime_smul (c t : ℝ) (s : Space) :
    mkSpacetime (c * t) (c • s) = c • mkSpacetime t s := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · exact (time_mkSpacetime (c * t) (c • s)).trans
      (by rw [← time_mkSpacetime t s]; rfl)
  · intro j
    have hL := congrArg (fun s : Space => s.ofLp j) (spatial_mkSpacetime (c * t) (c • s))
    have h1 := congrArg (fun s : Space => s.ofLp j) (spatial_mkSpacetime t s)
    change (YangMills.spatial (mkSpacetime (c * t) (c • s))).ofLp j =
      c * (YangMills.spatial (mkSpacetime t s)).ofLp j
    rw [hL, h1]; rfl

private lemma time_add (v w : Spacetime) :
    YangMills.time (v + w) = YangMills.time v + YangMills.time w := rfl

private lemma time_smul (c : ℝ) (v : Spacetime) :
    YangMills.time (c • v) = c * YangMills.time v := rfl

private lemma spatial_add (v w : Spacetime) :
    YangMills.spatial (v + w) = YangMills.spatial v + YangMills.spatial w := by
  ext i; rfl

private lemma spatial_smul (c : ℝ) (v : Spacetime) :
    YangMills.spatial (c • v) = c • YangMills.spatial v := by
  ext i; rfl

private lemma spacetime_inner_eq (x y : Spacetime) :
    inner ℝ x y = YangMills.time x * YangMills.time y + inner ℝ (YangMills.spatial x) (YangMills.spatial y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, Fin.sum_univ_succAbove _ (Fin.last 3)]
  have h1 : y.ofLp (Fin.last 3) * x.ofLp (Fin.last 3) = YangMills.time x * YangMills.time y :=
    mul_comm _ _
  rw [h1]
  congr 1

/-- Explicit pure Lorentz boost along spatial unit vector `u` with rapidity `η`. -/
private def boostLM (u : Space) (η : ℝ) : Spacetime →ₗ[ℝ] Spacetime where
  toFun v :=
    let t := YangMills.time v
    let s := YangMills.spatial v
    let proj := inner ℝ u s
    mkSpacetime (Real.cosh η * t - Real.sinh η * proj)
      (s + ((Real.cosh η - 1) * proj - Real.sinh η * t) • u)
  map_add' v w := by
    simp only [time_add, spatial_add, inner_add_right]
    rw [← mkSpacetime_add]
    congr 1
    · ring
    · rw [add_add_add_comm, ← add_smul]
      congr 2
      ring
  map_smul' c v := by
    simp only [time_smul, spatial_smul, inner_smul_right, RingHom.id_apply]
    rw [← mkSpacetime_smul]
    congr 1
    · ring
    · rw [smul_add, smul_smul]
      congr 2
      ring

private lemma boostLM_time (u : Space) (η : ℝ) (v : Spacetime) :
    YangMills.time (boostLM u η v) =
      Real.cosh η * YangMills.time v - Real.sinh η * inner ℝ u (YangMills.spatial v) :=
  time_mkSpacetime _ _

private lemma boostLM_spatial (u : Space) (η : ℝ) (v : Spacetime) :
    YangMills.spatial (boostLM u η v) =
      YangMills.spatial v +
        ((Real.cosh η - 1) * inner ℝ u (YangMills.spatial v) - Real.sinh η * YangMills.time v) • u :=
  spatial_mkSpacetime _ _

private lemma boostLM_zero (u : Space) : boostLM u 0 = LinearMap.id := by
  ext v i
  have ht : YangMills.time (boostLM u 0 v) = YangMills.time v := by
    rw [boostLM_time, Real.cosh_zero, Real.sinh_zero]; ring
  have hs : YangMills.spatial (boostLM u 0 v) = YangMills.spatial v := by
    rw [boostLM_spatial, Real.cosh_zero, Real.sinh_zero]; simp
  have hv : boostLM u 0 v = v := by
    rw [← mkSpacetime_eta (boostLM u 0 v), ht, hs, mkSpacetime_eta]
  simpa using congrArg (fun z : Spacetime => z i) hv

private lemma boostLM_comp {u : Space} (hu : ‖u‖ = 1) (η₁ η₂ : ℝ) :
    (boostLM u η₁).comp (boostLM u η₂) = boostLM u (η₁ + η₂) := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  ext v i
  have hproj2 :
      inner ℝ u (YangMills.spatial (boostLM u η₂ v)) =
        Real.cosh η₂ * inner ℝ u (YangMills.spatial v) - Real.sinh η₂ * YangMills.time v := by
    rw [boostLM_spatial, inner_add_right, inner_smul_right, huu, mul_one]
    ring
  have ht :
      YangMills.time (boostLM u η₁ (boostLM u η₂ v)) =
        YangMills.time (boostLM u (η₁ + η₂) v) := by
    rw [boostLM_time, boostLM_time, hproj2, boostLM_time, Real.cosh_add, Real.sinh_add]
    ring
  have hs :
      YangMills.spatial (boostLM u η₁ (boostLM u η₂ v)) =
        YangMills.spatial (boostLM u (η₁ + η₂) v) := by
    rw [boostLM_spatial, hproj2, boostLM_spatial, boostLM_time, boostLM_spatial,
      add_assoc, ← add_smul, Real.cosh_add, Real.sinh_add]
    congr 2
    ring
  have heq : boostLM u η₁ (boostLM u η₂ v) = boostLM u (η₁ + η₂) v := by
    rw [← mkSpacetime_eta (boostLM u η₁ (boostLM u η₂ v)), ht, hs, mkSpacetime_eta]
  simpa [LinearMap.comp_apply] using congrArg (fun z : Spacetime => z i) heq

private lemma boostLM_selfAdjoint (u : Space) (η : ℝ) (x y : Spacetime) :
    inner ℝ (boostLM u η x) y = inner ℝ x (boostLM u η y) := by
  rw [spacetime_inner_eq, spacetime_inner_eq, boostLM_time, boostLM_spatial,
    boostLM_time, boostLM_spatial, inner_add_left, inner_smul_left,
    inner_add_right, inner_smul_right, real_inner_comm (YangMills.spatial x) u,
    real_inner_comm (YangMills.spatial y) u]
  simp only [conj_trivial]
  ring

private lemma boostLM_minkowskiSquare {u : Space} (hu : ‖u‖ = 1) (η : ℝ) (v : Spacetime) :
    YangMills.minkowskiSquare (boostLM u η v) = YangMills.minkowskiSquare v := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hcs : Real.cosh η ^ 2 - Real.sinh η ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq η
  unfold YangMills.minkowskiSquare
  rw [boostLM_time, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, boostLM_spatial,
    inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, huu, real_inner_comm (YangMills.spatial v) u]
  simp only [conj_trivial, mul_one]
  set t := YangMills.time v
  set p := inner ℝ (YangMills.spatial v) u
  have key :
      (Real.cosh η * t - Real.sinh η * p) ^ 2 -
        (inner ℝ (YangMills.spatial v) (YangMills.spatial v) +
          ((Real.cosh η - 1) * p - Real.sinh η * t) * p +
          (((Real.cosh η - 1) * p - Real.sinh η * t) * p +
            ((Real.cosh η - 1) * p - Real.sinh η * t) *
              ((Real.cosh η - 1) * p - Real.sinh η * t)))
      = t ^ 2 - inner ℝ (YangMills.spatial v) (YangMills.spatial v)
        + (Real.cosh η ^ 2 - Real.sinh η ^ 2 - 1) * (t ^ 2 - p ^ 2) := by ring
  rw [key, hcs]
  ring

private lemma boostLM_forwardCone_imp {u : Space} (hu : ‖u‖ = 1) (η : ℝ) {v : Spacetime}
    (hv : v ∈ YangMills.forwardCone) : boostLM u η v ∈ YangMills.forwardCone := by
  change ‖YangMills.spatial (boostLM u η v)‖ ≤ YangMills.time (boostLM u η v)
  have hv_le : ‖YangMills.spatial v‖ ≤ YangMills.time v := hv
  have ht_nonneg : 0 ≤ YangMills.time v := le_trans (norm_nonneg _) hv_le
  have hproj_abs : |inner ℝ u (YangMills.spatial v)| ≤ YangMills.time v := by
    calc
      |inner ℝ u (YangMills.spatial v)| ≤ ‖u‖ * ‖YangMills.spatial v‖ :=
        abs_real_inner_le_norm u (YangMills.spatial v)
      _ = ‖YangMills.spatial v‖ := by rw [hu, one_mul]
      _ ≤ YangMills.time v := hv_le
  have hcosh_pos : 0 < Real.cosh η := Real.cosh_pos η
  have hsinh_le : |Real.sinh η| ≤ Real.cosh η := by
    have h1 : Real.sinh η ^ 2 ≤ Real.cosh η ^ 2 := by
      have := Real.cosh_sq_sub_sinh_sq η; nlinarith
    have h2 : |Real.sinh η| ≤ |Real.cosh η| := sq_le_sq.mp h1
    rwa [abs_of_pos hcosh_pos] at h2
  have ht'_nonneg : 0 ≤ YangMills.time (boostLM u η v) := by
    rw [boostLM_time]
    have hprod : Real.sinh η * inner ℝ u (YangMills.spatial v) ≤ Real.cosh η * YangMills.time v := by
      calc
        Real.sinh η * inner ℝ u (YangMills.spatial v)
            ≤ |Real.sinh η * inner ℝ u (YangMills.spatial v)| := le_abs_self _
        _ = |Real.sinh η| * |inner ℝ u (YangMills.spatial v)| := abs_mul _ _
        _ ≤ Real.cosh η * YangMills.time v :=
          mul_le_mul hsinh_le hproj_abs (abs_nonneg _) hcosh_pos.le
    linarith
  have hmk : YangMills.minkowskiSquare (boostLM u η v) = YangMills.minkowskiSquare v :=
    boostLM_minkowskiSquare hu η v
  have hv_mk : 0 ≤ YangMills.minkowskiSquare v := by
    unfold YangMills.minkowskiSquare
    nlinarith [norm_nonneg (YangMills.spatial v)]
  have hsq : ‖YangMills.spatial (boostLM u η v)‖ ^ 2 ≤ YangMills.time (boostLM u η v) ^ 2 := by
    unfold YangMills.minkowskiSquare at hmk hv_mk
    linarith
  nlinarith [norm_nonneg (YangMills.spatial (boostLM u η v))]

private lemma boostLM_forwardCone_iff {u : Space} (hu : ‖u‖ = 1) (η : ℝ) (v : Spacetime) :
    boostLM u η v ∈ YangMills.forwardCone ↔ v ∈ YangMills.forwardCone := by
  constructor
  · intro h
    have hback := boostLM_forwardCone_imp hu (-η) h
    have hcomp : boostLM u (-η) (boostLM u η v) = v := by
      have h1 := congrArg (fun f => f v) (boostLM_comp hu (-η) η)
      simp only [LinearMap.comp_apply, neg_add_cancel, boostLM_zero, LinearMap.id_apply] at h1
      exact h1
    rwa [hcomp] at hback
  · exact boostLM_forwardCone_imp hu η

/-- Parity involution `J (t, s) = (t, -s)`, used for the algebraic proof of `det(boost) = 1`. -/
private def parityLM : Spacetime →ₗ[ℝ] Spacetime where
  toFun v := mkSpacetime (YangMills.time v) (-YangMills.spatial v)
  map_add' v w := by
    simp only [time_add, spatial_add, neg_add]
    exact mkSpacetime_add _ _ _ _
  map_smul' c v := by
    simp only [time_smul, spatial_smul, RingHom.id_apply, ← smul_neg]
    exact mkSpacetime_smul _ _ _

private lemma parityLM_comp_self : parityLM.comp parityLM = LinearMap.id := by
  ext v i
  have ht : YangMills.time (parityLM (parityLM v)) = YangMills.time v := by
    simp [parityLM, time_mkSpacetime]
  have hs : YangMills.spatial (parityLM (parityLM v)) = YangMills.spatial v := by
    simp [parityLM, spatial_mkSpacetime]
  have heq : parityLM (parityLM v) = v := by
    rw [← mkSpacetime_eta (parityLM (parityLM v)), ht, hs, mkSpacetime_eta]
  simpa [LinearMap.comp_apply] using congrArg (fun z : Spacetime => z i) heq

private lemma parityLM_conj_boost (u : Space) (η : ℝ) :
    parityLM.comp ((boostLM u η).comp parityLM) = boostLM u (-η) := by
  ext v i
  have ht : YangMills.time (parityLM (boostLM u η (parityLM v))) = YangMills.time (boostLM u (-η) v) := by
    simp only [parityLM, LinearMap.coe_mk, AddHom.coe_mk, time_mkSpacetime, spatial_mkSpacetime,
      boostLM_time, inner_neg_right, Real.cosh_neg, Real.sinh_neg]
    ring
  have hs : YangMills.spatial (parityLM (boostLM u η (parityLM v))) = YangMills.spatial (boostLM u (-η) v) := by
    simp only [parityLM, LinearMap.coe_mk, AddHom.coe_mk, time_mkSpacetime, spatial_mkSpacetime,
      boostLM_spatial, inner_neg_right, Real.cosh_neg, Real.sinh_neg, neg_add, neg_neg, ← neg_smul]
    congr 2
    ring
  have heq : parityLM (boostLM u η (parityLM v)) = boostLM u (-η) v := by
    rw [← mkSpacetime_eta (parityLM (boostLM u η (parityLM v))), ht, hs, mkSpacetime_eta]
  simpa [LinearMap.comp_apply] using congrArg (fun z : Spacetime => z i) heq

private lemma boostLM_det {u : Space} (hu : ‖u‖ = 1) (η : ℝ) :
    LinearMap.det (boostLM u η) = 1 := by
  have hJsq : LinearMap.det parityLM * LinearMap.det parityLM = 1 := by
    rw [← LinearMap.det_comp, parityLM_comp_self, LinearMap.det_id]
  have hNeg : LinearMap.det (boostLM u (-η)) = LinearMap.det (boostLM u η) := by
    have h1 := congrArg LinearMap.det (parityLM_conj_boost u η)
    rw [LinearMap.det_comp, LinearMap.det_comp] at h1
    have h2 :
        LinearMap.det parityLM * (LinearMap.det (boostLM u η) * LinearMap.det parityLM) =
          (LinearMap.det parityLM * LinearMap.det parityLM) * LinearMap.det (boostLM u η) := by
      ring
    rw [h2, hJsq, one_mul] at h1
    exact h1.symm
  have hSq : LinearMap.det (boostLM u η) * LinearMap.det (boostLM u η) = 1 := by
    have h1 := congrArg LinearMap.det (boostLM_comp hu η (-η))
    rw [LinearMap.det_comp, add_neg_cancel, boostLM_zero, LinearMap.det_id, hNeg] at h1
    exact h1
  have hNonneg : 0 ≤ LinearMap.det (boostLM u η) := by
    have hhalf : η / 2 + η / 2 = η := by ring
    have h1 := congrArg LinearMap.det (boostLM_comp hu (η / 2) (η / 2))
    rw [LinearMap.det_comp, hhalf] at h1
    nlinarith
  nlinarith

/-- Package `boostLM u η` as an element of `OpenAI-YM-20261028`'s `YangMills.ProperLorentz`. -/
private def properBoost {u : Space} (hu : ‖u‖ = 1) (η : ℝ) : YangMills.ProperLorentz := by
  let f : Spacetime →L[ℝ] Spacetime := (boostLM u η).toContinuousLinearMap
  let g : Spacetime →L[ℝ] Spacetime := (boostLM u (-η)).toContinuousLinearMap
  have hfg : f * g = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have h1 := congrArg (fun m => m v) (boostLM_comp hu η (-η))
    simpa [f, g, LinearMap.comp_apply, boostLM_zero] using h1
  have hgf : g * f = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have h1 := congrArg (fun m => m v) (boostLM_comp hu (-η) η)
    simpa [f, g, LinearMap.comp_apply, boostLM_zero] using h1
  refine ⟨⟨f, g, hfg, hgf⟩, ?_, ?_, ?_⟩
  · exact boostLM_det hu η
  · exact boostLM_minkowskiSquare hu η
  · exact boostLM_forwardCone_iff hu η

/-- Unitary operators preserve the complex inner product (via polarization). -/
private lemma inner_unitary {H : HilbertSpace} (U : H.Operator)
    (hU : ∀ x : H.carrier, ‖U x‖ = ‖x‖) (x y : H.carrier) :
    inner ℂ (U x) (U y) = inner ℂ x y := by
  let iso : H.carrier →ₗᵢ[ℂ] H.carrier :=
    { toLinearMap := U.toLinearMap
      norm_map' := hU }
  exact iso.inner_map_map x y

/-- **Lorentz Covariance of `EnergyMomentumMeasure.diagonal` under symmetric boosts**
(derived directly from `W0.spectralRepresentation` + `PoincareAction` + `Measure.ext_of_charFun`,
requiring ZERO extra axioms beyond `PublicTheory.lean`). -/
lemma diagonal_map_properBoost {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0)
    {u : Space} (hu : ‖u‖ = 1) (η : ℝ) (ψ : H.carrier) :
    (theory.energyMomentum.diagonal ψ).map (boostLM u η) =
      theory.energyMomentum.diagonal
        (theory.poincare.onStates (theory.poincare.coordinates.symm (properBoost hu (-η), 0)) ψ) := by
  set Λ : YangMills.ProperLorentz := properBoost hu η
  set ΛInv : YangMills.ProperLorentz := properBoost hu (-η)
  set gΛ : theory.poincare.Symmetry := theory.poincare.coordinates.symm (Λ, 0)
  set gΛInv : theory.poincare.Symmetry := theory.poincare.coordinates.symm (ΛInv, 0)
  have hgΛ_coords : theory.poincare.coordinates gΛ = (Λ, 0) :=
    theory.poincare.coordinates.apply_symm_apply _
  have hgΛInv_coords : theory.poincare.coordinates gΛInv = (ΛInv, 0) :=
    theory.poincare.coordinates.apply_symm_apply _
  have hΛ_mul : Λ.val * ΛInv.val = 1 := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro v
    have h1 := congrArg (fun m => m v) (boostLM_comp hu η (-η))
    simpa [Λ, ΛInv, properBoost, LinearMap.comp_apply, boostLM_zero] using h1
  have hmul_id : gΛ * gΛInv = 1 := by
    apply theory.poincare.coordinates.injective
    apply Prod.ext
    · apply Subtype.ext
      have h1 := (theory.poincare.productCoordinates gΛ gΛInv).1
      rw [hgΛ_coords, hgΛInv_coords] at h1
      rw [h1, theory.poincare.identityCoordinates.1]
      exact hΛ_mul
    · have h2 := (theory.poincare.productCoordinates gΛ gΛInv).2
      rw [hgΛ_coords, hgΛInv_coords] at h2
      rw [h2, theory.poincare.identityCoordinates.2, map_zero, add_zero]
  have hconj : ∀ x : Spacetime,
      gΛ * theory.poincare.pureTranslation x =
        theory.poincare.pureTranslation (Λ.val.val x) * gΛ := by
    intro x
    apply theory.poincare.coordinates.injective
    apply Prod.ext
    · apply Subtype.ext
      have hl := (theory.poincare.productCoordinates gΛ (theory.poincare.pureTranslation x)).1
      have hr := (theory.poincare.productCoordinates (theory.poincare.pureTranslation (Λ.val.val x)) gΛ).1
      rw [hgΛ_coords, (theory.poincare.translationCoordinates x).1] at hl
      rw [hgΛ_coords, (theory.poincare.translationCoordinates (Λ.val.val x)).1] at hr
      rw [hl, hr, mul_one, one_mul]
    · have hl := (theory.poincare.productCoordinates gΛ (theory.poincare.pureTranslation x)).2
      have hr := (theory.poincare.productCoordinates (theory.poincare.pureTranslation (Λ.val.val x)) gΛ).2
      rw [hgΛ_coords, (theory.poincare.translationCoordinates x).2] at hl
      rw [hgΛ_coords, (theory.poincare.translationCoordinates (Λ.val.val x)).1,
        (theory.poincare.translationCoordinates (Λ.val.val x)).2] at hr
      simp only [Units.val_one, map_zero, add_zero, zero_add] at hl hr
      rw [hl, hr]
  haveI : IsFiniteMeasure (theory.energyMomentum.diagonal ψ) :=
    theory.energyMomentum.finite ψ
  haveI : IsFiniteMeasure (theory.energyMomentum.diagonal (theory.poincare.onStates gΛInv ψ)) :=
    theory.energyMomentum.finite _
  have hContB : Continuous (boostLM u η) := (boostLM u η).continuous_of_finiteDimensional
  haveI : IsFiniteMeasure ((theory.energyMomentum.diagonal ψ).map (boostLM u η)) :=
    Measure.isFiniteMeasure_map _ _
  apply Measure.ext_of_charFun
  funext x
  rw [hW0.spectralRepresentation (theory.poincare.onStates gΛInv ψ) x]
  have hInnerEq :
      inner ℂ (theory.poincare.onStates gΛInv ψ)
          (theory.translations.operator x (theory.poincare.onStates gΛInv ψ)) =
        inner ℂ ψ (theory.translations.operator (Λ.val.val x) ψ) := by
    rw [← inner_unitary (theory.poincare.onStates gΛ) (theory.poincare.unitary gΛ)]
    have hLeft : theory.poincare.onStates gΛ (theory.poincare.onStates gΛInv ψ) = ψ := by
      have hc := congrArg (fun op => op ψ) (theory.poincare.composition gΛ gΛInv).symm
      rw [hmul_id, theory.poincare.identity] at hc
      exact hc
    have hRight :
        theory.poincare.onStates gΛ
            (theory.translations.operator x (theory.poincare.onStates gΛInv ψ)) =
          theory.translations.operator (Λ.val.val x) ψ := by
      rw [← theory.translationCompatibility x, ← theory.translationCompatibility (Λ.val.val x)]
      have h1 :
          theory.poincare.onStates gΛ
              (theory.poincare.onStates (theory.poincare.pureTranslation x)
                (theory.poincare.onStates gΛInv ψ)) =
            theory.poincare.onStates (gΛ * theory.poincare.pureTranslation x)
              (theory.poincare.onStates gΛInv ψ) := by
        exact (congrArg (fun op => op (theory.poincare.onStates gΛInv ψ))
          (theory.poincare.composition gΛ (theory.poincare.pureTranslation x))).symm
      rw [h1, hconj x, theory.poincare.composition]
      simp only [ContinuousLinearMap.comp_apply, hLeft]
    rw [hLeft, hRight]
  rw [hInnerEq, ← hW0.spectralRepresentation ψ (Λ.val.val x)]
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply]
  have hMeasIntegrand :
      AEStronglyMeasurable (fun y : Spacetime => Complex.exp (↑(inner ℝ y x) * Complex.I))
        ((theory.energyMomentum.diagonal ψ).map (boostLM u η)) :=
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul
        continuous_const)).aestronglyMeasurable
  rw [MeasureTheory.integral_map hContB.measurable.aemeasurable hMeasIntegrand]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hSA : inner ℝ (boostLM u η p) x = inner ℝ p (Λ.val.val x) :=
    boostLM_selfAdjoint u η p x
  dsimp only
  rw [hSA]

/-- Every non-zero `p ∈ massGapHyperboloid Δ` can be boosted into the open
energy strip `energyGapStrip Δ` by some pure boost `boostLM u η` (`‖u‖ = 1`). -/
private lemma exists_boost_into_energyGapStrip {Δ : ℝ} (hΔ : 0 < Δ) {p : Spacetime}
    (hp : p ∈ massGapHyperboloid Δ) :
    ∃ (u : Space) (_ : ‖u‖ = 1) (η : ℝ), boostLM u η p ∈ energyGapStrip Δ := by
  rcases hp with ⟨hCone, hNe, hMk⟩
  have hCone_le : ‖YangMills.spatial p‖ ≤ YangMills.time p := hCone
  have ht_pos : 0 < YangMills.time p := by
    by_contra hle
    push Not at hle
    have hsp0 : YangMills.spatial p = 0 :=
      norm_le_zero_iff.mp (le_trans hCone_le hle)
    have ht0 : YangMills.time p = 0 :=
      le_antisymm hle (le_trans (norm_nonneg _) hCone_le)
    apply hNe
    rw [← mkSpacetime_eta p, ht0, hsp0]
    ext i
    refine Fin.lastCases ?_ ?_ i
    · exact time_mkSpacetime 0 0
    · intro j
      exact congrArg (fun s : Space => s.ofLp j) (spatial_mkSpacetime 0 0)
  by_cases hsp : YangMills.spatial p = 0
  · refine ⟨WithLp.toLp 2 ![1, 0, 0], ?_, 0, ?_⟩
    · rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_three]
    · have hb : boostLM (WithLp.toLp 2 ![1, 0, 0]) 0 p = p := by
        rw [boostLM_zero]; rfl
      rw [hb]
      unfold YangMills.minkowskiSquare at hMk
      rw [hsp, norm_zero, zero_pow two_ne_zero, sub_zero] at hMk
      exact ⟨ht_pos, by nlinarith⟩
  · have hk_pos : 0 < ‖YangMills.spatial p‖ := norm_pos_iff.mpr hsp
    set u : Space := (‖YangMills.spatial p‖⁻¹) • YangMills.spatial p
    have hu : ‖u‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hk_pos.ne']
    have hproj : inner ℝ u (YangMills.spatial p) = ‖YangMills.spatial p‖ := by
      rw [inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      field_simp [hk_pos.ne']
    set E := YangMills.time p
    set k := ‖YangMills.spatial p‖
    by_cases hMassless : k = E
    · set η : ℝ := Real.log (2 * E / Δ)
      refine ⟨u, hu, η, ?_⟩
      have ht' : YangMills.time (boostLM u η p) = E * Real.exp (-η) := by
        rw [boostLM_time, hproj, hMassless, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
        ring
      have hpos_arg : 0 < 2 * E / Δ := by positivity
      have hexp : Real.exp (-η) = Δ / (2 * E) := by
        rw [Real.exp_neg, Real.exp_log hpos_arg]
        field_simp [hΔ.ne', ht_pos.ne']
      rw [energyGapStrip, Set.mem_setOf_eq, ht', hexp]
      have hval : E * (Δ / (2 * E)) = Δ / 2 := by field_simp [ht_pos.ne']
      rw [hval]
      exact ⟨by linarith, by linarith⟩
    · have hk_lt : k < E := lt_of_le_of_ne hCone_le hMassless
      have hEmk : 0 < E - k := sub_pos.mpr hk_lt
      have hEpk : 0 < E + k := by linarith
      set r : ℝ := Real.sqrt ((E + k) / (E - k))
      have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos hEpk hEmk)
      set η : ℝ := Real.log r
      refine ⟨u, hu, η, ?_⟩
      have hexp_pos : Real.exp η = r := Real.exp_log hr_pos
      have hexp_neg : Real.exp (-η) = r⁻¹ := by rw [Real.exp_neg, hexp_pos]
      have hr_sq : r ^ 2 = (E + k) / (E - k) := Real.sq_sqrt (div_pos hEpk hEmk).le
      have ht' : YangMills.time (boostLM u η p) = Real.sqrt (E ^ 2 - k ^ 2) := by
        rw [boostLM_time, hproj, Real.cosh_eq, Real.sinh_eq, hexp_pos, hexp_neg]
        have hlhs_nonneg : 0 ≤ (r + r⁻¹) / 2 * E - (r - r⁻¹) / 2 * k := by
          have : (r + r⁻¹) / 2 * E - (r - r⁻¹) / 2 * k =
              (E - k) / 2 * r + (E + k) / 2 * r⁻¹ := by ring
          rw [this]
          positivity
        have hsq : ((r + r⁻¹) / 2 * E - (r - r⁻¹) / 2 * k) ^ 2 = E ^ 2 - k ^ 2 := by
          have h1 : r * r = (E + k) / (E - k) := by simpa [sq] using hr_sq
          have h2 : r⁻¹ * r⁻¹ = (E - k) / (E + k) := by
            rw [← mul_inv, h1, inv_div]
          have h3 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr_pos.ne'
          calc
            ((r + r⁻¹) / 2 * E - (r - r⁻¹) / 2 * k) ^ 2
                = ((E - k) ^ 2 * (r * r) + (E + k) ^ 2 * (r⁻¹ * r⁻¹) +
                    2 * (E ^ 2 - k ^ 2) * (r * r⁻¹)) / 4 := by ring
            _ = ((E - k) ^ 2 * ((E + k) / (E - k)) + (E + k) ^ 2 * ((E - k) / (E + k)) +
                    2 * (E ^ 2 - k ^ 2) * 1) / 4 := by rw [h1, h2, h3]
            _ = E ^ 2 - k ^ 2 := by field_simp [hEmk.ne', hEpk.ne']; ring
        rw [← hsq, Real.sqrt_sq hlhs_nonneg]
      rw [energyGapStrip, Set.mem_setOf_eq, ht']
      have hmk_pos : 0 < E ^ 2 - k ^ 2 := by nlinarith
      refine ⟨Real.sqrt_pos.mpr hmk_pos, ?_⟩
      rw [Real.sqrt_lt' hΔ]
      exact hMk

/-- Countable dense rational parameterization of pure Lorentz boosts `(u_q, η_q)`. -/
private abbrev RatBoostIdx := {v : Fin 3 → ℚ // v ≠ 0} × ℚ

private def ratVecToSpace (v : Fin 3 → ℚ) : Space :=
  WithLp.toLp 2 fun i => (v i : ℝ)

private lemma ratVecToSpace_ne_zero {v : Fin 3 → ℚ} (hv : v ≠ 0) :
    ratVecToSpace v ≠ 0 := by
  intro h
  apply hv
  ext i
  have hi := congrArg (fun s : Space => s i) h
  simpa [ratVecToSpace] using hi

private def ratUnitSpace (v : {v : Fin 3 → ℚ // v ≠ 0}) : Space :=
  (‖ratVecToSpace v.1‖⁻¹) • ratVecToSpace v.1

private lemma norm_ratUnitSpace (v : {v : Fin 3 → ℚ // v ≠ 0}) :
    ‖ratUnitSpace v‖ = 1 := by
  have hne : ratVecToSpace v.1 ≠ 0 := ratVecToSpace_ne_zero v.2
  rw [ratUnitSpace, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- Countable union of rational Lorentz-boost preimages of `energyGapStrip Δ`
covers the entire relativistic `massGapHyperboloid Δ`. -/
private lemma massGapHyperboloid_subset_countable_boosts {Δ : ℝ} (hΔ : 0 < Δ) :
    massGapHyperboloid Δ ⊆
      ⋃ idx : RatBoostIdx, (boostLM (ratUnitSpace idx.1) (idx.2 : ℝ)) ⁻¹' energyGapStrip Δ := by
  intro p hp
  obtain ⟨u, hu, η, hmem⟩ := exists_boost_into_energyGapStrip hΔ hp
  let f : Space × ℝ → ℝ := fun pair =>
    Real.cosh pair.2 * YangMills.time p -
      Real.sinh pair.2 * inner ℝ ((‖pair.1‖⁻¹) • pair.1) (YangMills.spatial p)
  have hContNorm : ContinuousAt (fun w : Space => (‖w‖⁻¹) • w) u := by
    have hu_ne : ‖u‖ ≠ 0 := by rw [hu]; norm_num
    exact (continuous_norm.continuousAt.inv₀ hu_ne).smul continuousAt_id
  have hContF : ContinuousAt f (u, η) := by
    have h1 : ContinuousAt (fun pair : Space × ℝ => Real.cosh pair.2 * YangMills.time p) (u, η) :=
      (Real.continuous_cosh.comp continuous_snd).continuousAt.mul continuousAt_const
    have h2 : ContinuousAt (fun pair : Space × ℝ => Real.sinh pair.2) (u, η) :=
      (Real.continuous_sinh.comp continuous_snd).continuousAt
    have h3 : ContinuousAt (fun pair : Space × ℝ => (‖pair.1‖⁻¹) • pair.1) (u, η) :=
      ContinuousAt.comp (g := fun w : Space => (‖w‖⁻¹) • w) (f := Prod.fst) hContNorm
        continuous_fst.continuousAt
    have h4 : ContinuousAt
        (fun pair : Space × ℝ => inner ℝ ((‖pair.1‖⁻¹) • pair.1) (YangMills.spatial p)) (u, η) :=
      h3.inner continuousAt_const
    exact h1.sub (h2.mul h4)
  have hf_mem : f (u, η) ∈ Set.Ioo (0 : ℝ) Δ := by
    have hu_eq : (‖u‖⁻¹) • u = u := by rw [hu, inv_one, one_smul]
    have htime : f (u, η) = YangMills.time (boostLM u η p) := by
      simp only [f, hu_eq, boostLM_time]
    rw [htime]
    exact hmem
  have hNhds : f ⁻¹' Set.Ioo (0 : ℝ) Δ ∈ 𝓝 (u, η) :=
    hContF.preimage_mem_nhds (isOpen_Ioo.mem_nhds hf_mem)
  rw [Metric.mem_nhds_iff] at hNhds
  obtain ⟨δ, hδ_pos, hBall⟩ := hNhds
  set δ' : ℝ := min δ (1 / 2)
  have hδ'_pos : 0 < δ' := lt_min hδ_pos (by norm_num)
  have hCoord : ∀ i : Fin 3, ∃ q : ℚ, |(q : ℝ) - u i| < δ' / 3 := by
    intro i
    obtain ⟨q, hq⟩ := exists_rat_btwn (show u i - δ' / 3 < u i + δ' / 3 by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose qVec hqVec using hCoord
  obtain ⟨qη, hqη⟩ := exists_rat_btwn (show η - δ' < η + δ' by linarith)
  have hDistU : dist (ratVecToSpace qVec) u < δ' := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    have hsum : ∑ i : Fin 3, ‖(ratVecToSpace qVec - u) i‖ ^ 2 < δ' ^ 2 := by
      have hterm : ∀ i : Fin 3, ‖(ratVecToSpace qVec - u) i‖ ^ 2 < (δ' / 3) ^ 2 := by
        intro i
        have hi : ‖(ratVecToSpace qVec - u) i‖ = |(qVec i : ℝ) - u i| := by
          simp [ratVecToSpace, Real.norm_eq_abs]
        rw [hi]
        have hlt := hqVec i
        have hnn : 0 ≤ |(qVec i : ℝ) - u i| := abs_nonneg _
        nlinarith
      have h3 := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin 3))
        (fun i _ => hterm i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
      nlinarith
    calc
      Real.sqrt (∑ i : Fin 3, ‖(ratVecToSpace qVec - u) i‖ ^ 2)
          < Real.sqrt (δ' ^ 2) := Real.sqrt_lt_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _) hsum
      _ = δ' := Real.sqrt_sq hδ'_pos.le
  have hqVec_ne : qVec ≠ 0 := by
    intro h0
    have hrat0 : ratVecToSpace qVec = 0 := by
      ext i; simp [ratVecToSpace, h0]
    rw [hrat0, dist_zero_left, hu] at hDistU
    have hle : δ' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hDistη : dist (qη : ℝ) η < δ' := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hInBall : (ratVecToSpace qVec, (qη : ℝ)) ∈ Metric.ball (u, η) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le hDistU (min_le_left _ _)) (lt_of_lt_of_le hDistη (min_le_left _ _))
  have hInIoo : f (ratVecToSpace qVec, (qη : ℝ)) ∈ Set.Ioo (0 : ℝ) Δ := hBall hInBall
  rw [Set.mem_iUnion]
  refine ⟨(⟨qVec, hqVec_ne⟩, qη), ?_⟩
  rw [Set.mem_preimage, energyGapStrip, Set.mem_setOf_eq, boostLM_time]
  exact hInIoo

/-- **Theorem 4 (Energy-Strip Gap ⇒ Exact Relativistic Mass-Hyperboloid Gap):**
Using ONLY `theory.W0` and `PoincareAction` (zero extra axioms), vanishing of
`energyMomentum.projection` on `energyGapStrip Δ` implies exact vanishing on the
full Lorentz-invariant relativistic mass hyperboloid
`{p ∈ forwardCone | p ≠ 0 ∧ minkowskiSquare p < Δ^2}`. -/
theorem energy_gap_implies_relativistic_mass_gap {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0)
    {Δ : ℝ} (hGap : HasEnergyGap theory Δ) :
    HasRelativisticMassGap theory Δ := by
  refine ⟨hGap.1, ?_⟩
  have hHyperMeas : MeasurableSet (massGapHyperboloid Δ) := measurableSet_massGapHyperboloid Δ
  have hStripMeas : MeasurableSet (energyGapStrip Δ) := measurableSet_energyGapStrip Δ
  have hStripNull : ∀ φ : H.carrier, theory.energyMomentum.diagonal φ (energyGapStrip Δ) = 0 := by
    intro φ
    have hId := theory.energyMomentum.diagonalIdentity hStripMeas φ
    rw [hGap.2] at hId
    simp only [zero_apply, inner_zero_right] at hId
    have hreal : (theory.energyMomentum.diagonal φ).real (energyGapStrip Δ) = 0 := by
      exact_mod_cast hId
    have hfin : theory.energyMomentum.diagonal φ (energyGapStrip Δ) ≠ ⊤ := measure_ne_top _ _
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hreal
    exact hreal.resolve_right hfin
  ext ψ
  rw [zero_apply]
  refine projection_apply_eq_zero_of_diagonal_zero theory.energyMomentum hHyperMeas ψ ?_
  refine measure_mono_null (massGapHyperboloid_subset_countable_boosts hGap.1) ?_
  refine measure_iUnion_null fun idx => ?_
  have hu : ‖ratUnitSpace idx.1‖ = 1 := norm_ratUnitSpace idx.1
  have hContB : Continuous (boostLM (ratUnitSpace idx.1) (idx.2 : ℝ)) :=
    (boostLM (ratUnitSpace idx.1) (idx.2 : ℝ)).continuous_of_finiteDimensional
  have hMapEq := diagonal_map_properBoost theory hW0 hu (idx.2 : ℝ) ψ
  have hApply :
      (theory.energyMomentum.diagonal ψ)
          ((boostLM (ratUnitSpace idx.1) (idx.2 : ℝ)) ⁻¹' energyGapStrip Δ) =
        ((theory.energyMomentum.diagonal ψ).map (boostLM (ratUnitSpace idx.1) (idx.2 : ℝ)))
          (energyGapStrip Δ) :=
    (Measure.map_apply hContB.measurable hStripMeas).symm
  rw [hApply, hMapEq]
  exact hStripNull _

/-- Values at equally spaced Euclidean times suffice for spectral decay. Forward
spectral support makes the diagonal Laplace transform decreasing between shells. -/
theorem state_decay_of_shell_bounds {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0) (ψ : H.carrier)
    {R Δ C : ℝ} (hR : 0 < R) (hΔ : 0 ≤ Δ) (hC : 0 ≤ C)
    (hs : ∀ k : ℕ, (∫ p, Real.exp (-((k : ℝ)*R)*YangMills.time p)
      ∂(theory.energyMomentum.diagonal ψ)) ≤ C * Real.exp (-Δ*((k : ℝ)*R))) :
    StateLaplaceDecay theory Δ ψ := by
  let μ := theory.energyMomentum.diagonal ψ
  haveI : IsFiniteMeasure μ := theory.energyMomentum.finite ψ
  have hcone : ∀ᵐ p ∂μ, p ∈ YangMills.forwardCone := by
    rw [ae_iff]
    exact diagonal_forwardCone_compl_eq_zero theory hW0 ψ
  have he := hcone.mono fun p hp => time_nonneg_of_mem_forwardCone hp
  have hi (u : ℝ) (hu : 0 ≤ u) : Integrable (fun p => Real.exp (-u * YangMills.time p)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((Real.continuous_exp.comp (continuous_const.mul continuous_time)).aestronglyMeasurable) ?_
    exact he.mono fun p hp => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hp
  refine ⟨C * Real.exp (Δ*R), by positivity, fun t ht => ?_⟩
  let k := ⌊t/R⌋₊
  have hleft : (k : ℝ)*R ≤ t := (le_div_iff₀ hR).mp (Nat.floor_le (div_nonneg ht hR.le))
  have hright : t < ((k : ℝ)+1)*R := (div_lt_iff₀ hR).mp (Nat.lt_floor_add_one _)
  have hm := integral_mono_ae (hi t ht) (hi ((k:ℝ)*R) (by positivity))
    (he.mono fun p hp => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hleft) hp))
  apply hm.trans ((hs k).trans ?_)
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hΔ (sub_nonneg.mpr hright.le)]

/-- Subtract the vacuum component of an ordered word of smeared fields. -/
def centeredFieldWord {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (w : List (Labels.carrier × TestFunction)) : H.carrier :=
  let v := (T.fields.vector w).1
  v - inner ℂ T.fields.vacuum.1 v • T.fields.vacuum.1

theorem centeredFieldWord_orthogonal {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW1 : T.W1) (w : List (Labels.carrier × TestFunction)) :
    inner ℂ T.fields.vacuum.1 (centeredFieldWord T w) = 0 := by
  simp [centeredFieldWord, inner_self_eq_norm_sq_to_K,
    hW1.domain.normalizedVacuum]

/-- W1 supplies the dense word span. Linearity and continuity extend annihilation
from each centered word and the vacuum to the entire Hilbert space. -/
theorem operator_zero_of_centered_words {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW1 : T.W1) (P : H.Operator)
    (hv : P T.fields.vacuum.1 = 0) (hw : ∀ w, P (centeredFieldWord T w) = 0) : P = 0 := by
  have hdom : T.fields.domain ≤ P.ker := by
    rw [hW1.domain.cyclicVacuum, Submodule.span_le]
    rintro _ ⟨w,rfl⟩
    simpa [centeredFieldWord, map_sub, map_smul, hv] using hw w
  have hall := T.fields.domain.topologicalClosure_minimal hdom P.isClosed_ker
  rw [Submodule.dense_iff_topologicalClosure_eq_top.mp hW1.domain.denseDomain] at hall
  ext v
  exact hall (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ H.carrier))

/-- A common rate on centered field words gives a relativistic gap. Every word
may use its own prefactor and its own unbounded sequence of physical times. -/
theorem cyclic_word_decay_implies_relativistic_mass_gap {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hwords : ∀ w, ∃ (C : ℝ) (t : ℕ → ℝ), Tendsto t atTop atTop ∧
      ∀ᶠ j in atTop, (∫ p, Real.exp (-t j * YangMills.time p) ∂(T.energyMomentum.diagonal (centeredFieldWord T w)))
        ≤ C * Real.exp (-Δ*t j)) : HasRelativisticMassGap T Δ := by
  apply energy_gap_implies_relativistic_mass_gap T hW0
  refine ⟨hΔ,operator_zero_of_centered_words T hW1 _ ?_ ?_⟩
  · exact projection_apply_eq_zero_of_diagonal_zero _ (measurableSet_energyGapStrip _) _
      (vacuum_diagonal_energyGapStrip T hW0 hW1 hW2 Δ)
  · intro w
    obtain ⟨C,t,ht,hb⟩ := hwords w
    exact projection_apply_eq_zero_of_diagonal_zero _ (measurableSet_energyGapStrip _) _
      (sparse_decay_kills_energy_strip T hW0 _ hΔ t ht hb)

#print axioms diagonal_subStrip_le_laplace
#print axioms sparse_decay_kills_energy_strip
#print axioms centeredFieldWord_orthogonal
#print axioms operator_zero_of_centered_words
#print axioms cyclic_word_decay_implies_relativistic_mass_gap

/-- **Theorem 5 (Uniform Exponential Decay ⇒ Exact Relativistic Mass-Hyperboloid Gap):**
Combines `uniform_decay_implies_energy_gap` and `energy_gap_implies_relativistic_mass_gap`. -/
theorem uniform_decay_implies_relativistic_mass_gap {H : HilbertSpace} {Labels : FieldLabels}
    (theory : WightmanTheory H Labels) (hW0 : theory.W0) (hW1 : theory.W1)
    {Δ : ℝ} (hDec : UniformSpectralDecay theory Δ) :
    HasRelativisticMassGap theory Δ :=
  energy_gap_implies_relativistic_mass_gap theory hW0
    (uniform_decay_implies_energy_gap theory hW0 hW1 hDec)

/-! ## Unified Part I Conditional Relativistic Mass-Gap Theorem Over `OpenAI-YM-20261028` -/

/-- **Headline Part I Theorem over `OpenAI-YM-20261028` (`ChallengeSpec.Hierarchy`):**
Given any reconstructed Yang-Mills continuum hierarchy `T : Hierarchy C` (as produced
by `YangMills.jointExistence`), if:
  1. `UniformPhaseInsensitivity T` (UFBI on the local algebra),
  2. `CharacterExtensional T`, and
  3. `UniformSpectralDecay T.theory Δ`,
then:
  - every separated Wilson continuum correlation equals the selected pure-phase correlation,
  - `T.Character` is a singleton and `T.phaseMeasure = Measure.dirac T.selected`,
  - `T.theory` has a strict energy-strip gap `HasEnergyGap T.theory Δ`, AND
  - `T.theory` has the **exact Lorentz-invariant relativistic Clay Mass Gap**
    `HasRelativisticMassGap T.theory Δ`:
    `T.theory.energyMomentum.projection {p ∈ forwardCone | p ≠ 0 ∧ minkowskiSquare p < Δ^2} = 0`. -/
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
    HasEnergyGap T.theory Δ ∧
    HasRelativisticMassGap T.theory Δ := by
  have hE : HasEnergyGap T.theory Δ :=
    uniform_decay_implies_energy_gap T.theory hRec.axioms.w0 hRec.axioms.w1 hDec
  refine ⟨?_, ?_, hE, energy_gap_implies_relativistic_mass_gap T.theory hRec.axioms.w0 hE⟩
  · intro n a x hx
    exact ufbi_collapses_phase_mixture T hRec hUfbi a x hx
  · exact ufbi_collapses_character_space T hRec hExt hUfbi

#print axioms ufbi_collapses_phase_mixture
#print axioms ufbi_collapses_character_space
#print axioms exponential_decay_kills_energy_strip_measure
#print axioms state_decay_of_shell_bounds
#print axioms uniform_decay_implies_energy_gap
#print axioms energy_gap_implies_relativistic_mass_gap
#print axioms uniform_decay_implies_relativistic_mass_gap
#print axioms part1_conditional_mass_gap_over_openai_ym

end YangMills.UfbiBridge
