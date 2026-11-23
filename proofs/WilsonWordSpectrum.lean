-- SPDX-License-Identifier: Apache-2.0
import WilsonCyclicGap
import Mathlib.MeasureTheory.Measure.LevyConvergence

namespace YangMills.UfbiBridge
open MeasureTheory Set Filter Real
open scoped Topology ComplexConjugate
noncomputable section

abbrev FieldWord (Labels : FieldLabels) := List (Labels.carrier × TestFunction)

/-- The adjoint product reverses the insertions and conjugates each test. -/
def adjointFieldWord {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (w : FieldWord Labels) : FieldWord Labels :=
  (w.map fun a => (T.adjointLabel a.1,conjugateTest a.2)).reverse

def translatedFieldWord {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (x : Spacetime) (w : FieldWord Labels) : FieldWord Labels :=
  let g := T.poincare.pureTranslation x
  w.map fun a => (T.poincare.onLabels g a.1,T.poincare.onTests g a.2)

def wordExpectation {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (w : FieldWord Labels) := inner ℂ T.fields.vacuum.1 (T.fields.vector w).1

theorem word_inner_eq_expectation {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (hW1 : T.W1) (w v : FieldWord Labels) :
    inner ℂ (T.fields.vector w).1 (T.fields.vector v).1 = wordExpectation T (adjointFieldWord T w ++ v) := by
  induction w generalizing v with
  | nil => rfl
  | cons a w ih =>
    rw [FieldSystem.vector, hW1.adjoint]
    simpa [adjointFieldWord, List.append_assoc, FieldSystem.vector] using ih ((T.adjointLabel a.1,conjugateTest a.2)::v)

theorem translatedFieldWord_vector {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (hW2 : T.W2) (x : Spacetime) (w : FieldWord Labels) :
    T.translations.operator x (T.fields.vector w).1 = (T.fields.vector (translatedFieldWord T x w)).1 := by
  rw [← T.translationCompatibility]
  induction w with
  | nil => exact hW2.vacuumInvariant _
  | cons a w ih =>
    rw [FieldSystem.vector, hW2.fieldCovariance]
    have hd : (⟨_,hW2.domainInvariant _ (T.fields.vector w).2⟩ : T.fields.domain) =
          T.fields.vector (translatedFieldWord T x w) := Subtype.ext ih
    rw [hd]; rfl

/-- The connected real-time translation correlation of a smeared word. -/
def connectedWordTranslation {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (w : FieldWord Labels) (x : Spacetime) :=
  wordExpectation T (adjointFieldWord T w ++ translatedFieldWord T x w) - conj (wordExpectation T w) * wordExpectation T w

theorem centered_word_charFun {H : HilbertSpace} {Labels : FieldLabels} (T : WightmanTheory H Labels)
    (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2) (w : FieldWord Labels) (x : Spacetime) :
    charFun (T.energyMomentum.diagonal (centeredFieldWord T w)) x = connectedWordTranslation T w x := by
  let Ω := T.fields.vacuum.1
  let v := (T.fields.vector w).1
  let U := T.translations.operator x
  have hΩ : U Ω = Ω := by dsimp [U,Ω]; rw [← T.translationCompatibility, hW2.vacuumInvariant]
  let iso : H.carrier →ₗᵢ[ℂ] H.carrier := ⟨U.toLinearMap,T.translations.unitary x⟩
  have hinv : inner ℂ Ω (U v) = inner ℂ Ω v := by
    calc _ = inner ℂ (U Ω) (U v) := by rw [hΩ]
         _ = _ := iso.inner_map_map Ω v
  have hnorm : inner ℂ Ω Ω = 1 := by simp [Ω,inner_self_eq_norm_sq_to_K,hW1.domain.normalizedVacuum]
  have hconj : inner ℂ v Ω = conj (inner ℂ Ω v) := (inner_conj_symm ..).symm
  rw [hW0.spectralRepresentation]
  change inner ℂ (v-inner ℂ Ω v • Ω) (U (v-inner ℂ Ω v • Ω)) = _
  rw [map_sub, map_smul, hΩ]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hinv, hnorm, hconj, mul_one]
  have hcorr : inner ℂ v (U v) = wordExpectation T (adjointFieldWord T w ++ translatedFieldWord T x w) := by
    rw [show U v = _ from translatedFieldWord_vector T hW2 x w, word_inner_eq_expectation T hW1]
  rw [hcorr]
  change _ = _ - conj (inner ℂ Ω v) * inner ℂ Ω v
  ring

/-- The public reconstruction evaluates each word expectation appearing in
the connected characteristic function as a boundary value of its own
smeared analytic continuation. -/
theorem wordExpectation_boundary {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (hT : T.Reconstructed) (w : FieldWord T.labels) (height : Fin w.length → ℝ) (hh : StrictMono height) :
    ∃ tags : Fin w.length → T.Tag,
      (∀ i, T.toLabel (tags i).1 (tags i).2 = (w.get i).1) ∧
      Tendsto (fun r => ∫ x : Points w.length,
        T.continuation tags (Hierarchy.complexShift r height x) (Hierarchy.spatialPoints x) *
          Hierarchy.tensorTest (fun i => (w.get i).2) x) (𝓝[>] 0) (𝓝 (wordExpectation T.theory w)) := by
  choose tags ht using fun i : Fin w.length => hT.covers (w.get i).1
  refine ⟨tags,ht,?_⟩
  have hw : List.ofFn (fun i => (T.toLabel (tags i).1 (tags i).2,(w.get i).2)) = w := by
    simp_rw [ht]; exact List.ofFn_get w
  have h := hT.boundary tags height hh (fun i => (w.get i).2)
  unfold FieldSystem.vacuumExpectation at h
  rwa [hw] at h

private theorem measure_mass_char_zero (μ : FiniteMeasure Spacetime) :
    (charFun (μ : Measure Spacetime) 0).re = μ.mass := by
  rw [charFun_zero, Complex.ofReal_re, Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

private theorem charFun_normalize (μ : FiniteMeasure Spacetime) (h : μ ≠ 0) (x : Spacetime) :
    charFun (μ.normalize : Measure Spacetime) x = charFun (μ : Measure Spacetime) x / (μ.mass:ℂ) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero h]
  simp only [charFun_apply, integral_smul_nnreal_measure]
  simp [div_eq_inv_mul, NNReal.smul_def, Complex.real_smul]

/-- The finite-measure form of Lévy convergence also covers null word states.
Masses are read from the characteristic functions at the origin. -/
theorem finiteMeasure_tendsto_of_charFun {μ : FiniteMeasure Spacetime} {ν : ℕ → FiniteMeasure Spacetime}
    (h : ∀ x, Tendsto (fun n => charFun (ν n : Measure Spacetime) x) atTop (𝓝 (charFun (μ : Measure Spacetime) x))) :
    Tendsto ν atTop (𝓝 μ) := by
  have hm : Tendsto (fun n => (ν n).mass) atTop (𝓝 μ.mass) := by
    apply NNReal.tendsto_coe.mp
    simpa only [Function.comp_def, measure_mass_char_zero] using Complex.continuous_re.continuousAt.tendsto.comp (h 0)
  by_cases hz : μ=0
  · subst μ
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hm
  have hm0 := μ.mass_nonzero_iff.mpr hz
  apply μ.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass _ hm
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro x
  have hev : ∀ᶠ n in atTop, (ν n).mass ≠ 0 := hm.eventually_ne hm0
  have hc : Tendsto (fun n => ((ν n).mass:ℂ)) atTop (𝓝 (μ.mass:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (NNReal.tendsto_coe.mpr hm)
  rw [charFun_normalize μ hz]
  apply ((h x).div hc (by exact_mod_cast hm0)).congr'
  filter_upwards [hev] with n hn
  exact (charFun_normalize _ ((ν n).mass_nonzero_iff.mp hn) x).symm

/-- Match continuum real-time word correlations to characteristic functions
of finite positive spectral measures. Their Euclidean moments then converge
at every fixed nonnegative time. -/
theorem word_laplace_limit_of_translation_match {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2) (w : FieldWord Labels)
    (ν : ℕ → FiniteMeasure Spacetime) (hs : ∀ n, ∀ᵐ p ∂(ν n : Measure Spacetime), 0 ≤ YangMills.time p)
    (hmatch : ∀ x, Tendsto (fun n => charFun (ν n : Measure Spacetime) x) atTop (𝓝 (connectedWordTranslation T w x)))
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ p, exp (-t*YangMills.time p) ∂(ν n : Measure Spacetime)) atTop
      (𝓝 (∫ p, exp (-t*YangMills.time p) ∂(T.energyMomentum.diagonal (centeredFieldWord T w)))) := by
  let μ : FiniteMeasure Spacetime := ⟨T.energyMomentum.diagonal (centeredFieldWord T w),inferInstance⟩
  have hμ : (μ : Measure Spacetime) = T.energyMomentum.diagonal (centeredFieldWord T w) := rfl
  have hweak : Tendsto ν atTop (𝓝 μ) := finiteMeasure_tendsto_of_charFun fun x => by
    rw [hμ, centered_word_charFun T hW0 hW1 hW2 w x]
    exact hmatch x
  let f : C(Spacetime,ℝ) := ⟨fun p => exp (-t*max 0 (YangMills.time p)), by
    have htime : Continuous YangMills.time := PiLp.continuous_apply 2 (fun _ : Axis => ℝ) YangMills.timeAxis
    exact continuous_exp.comp (continuous_const.mul (continuous_const.max htime))⟩
  have h01 (p : Spacetime) : 0 ≤ f p ∧ f p ≤ 1 :=
    ⟨(exp_pos _).le, exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (le_max_left ..))⟩
  let F := BoundedContinuousFunction.mkOfBound f 1 fun x y => by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [(h01 x).1,(h01 x).2,(h01 y).1,(h01 y).2]
  have eq (m : Measure Spacetime) (hm : ∀ᵐ p ∂m, 0 ≤ YangMills.time p) :
      (∫ p, F p ∂m) = ∫ p, exp (-t*YangMills.time p) ∂m := by
    apply integral_congr_ae
    filter_upwards [hm] with p hp
    change exp (-t*max 0 (YangMills.time p)) = _
    rw [max_eq_right hp]
  have hcone : ∀ᵐ p ∂(μ : Measure Spacetime), p ∈ forwardCone := by
    rw [ae_iff]; exact diagonal_forwardCone_compl_eq_zero T hW0 _
  have hc := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak F
  rw [eq (μ : Measure Spacetime) (hcone.mono fun _ hp => time_nonneg_of_mem_forwardCone hp)] at hc
  simp only [eq _ (hs _), hμ] at hc
  exact hc

#print axioms word_inner_eq_expectation
#print axioms translatedFieldWord_vector
#print axioms centered_word_charFun
#print axioms wordExpectation_boundary
#print axioms finiteMeasure_tendsto_of_charFun
#print axioms word_laplace_limit_of_translation_match
end
end YangMills.UfbiBridge

namespace YangMills.PeriodicWilson
open FundamentalSU2 UfbiBridge Set Filter MeasureTheory Real
open scoped Topology
noncomputable section

/-- A finite-volume spectral route to the full relativistic gap. Identify
the positive measures by their real-time connected word correlations and
dominate their Euclidean moments by the actual blocked Wilson products. -/
theorem reconstructed_gap_of_translation_match {C : WilsonFamily gaugeGroup}
    (T : Hierarchy C) (hT : T.Reconstructed) (b : ℕ+) (axis : Axis)
    {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax) (hwindow : βmax < sqrt 3/18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val) (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Icc 0 βmax)
    (hwords : ∀ w : List (C.Token × TestFunction),
      ∃ (ν : ℕ → FiniteMeasure Spacetime) (A : ℝ) (k : ℕ → ℕ)
        (terms : (n j : ℕ) → List (WilsonProductTerm (l n))),
        (∀ n, ∀ᵐ p ∂(ν n : Measure Spacetime), 0 ≤ YangMills.time p) ∧
        (∀ x, Tendsto (fun n => charFun (ν n : Measure Spacetime) x) atTop
          (𝓝 (connectedWordTranslation T.theory (insertionWord T w) x))) ∧
        0 ≤ A ∧ Tendsto k atTop atTop ∧
        ∀ j, ∀ᶠ n in atTop, productExpansionWeight (terms n j) ≤ A ∧
          (∀ a ∈ terms n j, a.coefficient ≠ 0 → separatedPlaquetteProducts axis (k j) a.left a.right) ∧
          (∫ p, exp (-((b.val*k j:ℕ):ℝ)*R*YangMills.time p) ∂(ν n : Measure Spacetime))
            ≤ productExpansion b (β n) (terms n j)) :
    HasRelativisticMassGap T.theory ((1/R)*log (1/straightRow βmax)) := by
  apply blockedWilson_gap_of_word_comparison T.theory hT.axioms.w0 hT.axioms.w1 hT.axioms.w2
    b axis hR hpos hwindow l hl β hβ
  intro v
  obtain ⟨w,rfl⟩ := insertionWord_surjective T hT v
  obtain ⟨ν,A,k,terms,henergy,hmatch,hA,hk,hs⟩ := hwords w
  refine ⟨A,k,hA,hk,fun j ε hε => ?_⟩
  have hm := word_laplace_limit_of_translation_match T.theory hT.axioms.w0 hT.axioms.w1 hT.axioms.w2
    (insertionWord T w) ν henergy hmatch (((b.val*k j:ℕ):ℝ)*R) (by positivity)
  simp only [neg_mul] at hm
  obtain ⟨n,hn,hnear⟩ := ((hs j).and ((Metric.tendsto_nhds.mp hm) ε hε)).exists
  refine ⟨n,terms n j,hn.1,hn.2.1,?_⟩
  rw [Real.dist_eq, abs_lt] at hnear
  have hc := hn.2.2
  simp only [neg_mul] at hc ⊢
  linarith only [hnear.1,hc]

#print axioms reconstructed_gap_of_translation_match
end
end YangMills.PeriodicWilson
