-- SPDX-License-Identifier: Apache-2.0
import PeriodicWilson
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Disintegration.Unique

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section

variable {l : ℕ+}

/-- The values of all Wilson links except the one being resampled. -/
abbrev Background (e : Edge l) := {i : Edge l // i ≠ e} → gaugeGroup.image

/-- Split a configuration into its unchanged links and the selected link. -/
def splitLink (e : Edge l) :
    Configuration gaugeGroup l ≃ᵐ Background e × gaugeGroup.image :=
  ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge l => gaugeGroup.image) (· = e)).trans
    ((MeasurableEquiv.piUnique (fun _ : {i : Edge l // i = e} => gaugeGroup.image)).prodCongr
      (MeasurableEquiv.refl _))).trans MeasurableEquiv.prodComm

@[simp] theorem splitLink_apply (e : Edge l) (U : Configuration gaugeGroup l) :
    splitLink e U = (fun i => U i.val, U e) := rfl

private theorem fill_update (e : Edge l) (b : Background e) (u v : gaugeGroup.image) :
    Function.update ((splitLink e).symm (b,u)) e v = (splitLink e).symm (b,v) := by
  apply (splitLink e).injective
  rw [MeasurableEquiv.apply_symm_apply, splitLink_apply]
  have h := (splitLink e).apply_symm_apply (b,u)
  rw [splitLink_apply] at h
  apply Prod.ext
  · funext i
    simpa [Function.update_of_ne i.property] using congrFun (congrArg Prod.fst h) i
  · simp

private abbrev prior (l : ℕ+) := Measure.pi (fun _ : Edge l => su2Haar)
private abbrev backgroundPrior (e : Edge l) := Measure.pi (fun _ : {i : Edge l // i ≠ e} => su2Haar)

private theorem split_preserving (e : Edge l) :
    MeasurePreserving (splitLink e) (prior l) ((backgroundPrior e).prod su2Haar) := by
  letI : Fintype {i : Edge l // i = e} := Subtype.fintype _
  exact Measure.measurePreserving_swap.comp
    (((measurePreserving_piUnique (fun _ : {i : Edge l // i = e} => su2Haar)).prod
      (MeasurePreserving.id _)).comp
        (measurePreserving_piEquivPiSubtypeProd (fun _ : Edge l => su2Haar) (· = e)))

private theorem continuous_energy : Continuous (wilsonEnergy (g := gaugeGroup) (l := l)) := by
  unfold wilsonEnergy
  apply continuous_finsetSum
  intro p _
  have h : Continuous (fun U : Configuration gaugeGroup l => plaquette U p.1 p.2.val.1 p.2.val.2) := by
    unfold plaquette
    fun_prop
  exact continuous_const.sub ((Complex.continuous_re.comp
    ((continuous_subtype_val.comp (continuous_subtype_val.comp h)).matrix_trace)).div_const _)

private def weight (β : ℝ) (U : Configuration gaugeGroup l) := Real.exp (-β * wilsonEnergy U)

private theorem continuous_weight (β : ℝ) : Continuous (weight (l := l) β) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_energy)

private def localZ (β : ℝ) (e : Edge l) (b : Background e) :=
  ∫ v, weight β ((splitLink e).symm (b,v)) ∂su2Haar

private theorem measurable_localZ (β : ℝ) (e : Edge l) : Measurable (localZ β e) :=
  (((continuous_weight β).measurable.comp (splitLink e).symm.measurable).stronglyMeasurable.integral_prod_right'
    (ν := su2Haar)).measurable

private theorem fiber_integrable (β : ℝ) (e : Edge l) (b : Background e) :
    Integrable (fun v => weight β ((splitLink e).symm (b,v))) su2Haar := by
  have hfill : Continuous (fun v : gaugeGroup.image => (splitLink e).symm (b,v)) := by
    have h := continuous_const.update (f := fun _ : gaugeGroup.image => (splitLink e).symm (b,1)) e continuous_id
    simpa only [id_eq, fill_update] using h
  exact ((continuous_weight β).comp hfill).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem localZ_pos (β : ℝ) (e : Edge l) (b : Background e) : 0 < localZ β e b :=
  integral_exp_pos (fiber_integrable β e b)

private def linkDensity (β : ℝ) (e : Edge l) (b : Background e) (v : gaugeGroup.image) :=
  ENNReal.ofReal (weight β ((splitLink e).symm (b,v)) / localZ β e b)

private theorem measurable_linkDensity (β : ℝ) (e : Edge l) :
    Measurable (Function.uncurry (linkDensity β e)) :=
  (((continuous_weight β).measurable.comp (splitLink e).symm.measurable).div
    ((measurable_localZ β e).comp measurable_fst)).ennreal_ofReal

/-- One-link resampling as a measurable kernel on the other links. -/
def heatBathKernel (β : ℝ) (e : Edge l) : Kernel (Background e) gaugeGroup.image :=
  (Kernel.const _ su2Haar).withDensity (linkDensity β e)

theorem heatBathKernel_apply (β : ℝ) (e : Edge l) (b : Background e) (u : gaugeGroup.image) :
    heatBathKernel β e b = heatBath β ((splitLink e).symm (b,u)) e := by
  rw [heatBathKernel, Kernel.withDensity_apply _ (measurable_linkDensity β e), Kernel.const_apply]
  unfold heatBath Measure.tilted
  simp_rw [fill_update]
  rfl

private theorem global_integrable (β : ℝ) : Integrable (weight (l := l) β) (prior l) :=
  (continuous_weight β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private def globalZ (l : ℕ+) (β : ℝ) := ∫ U, weight β U ∂prior l

private def backgroundDensity (β : ℝ) (e : Edge l) (b : Background e) :=
  ENNReal.ofReal (localZ β e b / globalZ l β)

private theorem measurable_backgroundDensity (β : ℝ) (e : Edge l) :
    Measurable (backgroundDensity β e) :=
  ((measurable_localZ β e).div_const _).ennreal_ofReal

/-- The Wilson law expressed in background and selected-link coordinates. -/
def splitLaw (β : ℝ) (e : Edge l) :=
  (wilsonLaw gaugeGroup l β su2Haar).map (splitLink e)

instance splitLaw_probability (β : ℝ) (e : Edge l) : IsProbabilityMeasure (splitLaw β e) := by
  haveI : IsProbabilityMeasure (wilsonLaw gaugeGroup l β su2Haar) :=
    isProbabilityMeasure_tilted (global_integrable β)
  exact Measure.isProbabilityMeasure_map (splitLink e).measurable.aemeasurable

instance heatBathKernel_markov (β : ℝ) (e : Edge l) : IsMarkovKernel (heatBathKernel β e) where
  isProbabilityMeasure b := by
    rw [heatBathKernel_apply β e b 1]
    apply isProbabilityMeasure_tilted
    simp_rw [fill_update]
    exact fiber_integrable β e b

private theorem splitLaw_density (β : ℝ) (e : Edge l) :
    splitLaw β e = ((backgroundPrior e).prod su2Haar).withDensity
      (fun p => ENNReal.ofReal (weight β ((splitLink e).symm p) / globalZ l β)) := by
  have hm : Measurable (fun p => ENNReal.ofReal (weight β ((splitLink e).symm p) / globalZ l β)) :=
    (((continuous_weight β).measurable.comp (splitLink e).symm.measurable).div_const _).ennreal_ofReal
  ext s hs
  rw [splitLaw, Measure.map_apply (splitLink e).measurable hs, wilsonLaw,
    withDensity_apply _ ((splitLink e).measurable hs), withDensity_apply _ hs,
    ← (split_preserving e).map_eq, setLIntegral_map hs hm (splitLink e).measurable]
  simp only [MeasurableEquiv.symm_apply_apply]
  rfl

/-- Disintegration at a selected link. The marginal is the projection of the actual
finite-volume Wilson law, and the kernel is its normalized Haar resampling law. -/
theorem wilsonLaw_disintegrates (β : ℝ) (e : Edge l) :
    splitLaw β e = (splitLaw β e).fst ⊗ₘ heatBathKernel β e := by
  let m := (backgroundPrior e).withDensity (backgroundDensity β e)
  letI : IsSFiniteKernel ((Kernel.const (Background e) su2Haar).withDensity (linkDensity β e)) :=
    inferInstanceAs (IsSFiniteKernel (heatBathKernel β e))
  have hbg : Measurable (fun p : Background e × gaugeGroup.image => backgroundDensity β e p.1) :=
    (measurable_backgroundDensity β e).comp measurable_fst
  have hlink : Measurable (fun p : Background e × gaugeGroup.image => linkDensity β e p.1 p.2) :=
    measurable_linkDensity β e
  have h : splitLaw β e = m ⊗ₘ heatBathKernel β e := by
    rw [splitLaw_density, heatBathKernel, Measure.compProd_withDensity (κ := Kernel.const (Background e) su2Haar) (measurable_linkDensity β e),
      Measure.compProd_const, prod_withDensity_left (measurable_backgroundDensity β e),
      ← withDensity_mul _ hbg hlink]
    congr 1
    funext p
    change ENNReal.ofReal (_ / _) = ENNReal.ofReal (_ / _) * ENNReal.ofReal (_ / _)
    have hp := localZ_pos β e p.1
    have hg : 0 < globalZ l β := integral_exp_pos (global_integrable β)
    rw [← ENNReal.ofReal_mul (div_nonneg hp.le hg.le)]
    congr 1
    field_simp
  have hm : (splitLaw β e).fst = m := by rw [h, Measure.fst_compProd]
  rwa [hm]

instance su2_standardBorel : StandardBorelSpace gaugeGroup.image := by
  have hu : IsClosed (Matrix.unitaryGroup (Fin (1+1)) ℂ : Set (Matrix (Fin (1+1)) (Fin (1+1)) ℂ)) :=
    isClosed_unitary
  letI : PolishSpace (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℂ))
  letI : PolishSpace (UnitaryRepresentation gaugeGroup.n) := hu.polishSpace
  letI : PolishSpace gaugeGroup.image := gaugeGroup.imageClosed.polishSpace
  infer_instance

/-- The Haar heat bath agrees with the regular conditional distribution, for
almost every background under the Wilson marginal. -/
theorem heatBath_eq_condKernel (β : ℝ) (e : Edge l) :
    ∀ᵐ b ∂(splitLaw β e).fst, heatBath β ((splitLink e).symm (b,1)) e =
      (splitLaw β e).condKernel b := by
  simpa only [← heatBathKernel_apply β e _ 1] using
    (eq_condKernel_of_measure_eq_compProd (heatBathKernel β e) (wilsonLaw_disintegrates β e))

/-- For side at least two the conditional law is the zonal Haar tilt at the
actual Wilson staple, including configurations where the staple vanishes. -/
theorem condKernel_eq_stapleTilt (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    ∀ᵐ b ∂(splitLaw β e).fst, ∃ K : gaugeGroup.image,
      (splitLaw β e).condKernel b = su2Haar.tilted (fun v =>
        fieldStrength β ((splitLink e).symm (b,1)) e * (suMat (v*K) 0 0).re) := by
  filter_upwards [heatBath_eq_condKernel β e] with b hb
  rw [← hb]
  exact heatBath_eq_tilt hl β _ e

#print axioms heatBathKernel_apply
#print axioms splitLaw_probability
#print axioms heatBathKernel_markov
#print axioms wilsonLaw_disintegrates
#print axioms heatBath_eq_condKernel
#print axioms condKernel_eq_stapleTilt

end
end YangMills.PeriodicWilson
