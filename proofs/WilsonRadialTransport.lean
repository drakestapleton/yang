-- SPDX-License-Identifier: Apache-2.0
import WilsonAngle
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Constructions.UnitInterval

namespace YangMills.PeriodicWilson
open MeasureTheory Set Real Filter OneLinkTransport FundamentalSU2
open scoped Topology unitInterval ENNReal
noncomputable section

/-- Normalized cumulative integral, used as the angular CDF on [0,π]. -/
def angleCumulative (r t : ℝ) := (∫ x in 0..t, weight r x) / angleNormalizer r

private theorem continuous_weight_pair : Continuous (Function.uncurry weight) := by
  unfold weight Function.uncurry; fun_prop

private theorem continuous_Z : Continuous angleNormalizer :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' continuous_weight_pair _ _

private theorem continuous_cum : Continuous (Function.uncurry angleCumulative) :=
  (intervalIntegral.continuous_parametric_primitive_of_continuous continuous_weight_pair).div
    (continuous_Z.comp continuous_fst) (fun p => (angleNormalizer_pos p.1).ne')

private theorem weight_pos {t : ℝ} (ht : t ∈ Ioo 0 π) (r : ℝ) : 0 < weight r t :=
  mul_pos (pow_pos (sin_pos_of_pos_of_lt_pi ht.1 ht.2) _) (exp_pos _)

private theorem cum_angle_deriv (r t : ℝ) :
    HasDerivAt (angleCumulative r) (weight r t / angleNormalizer r) t := by
  have h : Continuous (weight r) := by unfold weight; fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable _ _)
    h.aestronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt).div_const _

private theorem mass_deriv (r t : ℝ) :
    HasDerivAt (fun s => ∫ x in 0..t, weight s x) (∫ x in 0..t, weight r x*cos x) r := by
  let dw := fun s x => weight s x * cos x
  have hd : Continuous (Function.uncurry dw) := continuous_weight_pair.mul (continuous_cos.comp continuous_snd)
  have hc (s : ℝ) : Continuous (weight s) := by unfold weight; fun_prop
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := r-1) (b := r+1)).prod (isCompact_uIcc (a := 0) (b := t))
    |>.exists_bound_of_continuousOn hd.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := dw)
    (Icc_mem_nhds (by linarith : r-1<r) (by linarith : r<r+1))
    (.of_forall fun s => (hc s).aestronglyMeasurable)
    ((hc r).intervalIntegrable _ _) ((hc r).mul continuous_cos).aestronglyMeasurable
    (.of_forall fun x hx s hs => hC (s,x) ⟨hs,uIoc_subset_uIcc hx⟩)
    ((continuous_const (y := C)).intervalIntegrable _ _) ?_).2
  exact .of_forall fun x _ s _ => by
    have h := (((hasDerivAt_id s).mul_const (cos x)).exp).const_mul (sin x ^ 2)
    convert h using 1 <;> first | rfl | (simp [dw,weight]; ring)

private theorem cum_field_deriv (r t : ℝ) :
    HasDerivAt (fun s => angleCumulative s t) (polarFlux r t / angleNormalizer r) r := by
  have h := (mass_deriv r t).div (mass_deriv r π) (angleNormalizer_pos r).ne'
  apply h.congr_deriv
  have hw : Continuous (weight r) := by unfold weight; fun_prop
  have h₁ : Continuous (fun x => weight r x*cos x) := hw.mul continuous_cos
  have h₂ : Continuous (fun x => weight r x*meanCos r) := hw.mul continuous_const
  have hz : (∫ x in 0..π, weight r x) ≠ 0 := (angleNormalizer_pos r).ne'
  unfold polarFlux
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _),intervalIntegral.integral_mul_const]
  unfold meanCos angleNormalizer
  field_simp [hz]

private theorem cum_strict (r : ℝ) : StrictMonoOn (angleCumulative r) (Icc 0 π) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ..)
    ((continuous_cum.comp (continuous_const.prodMk continuous_id)).continuousOn)
  intro t ht
  rw [interior_Icc] at ht
  change 0 < deriv (angleCumulative r) t
  rw [(cum_angle_deriv r t).deriv]
  exact div_pos (weight_pos ht _) (angleNormalizer_pos _)

@[simp] private theorem cum_zero (r : ℝ) : angleCumulative r 0 = 0 := by simp [angleCumulative]
@[simp] private theorem cum_pi (r : ℝ) : angleCumulative r π = 1 := by
  change angleNormalizer r / angleNormalizer r = 1
  exact div_self (angleNormalizer_pos r).ne'

private theorem exists_quantile (r : ℝ) (p : unitInterval) :
    ∃ t ∈ Icc 0 π, angleCumulative r t = p := by
  apply intermediate_value_Icc pi_pos.le
    (show ContinuousOn (angleCumulative r) (Icc 0 π) from
      (continuous_cum.comp (continuous_const.prodMk continuous_id)).continuousOn)
  simp

/-- The unique angle with cumulative probability p. Both endpoint quantiles
are included, although they have probability zero under a uniform rank. -/
def angleQuantile (r : ℝ) (p : unitInterval) := (exists_quantile r p).choose

private theorem quantile_mem (r : ℝ) (p : unitInterval) : angleQuantile r p ∈ Icc 0 π :=
  (exists_quantile r p).choose_spec.1

theorem cumulative_quantile (r : ℝ) (p : unitInterval) : angleCumulative r (angleQuantile r p) = p :=
  (exists_quantile r p).choose_spec.2

private theorem quantile_iff (r : ℝ) (p : unitInterval) {t : ℝ} (ht : t ∈ Icc 0 π) :
    angleQuantile r p ≤ t ↔ p.val ≤ angleCumulative r t := by
  rw [← cumulative_quantile r p]
  exact ((cum_strict r).le_iff_le (quantile_mem ..) ht).symm

private theorem quantile_cont : Continuous (Function.uncurry angleQuantile) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨r,p⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact .of_forall fun z => ha0.trans_le (quantile_mem z.1 z.2).1
    have ht : a ∈ Icc 0 π := ⟨le_of_not_gt ha0, ha.le.trans (quantile_mem r p).2⟩
    have h : angleCumulative r a < p := by
      rw [← cumulative_quantile r p]; exact cum_strict r ht (quantile_mem ..) ha
    have hc : Continuous (fun z : ℝ × unitInterval => angleCumulative z.1 a) :=
      continuous_cum.comp (continuous_fst.prodMk continuous_const)
    filter_upwards [(isOpen_lt hc (continuous_subtype_val.comp continuous_snd)).mem_nhds h] with z hz
    exact lt_of_not_ge fun hh => (not_lt_of_ge ((quantile_iff z.1 z.2 ht).mp hh)) hz
  · intro a ha
    by_cases hπ : π < a
    · exact .of_forall fun z => (quantile_mem z.1 z.2).2.trans_lt hπ
    have ht : a ∈ Icc 0 π := ⟨(quantile_mem r p).1.trans ha.le,le_of_not_gt hπ⟩
    have h : (p:ℝ) < angleCumulative r a := by
      rw [← cumulative_quantile r p]; exact cum_strict r (quantile_mem ..) ht ha
    have hc : Continuous (fun z : ℝ × unitInterval => angleCumulative z.1 a) :=
      continuous_cum.comp (continuous_fst.prodMk continuous_const)
    filter_upwards [(isOpen_lt (continuous_subtype_val.comp continuous_snd) hc).mem_nhds h] with z hz
    apply ((cum_strict z.1).lt_iff_lt (quantile_mem ..) ht).mp
    rwa [cumulative_quantile]

private theorem quantile_interior {p : unitInterval} (hp : p ≠ 0 ∧ p ≠ 1) (r : ℝ) :
    angleQuantile r p ∈ Ioo 0 π := by
  have h := cumulative_quantile r p
  obtain ⟨h0,hπ⟩ := quantile_mem r p
  constructor
  · refine lt_of_le_of_ne h0 fun he => hp.1 (Subtype.ext ?_)
    simpa [← he] using h.symm
  · refine lt_of_le_of_ne hπ fun he => hp.2 (Subtype.ext ?_)
    simpa [he] using h.symm

private theorem continuous_flux : Continuous (Function.uncurry polarFlux) := by
  have hm : Continuous meanCos :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r t => weight r t * cos t) (continuous_weight_pair.mul (continuous_cos.comp continuous_snd)) 0 π).div
      continuous_Z (fun r => (angleNormalizer_pos r).ne')
  exact intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun r x => weight r x * (cos x-meanCos r))
    (continuous_weight_pair.mul ((continuous_cos.comp continuous_snd).sub (hm.comp continuous_fst)))

/-- The polar velocity is the derivative of the moving angle at fixed uniform rank.
The minus sign comes from keeping the cumulative mass fixed. -/
def radialVelocity (r t : ℝ) := -(polarFlux r t / weight r t)

theorem quantile_field_deriv (r : ℝ) {p : unitInterval} (hp : p ≠ 0 ∧ p ≠ 1) :
    HasDerivAt (fun s => angleQuantile s p) (radialVelocity r (angleQuantile r p)) r := by
  let t := angleQuantile r p
  let A := fun s x => polarFlux s x / angleNormalizer s
  let B := fun s x => weight s x / angleNormalizer s
  let lin := fun x : ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight x
  have hl : Continuous lin := (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous
  have hA : Continuous (Function.uncurry A) := continuous_flux.div (continuous_Z.comp continuous_fst)
    (fun z => (angleNormalizer_pos _).ne')
  have hB : Continuous (Function.uncurry B) := continuous_weight_pair.div (continuous_Z.comp continuous_fst)
    (fun z => (angleNormalizer_pos _).ne')
  have da : ∀ᶠ z : ℝ × ℝ in 𝓝 (r,t), HasFDerivAt (fun s => angleCumulative s z.2)
      (lin (A z.1 z.2)) z.1 := .of_forall fun z => (cum_field_deriv ..).hasFDerivAt
  have db : ∀ᶠ z : ℝ × ℝ in 𝓝 (r,t), HasFDerivAt (angleCumulative z.1)
      (lin (B z.1 z.2)) z.2 := .of_forall fun z => (cum_angle_deriv ..).hasFDerivAt
  have hb : 0 < B r t := div_pos (weight_pos (quantile_interior hp r) _) (angleNormalizer_pos _)
  have inv : (lin (B r t)).IsInvertible := ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (.mk0 _ hb.ne'), rfl⟩
  have ca : ContinuousAt (fun z : ℝ × ℝ => lin (A z.1 z.2)) (r,t) := (hl.comp hA).continuousAt
  have cb : ContinuousAt (fun z : ℝ × ℝ => lin (B z.1 z.2)) (r,t) := (hl.comp hB).continuousAt
  let ψ := implicitFunctionOfBivariate (u := (r,t)) (f := angleCumulative)
    (f₁ := fun s x => lin (A s x)) (f₂ := fun s x => lin (B s x)) da db ca cb inv
  have hq : Continuous (fun s => angleQuantile s p) :=
    quantile_cont.comp (continuous_id.prodMk continuous_const)
  have hh := (continuous_id.prodMk hq).continuousAt (x := r) |>.tendsto.eventually
    (eventually_apply_eq_iff_implicitFunctionOfBivariate (u := (r,t)) (f := angleCumulative)
    (f₁ := fun s x => lin (A s x)) (f₂ := fun s x => lin (B s x)) da db ca cb inv)
  have he : (fun s => angleQuantile s p) =ᶠ[𝓝 r] ψ := by
    filter_upwards [hh] with s hs
    exact (hs.mp ((cumulative_quantile s p).trans (cumulative_quantile r p).symm)).symm
  have hd := (hasStrictFDerivAt_implicitFunctionOfBivariate (u := (r,t)) (f := angleCumulative)
    (f₁ := fun s x => lin (A s x)) (f₂ := fun s x => lin (B s x)) da db ca cb inv).hasFDerivAt.hasDerivAt
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  change -((lin (B r t)).inverse (1 * A r t)) = -(polarFlux r t / weight r t)
  congr 1
  apply inv.inverse_apply_eq.mpr
  change 1 * (polarFlux r t / angleNormalizer r) =
    (polarFlux r t / weight r t) * (weight r t / angleNormalizer r)
  have hw : weight r t ≠ 0 := (weight_pos (quantile_interior hp r) r).ne'
  field_simp [hw,(angleNormalizer_pos r).ne']

private theorem angle_measure_Iic (r t : ℝ) :
    angleLaw r (Iic t) = ∫⁻ x in Iic t ∩ Ioc 0 π, ENNReal.ofReal (weight r x / angleNormalizer r) := by
  rw [angleLaw, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]

private theorem angle_measure_inside (r : ℝ) {t : ℝ} (ht : t ∈ Icc 0 π) :
    angleLaw r (Iic t) = ENNReal.ofReal (angleCumulative r t) := by
  rw [angle_measure_Iic, show Iic t ∩ Ioc 0 π = Ioc 0 t by ext x; simp only [mem_inter_iff,mem_Iic,mem_Ioc]; grind]
  have hc : Continuous (fun x => weight r x / angleNormalizer r) := by unfold weight; fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp (hc.intervalIntegrable (μ := volume) 0 t))
    (.of_forall fun x => div_nonneg (mul_nonneg (sq_nonneg _) (exp_pos _).le) (angleNormalizer_pos r).le)]
  rw [← intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_div, angleCumulative]

private theorem continuous_Q (r : ℝ) : Continuous (angleQuantile r) :=
  quantile_cont.comp (continuous_const.prodMk continuous_id)

/-- Sampling a uniform rank and taking its quantile reproduces the exact Wilson angular law. -/
theorem quantile_pushforward (r : ℝ) : (volume : Measure unitInterval).map (angleQuantile r) = angleLaw r := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (continuous_Q r).measurable measurableSet_Iic]
  by_cases hl : 0 ≤ t
  · by_cases hh : t ≤ π
    · have ht : t ∈ Icc 0 π := ⟨hl,hh⟩
      let z : unitInterval := ⟨angleCumulative r t,
        by simpa using (cum_strict r).monotoneOn (show 0 ∈ Icc 0 π from ⟨le_rfl,pi_pos.le⟩) ht hl,
        by simpa using (cum_strict r).monotoneOn ht (show π ∈ Icc 0 π from ⟨pi_pos.le,le_rfl⟩) hh⟩
      rw [show angleQuantile r ⁻¹' Iic t = Iic z from Set.ext fun p => quantile_iff r p ht,
        unitInterval.volume_Iic, angle_measure_inside r ht]
    · have he : angleQuantile r ⁻¹' Iic t = univ := eq_univ_of_forall fun p => (quantile_mem r p).2.trans (le_of_not_ge hh)
      have h := measure_mono (μ := angleLaw r) (Iic_subset_Iic.mpr (le_of_not_ge hh))
      rw [angle_measure_inside r (show π ∈ Icc 0 π from ⟨pi_pos.le,le_rfl⟩), cum_pi, ENNReal.ofReal_one] at h
      rw [he, measure_univ]
      exact le_antisymm h (prob_le_one)
  · have he : angleQuantile r ⁻¹' Iic t = ∅ := eq_empty_iff_forall_notMem.mpr
        fun p h => hl ((quantile_mem r p).1.trans h)
    rw [he,measure_empty,angle_measure_Iic, show Iic t ∩ Ioc 0 π = ∅ from eq_empty_iff_forall_notMem.mpr (fun x hx => hl (hx.2.1.le.trans hx.1)), setLIntegral_empty]

/-- Shared uniform rank coupling of two polar-angle laws. -/
def radialCoupling (r s : ℝ) : Measure (ℝ × ℝ) :=
  (volume : Measure unitInterval).map (fun p => (angleQuantile r p, angleQuantile s p))

theorem radialCoupling_marginals (r s : ℝ) :
    (radialCoupling r s).fst = angleLaw r ∧ (radialCoupling r s).snd = angleLaw s := by
  constructor
  · rw [radialCoupling, Measure.fst_map_prodMk (continuous_Q s).measurable,quantile_pushforward]
  · rw [radialCoupling, Measure.snd_map_prodMk (continuous_Q r).measurable,quantile_pushforward]

private def rankSpeed (r : ℝ) (p : unitInterval) := radialVelocity r (angleQuantile r p)

private theorem speed_measurable : Measurable (Function.uncurry rankSpeed) := by
  have h : Continuous (fun z : ℝ × unitInterval => (z.1, angleQuantile z.1 z.2)) :=
    continuous_fst.prodMk quantile_cont
  exact ((continuous_flux.comp h).measurable.div (continuous_weight_pair.comp h).measurable).neg

private theorem speed_in_rank {r : ℝ} (hr : 0 ≤ r) : Continuous (rankSpeed r) :=
  (polarSpeed_continuousOn hr).neg.comp_continuous (continuous_Q r) (quantile_mem r)

private theorem speed_in_field {p : unitInterval} (hp : p ≠ 0 ∧ p ≠ 1) :
    Continuous (fun r => rankSpeed r p) := by
  have h : Continuous (fun r => (r, angleQuantile r p)) :=
    continuous_id.prodMk (quantile_cont.comp (continuous_id.prodMk continuous_const))
  exact ((continuous_flux.comp h).div (continuous_weight_pair.comp h)
    (fun r => (weight_pos (quantile_interior hp r) r).ne')).neg

/-- The mean squared velocity of the quantile path equals the analytic parallel energy. -/
theorem quantile_mean_square_speed (r : ℝ) :
    (∫ p : unitInterval, (radialVelocity r (angleQuantile r p))^2) = parallelEnergy r := by
  have h : Measurable (fun t => (radialVelocity r t)^2) :=
    (((continuous_flux.comp (continuous_const (y := r) |>.prodMk continuous_id)).measurable.div
      (continuous_weight_pair.comp (continuous_const (y := r) |>.prodMk continuous_id)).measurable).neg.pow_const 2)
  rw [← integral_map (continuous_Q r).measurable.aemeasurable h.aestronglyMeasurable, quantile_pushforward,
    integral_angleLaw]
  unfold parallelEnergy
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change weight r t * (-(polarFlux r t / weight r t))^2 = polarFlux r t^2 / weight r t
  by_cases hw : weight r t = 0
  · simp [hw]
  · field_simp

private theorem square_increment {a b : ℝ} (hab : a < b) {p : unitInterval} (hp : p ≠ 0 ∧ p ≠ 1) :
    (angleQuantile b p - angleQuantile a p)^2 ≤ (b-a) * ∫ r in a..b, (rankSpeed r p)^2 := by
  let D := angleQuantile b p - angleQuantile a p
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have hc := speed_in_field hp
  have hD : (∫ r in a..b, rankSpeed r p) = D := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => quantile_field_deriv r hp) (hc.intervalIntegrable _ _)
  have hz := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun r => sq_nonneg (L*rankSpeed r p-D))
  have he (r : ℝ) : (L*rankSpeed r p-D)^2 =
      L^2*(rankSpeed r p)^2 - (2*L*D)*(rankSpeed r p) + D^2 := by ring
  simp_rw [he] at hz
  have c₁ : Continuous (fun r => L^2 * (rankSpeed r p)^2) := continuous_const.mul (hc.pow 2)
  have c₂ : Continuous (fun r => (2*L*D)*(rankSpeed r p)) := continuous_const.mul hc
  have c₃ : Continuous (fun r => L^2 * rankSpeed r p^2 - (2*L*D)*rankSpeed r p) := c₁.sub c₂
  rw [intervalIntegral.integral_add (c₃.intervalIntegrable _ _) (intervalIntegrable_const (c := D^2)),
    intervalIntegral.integral_sub (c₁.intervalIntegrable _ _) (c₂.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hD,intervalIntegral.integral_const] at hz
  change 0 ≤ L^2 * (∫ r in a..b, rankSpeed r p ^ 2) - 2*L*D*D + L * D^2 at hz
  apply (mul_le_mul_iff_right₀ hL).mp
  change L*D^2 ≤ L*(L * ∫ r in a..b, rankSpeed r p^2)
  linarith only [hz]

private theorem path_square_integrable {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    Integrable (fun z : ℝ × unitInterval => (rankSpeed z.1 z.2)^2)
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hm : Measurable (fun z : ℝ × unitInterval => rankSpeed z.1 z.2 ^ 2) := speed_measurable.pow_const 2
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := a) (b := b))] with r hr
    exact ((speed_in_rank (ha.trans hr.1.le)).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hmeas := hm.norm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure unitInterval))
    apply Integrable.of_bound hmeas.aestronglyMeasurable (1/12)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := a) (b := b))] with r hr
    have hn (p : unitInterval) : |rankSpeed r p ^ 2| = rankSpeed r p ^ 2 := abs_of_nonneg (sq_nonneg _)
    have hmean : 0 ≤ ∫ p : unitInterval, rankSpeed r p ^ 2 := integral_nonneg fun p => sq_nonneg _
    simp only [Real.norm_eq_abs, hn, abs_of_nonneg hmean]
    exact (quantile_mean_square_speed r).trans_le (parallel_energy_cap (ha.trans hr.1.le))

private theorem ordered_cost_bound {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (∫ p : unitInterval, (angleQuantile b p - angleQuantile a p)^2) ≤ (b-a)^2 / 12 := by
  have hprod := path_square_integrable ha b
  have hi : Integrable (fun p : unitInterval => ∫ r in a..b, rankSpeed r p^2) volume := by
    simp_rw [intervalIntegral.integral_of_le hab.le]
    exact hprod.integral_prod_right
  have hc : Continuous (fun p => (angleQuantile b p-angleQuantile a p)^2) :=
    ((continuous_Q b).sub (continuous_Q a)).pow 2
  have hh := integral_mono_ae (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hi.const_mul (b-a)) (by
      filter_upwards [(volume : Measure unitInterval).ae_ne 0, (volume : Measure unitInterval).ae_ne 1] with p h₀ h₁
      exact square_increment hab ⟨h₀,h₁⟩)
  rw [integral_const_mul, ← intervalIntegral_integral_swap (f := fun r p => rankSpeed r p^2)
    (by simpa only [uIoc_of_le hab.le, Function.uncurry_def] using hprod)] at hh
  have hs : IntervalIntegrable (fun r => ∫ p : unitInterval, rankSpeed r p^2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hprod.integral_prod_left
  have hh' := intervalIntegral.integral_mono_on (μ := volume) hab.le hs intervalIntegrable_const
    (fun r hr => (quantile_mean_square_speed r).trans_le (parallel_energy_cap (ha.trans hr.1)))
  rw [intervalIntegral.integral_const] at hh'
  exact hh.trans ((mul_le_mul_of_nonneg_left hh' (sub_nonneg.mpr hab.le)).trans_eq (by simp [smul_eq_mul]; ring))

/-- A concrete two-marginal coupling with the squared Euclidean angle transport cost
bounded by the strength increment squared divided by twelve. -/
theorem radialCoupling_cost {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫ z, (z.2-z.1)^2 ∂radialCoupling r s) ≤ (s-r)^2/12 := by
  have hm := (continuous_Q r).prodMk (continuous_Q s)
  rw [radialCoupling, integral_map hm.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : ℝ × ℝ => (z.2-z.1)^2) _ from
      ((continuous_snd.sub continuous_fst).pow 2).aestronglyMeasurable)]
  rcases lt_trichotomy r s with h|h|h
  · exact ordered_cost_bound hr h
  · subst s; simp
  · have he (p : unitInterval) : (angleQuantile s p-angleQuantile r p)^2 =
          (angleQuantile r p-angleQuantile s p)^2 := by ring
    simp_rw [he]
    exact (ordered_cost_bound hs h).trans_eq (by ring)

/-- Squared Wasserstein transport cost on the real angle coordinate (in radians).
The infimum runs over all joint measures with the specified marginals. -/
def angleWassersteinSq (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ⨅ γ : {P : Measure (ℝ × ℝ) // P.fst = μ ∧ P.snd = ν},
    ∫⁻ z, ENNReal.ofReal ((z.2-z.1)^2) ∂γ.val

theorem radial_wasserstein_sq_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    angleWassersteinSq (angleLaw r) (angleLaw s) ≤ ENNReal.ofReal ((s-r)^2/12) := by
  let γ : {P : Measure (ℝ × ℝ) // P.fst = angleLaw r ∧ P.snd = angleLaw s} :=
    ⟨radialCoupling r s, radialCoupling_marginals r s⟩
  apply (iInf_le _ γ).trans
  have cost : Continuous (fun z : ℝ × ℝ => (z.2-z.1)^2) := (continuous_snd.sub continuous_fst).pow 2
  have joint := (continuous_Q r).prodMk (continuous_Q s)
  have hi : Integrable (fun z : ℝ × ℝ => (z.2-z.1)^2) (radialCoupling r s) :=
    (integrable_map_measure cost.aestronglyMeasurable joint.aemeasurable).2
      ((cost.comp joint).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  change (∫⁻ z, ENNReal.ofReal ((z.2-z.1)^2) ∂radialCoupling r s) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun z => sq_nonneg (z.2-z.1))]
  exact ENNReal.ofReal_le_ofReal (radialCoupling_cost hr hs)

/-- Transport of the projected heat baths, each angle measured about its own staple pole. -/
theorem heatBath_radial_wasserstein {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    ∃ k j : gaugeGroup.image,
    angleWassersteinSq ((heatBath β U e).map fun u => polarAngle (u*k))
      ((heatBath β V e).map fun v => polarAngle (v*j)) ≤
        ENNReal.ofReal ((fieldStrength β V e - fieldStrength β U e)^2/12) := by
  obtain ⟨k,hk⟩ := heatBath_polarAngle hl β U e
  obtain ⟨j,hj⟩ := heatBath_polarAngle hl β V e
  refine ⟨k,j,?_⟩
  rw [hk,hj]
  exact radial_wasserstein_sq_le (fieldStrength_mem hβ U e).1 (fieldStrength_mem hβ V e).1

#print axioms quantile_field_deriv
#print axioms quantile_pushforward
#print axioms radialCoupling_marginals
#print axioms quantile_mean_square_speed
#print axioms radialCoupling_cost
#print axioms radial_wasserstein_sq_le
#print axioms heatBath_radial_wasserstein

end
end YangMills.PeriodicWilson
