-- SPDX-License-Identifier: Apache-2.0
import PhaseFourBridge
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace YangMills.OneLinkTransport

open Real MeasureTheory
noncomputable section

def weight (r t : ℝ) := sin t ^ 2 * exp (r * cos t)

def transverseCost (r x : ℝ) :=
  x^2 / 27 + (2/3 : ℝ) * (1/3 - r * (1-x^2) * x / 6)^2

private theorem cosh_cap {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 7/4) : cosh u ≤ 7/2 := by
  have h4 : exp u ^ 4 ≤ exp 1 ^ 7 := by
    rw [← exp_nat_mul, ← exp_nat_mul, exp_le_exp]
    norm_num; linarith
  have h7 : exp 1 ^ 7 ≤ (2.72 : ℝ)^7 := pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) _
  have he : exp u ≤ 6 := by
    by_contra! hh
    have hh4 := pow_lt_pow_left₀ hh (by norm_num : (0:ℝ) ≤ 6) (by decide : 4 ≠ 0)
    norm_num only [OfNat.ofNat, Nat.reducePow] at hh4
    have hnum : (2.72:ℝ)^7 < 6^4 := by norm_num
    linarith
  rw [cosh_eq]
  linarith [(exp_le_one_iff.mpr (neg_nonpos.mpr h0))]

private def excess (r t : ℝ) := weight r t * (transverseCost r (cos t) - 1/12)

private def primitive (r t : ℝ) := sin t ^ 3 * cos t * cosh (r * cos t) / 54

private def slope (r t : ℝ) :=
  sin t ^ 2 / 54 * ((3 * cos t ^ 2 - sin t ^ 2) * cosh (r*cos t) -
    r * sin t ^ 2 * cos t * sinh (r*cos t))

private theorem slope_spec (r t : ℝ) : HasDerivAt (primitive r) (slope r t) t := by
  unfold primitive slope
  apply HasDerivAt.congr_deriv (((((hasDerivAt_sin t).pow 3).mul (hasDerivAt_cos t)).mul
    (((hasDerivAt_cos t).const_mul r).cosh)).div_const 54)
  simp only [Pi.pow_apply, Pi.mul_apply]
  ring

private theorem paired_excess {r t : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 7/4)
    (ht : t ∈ Set.Icc 0 (π/2)) : excess r t + excess r (π-t) ≤ slope r t := by
  let x := cos t
  have hx : 0 ≤ x := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hx1 : x ≤ 1 := cos_le_one _
  have hy : 0 ≤ 1-x^2 := by nlinarith
  have harg : r*x ≤ 7/4 := by nlinarith
  have hs := self_le_sinh_iff.mpr (mul_nonneg hr hx)
  have hc := cosh_cap (mul_nonneg hr hx) harg
  have hcore : r*x*(1-x^2)*cosh (r*x) ≤ (7/2)*sinh (r*x) := calc
    _ ≤ r*x*(1-x^2)*(7/2) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (7/2)*(r*x) := by nlinarith [mul_nonneg (mul_nonneg hr hx) (sq_nonneg x)]
    _ ≤ _ := by linarith
  have hmult := mul_le_mul_of_nonneg_left hcore (show 0 ≤ r*x*(1-x^2)^2/27 by positivity)
  dsimp [x] at hmult
  unfold excess weight transverseCost slope
  rw [sin_pi_sub, cos_pi_sub]
  rw [show sin t ^ 2 = 1 - cos t ^ 2 by linarith [sin_sq_add_cos_sq t]]
  rw [cosh_eq, sinh_eq] at hmult ⊢
  rw [mul_neg]
  linarith only [hmult]

private theorem fold_cap {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t ∈ Set.Icc 0 (π/2), f t + f (π-t) ≤ g t) :
    (∫ t in 0..π, f t) ≤ ∫ t in 0..π/2, g t := by
  have hsub : Continuous (fun t => f (π-t)) := hf.comp (continuous_const.sub continuous_id)
  have hh := intervalIntegral.integral_mono_on (μ := volume) (show 0 ≤ π/2 by positivity)
    ((hf.add hsub).intervalIntegrable _ _) (hg.intervalIntegrable _ _) h
  change (∫ t in 0..π/2, f t + f (π-t)) ≤ _ at hh
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hsub.intervalIntegrable _ _),
    intervalIntegral.integral_comp_sub_left, sub_zero, show π-π/2 = π/2 by ring,
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)] at hh
  exact hh

private theorem slope_integral_zero (r : ℝ) : (∫ t in 0..π/2, slope r t) = 0 := by
  have hd : Continuous (slope r) := by unfold slope; fun_prop
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := π/2) (fun t _ => slope_spec r t) (hd.intervalIntegrable _ _)
  simpa [primitive] using hf

private theorem sin_moment_cap {r : ℝ} (hr : 0 ≤ r) :
    (∫ t in 0..π, weight r t * sin t^2) ≤ (3/4)*(∫ t in 0..π, weight r t) := by
  let f := fun t => weight r t * sin t^2 - (3/4)*weight r t
  have hc : Continuous f := by dsimp [f,weight]; fun_prop
  have hd : Continuous (fun t => -27 * slope r t) := by unfold slope; fun_prop
  have hh := fold_cap hc hd (by
    intro t ht
    dsimp [f, weight, slope]
    rw [sin_pi_sub, cos_pi_sub, mul_neg]
    have hx := cos_nonneg_of_mem_Icc (x := t) ⟨by linarith [pi_pos, ht.1], ht.2⟩
    have hp := mul_nonneg (mul_nonneg (mul_nonneg hr hx) (sq_nonneg ((sin t)^2)))
      (sinh_nonneg_iff.mpr (mul_nonneg hr hx))
    rw [sinh_eq] at hp
    rw [cosh_eq, sinh_eq]
    have hs : sin t^2 = 1-cos t^2 := by linarith [sin_sq_add_cos_sq t]
    rw [hs] at hp ⊢
    linarith only [hp])
  rw [intervalIntegral.integral_const_mul, slope_integral_zero, mul_zero] at hh
  have ha : Continuous (fun t => weight r t * sin t^2) := by unfold weight; fun_prop
  have hb : Continuous (fun t => (3/4:ℝ) * weight r t) := by unfold weight; fun_prop
  dsimp [f] at hh
  rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hh
  linarith

/-- Integrated transverse field cost on S³ over every staple field used at β ≤ 0.280.
The positive normalization is common to both sides. -/
theorem transverse_integral_cap {β r : ℝ} (hβ : β ≤ 7/25)
    (hr : r ∈ Set.Icc 0 (6*β)) :
    (∫ t in 0..π, weight r t * transverseCost r (cos t)) ≤
      (∫ t in 0..π, weight r t) / 12 := by
  have hc : Continuous (excess r) := by unfold excess weight transverseCost; fun_prop
  have hd : Continuous (slope r) := by unfold slope; fun_prop
  have hpair := fold_cap hc hd (fun t ht => paired_excess hr.1 (by linarith [hr.2]) ht)
  rw [slope_integral_zero] at hpair
  have he : excess r = fun t => weight r t * transverseCost r (cos t) - weight r t * (1/12) := by
    funext t; unfold excess; ring
  have hw : Continuous (weight r) := by unfold weight; fun_prop
  have hwc : Continuous (fun t => weight r t * transverseCost r (cos t)) := by unfold weight transverseCost; fun_prop
  have hw12 : Continuous (fun t => weight r t * (1/12:ℝ)) := hw.mul continuous_const
  rw [he, intervalIntegral.integral_sub (hwc.intervalIntegrable _ _)
    (hw12.intervalIntegrable _ _), intervalIntegral.integral_mul_const] at hpair
  linarith

private def reduced (F : ℝ → ℝ) (t : ℝ) := F t / sin t^2

open Filter Set
open scoped Topology InnerProductSpace

private theorem reduced_continuous {F : ℝ → ℝ} {r m : ℝ}
    (hF : ∀ t, HasDerivAt F (weight r t * (cos t-m)) t)
    (h0 : F 0 = 0) (hπ : F π = 0) : ContinuousOn (reduced F) (Icc 0 π) := by
  have hf : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  have hg (t : ℝ) : HasDerivAt (fun x => sin x^2) (2*sin t*cos t) t := by
    apply HasDerivAt.congr_deriv ((hasDerivAt_sin t).pow 2)
    ring
  let q := fun x => weight r x * (cos x-m) / (2*sin x*cos x)
  have hq : q = fun x => sin x * exp (r*cos x) * (cos x-m) / (2*cos x) := by
    funext x
    by_cases hs : sin x = 0
    · simp [q, weight, hs]
    by_cases hc : cos x = 0
    · simp [q, weight, hc]
    dsimp [q, weight]; field_simp
  have hq0 : ContinuousAt q 0 := by rw [hq]; fun_prop (disch := norm_num)
  have hqπ : ContinuousAt q π := by rw [hq]; fun_prop (disch := norm_num)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | ha
  · subst t
    have h := HasDerivAt.lhopital_zero_right_on_Ico (show 0 < π/2 by positivity)
      (fun x _ => hF x) (fun x _ => hg x) hf.continuousOn (continuous_sin.pow 2).continuousOn
      (fun x hx => by
        have hs := sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, pi_pos])
        have hcos := cos_pos_of_mem_Ioo (x := x) ⟨by linarith [hx.1, pi_pos], hx.2⟩
        positivity)
      h0 (by simp) (show Tendsto q (𝓝[>] 0) (𝓝 0) by simpa [q, weight] using (hq0.continuousWithinAt (s := Ioi 0)).tendsto)
    have hh : ContinuousWithinAt (reduced F) (Ioi 0) 0 := by
      change Tendsto (fun x => F x / sin x^2) _ (𝓝 (F _ / sin _^2))
      simpa using h
    exact hh.insert.mono (fun x hx => (eq_or_lt_of_le hx.1).elim (fun e => Or.inl e.symm) Or.inr)
  rcases eq_or_lt_of_le ht.2 with h | hb
  · subst t
    have h := HasDerivAt.lhopital_zero_left_on_Ioc (show π/2 < π by linarith [pi_pos])
      (fun x _ => hF x) (fun x _ => hg x) hf.continuousOn (continuous_sin.pow 2).continuousOn
      (fun x hx => by
        have hs := sin_pos_of_pos_of_lt_pi (by linarith [hx.1, pi_pos]) hx.2
        have hcos := cos_neg_of_pi_div_two_lt_of_lt hx.1 (by linarith [hx.2, pi_pos])
        exact mul_ne_zero (by positivity) hcos.ne)
      hπ (by simp) (show Tendsto q (𝓝[<] π) (𝓝 0) by simpa [q, weight] using (hqπ.continuousWithinAt (s := Iio π)).tendsto)
    have hh : ContinuousWithinAt (reduced F) (Iio π) π := by
      change Tendsto (fun x => F x / sin x^2) _ (𝓝 (F _ / sin _^2))
      simpa using h
    exact hh.insert.mono (fun x hx => (eq_or_lt_of_le hx.2).elim Or.inl Or.inr)
  exact hf.continuousWithinAt.div (continuous_sin.pow 2).continuousWithinAt (pow_ne_zero _ (sin_pos_of_pos_of_lt_pi ha hb).ne')

/-- A primitive for the one-dimensional weighted flux estimate. Written with the
reduced flux so that the formula is continuous at both poles. -/
private def boundaryTerm (F K : ℝ → ℝ) (r m t : ℝ) :=
  F t * (cos t-m) - K t^2 / exp (r*cos t) * sin t * (3*cos t-3*r*sin t^2/5)

private def energyIntegrand (K : ℝ → ℝ) (r t : ℝ) :=
  K t^2 * sin t^2 / exp (r*cos t)

private def remainder (K : ℝ → ℝ) (r m t : ℝ) :=
  let s := sin t
  let x := cos t
  let e := exp (r*x)
  let k := K t
  (s*e*(x-m)-k*(3*x-3*r*s^2/5))^2/e +
    6/25*r^2*s^4*k^2/e + 3/2*s^2/e*(k-e*s/3)^2

private def fluxSlope (K : ℝ → ℝ) (r m t : ℝ) :=
  (3/2)*energyIntegrand K r t - weight r t*sin t^2/6 + remainder K r m t

private theorem boundary_deriv {F : ℝ → ℝ} {r m t : ℝ}
    (hF : HasDerivAt F (weight r t * (cos t-m)) t) (hs : sin t ≠ 0) :
    HasDerivAt (boundaryTerm F (reduced F) r m) (fluxSlope (reduced F) r m t) t := by
  let K := reduced F
  have ht : F t = K t * sin t^2 := by dsimp [K,reduced]; field_simp
  have dk : HasDerivAt K (exp (r*cos t)*(cos t-m)-2*K t*cos t/sin t) t := by
    apply HasDerivAt.congr_deriv (hF.div ((hasDerivAt_sin t).pow 2) (pow_ne_zero _ hs))
    simp only [weight, Pi.pow_apply]
    rw [ht]; field_simp; ring
  have de := ((hasDerivAt_cos t).const_mul r).exp
  have db := ((hasDerivAt_cos t).const_mul 3).sub
    ((((hasDerivAt_sin t).pow 2).const_mul (3*r)).div_const 5)
  apply HasDerivAt.congr_deriv ((hF.mul ((hasDerivAt_cos t).sub_const m)).sub
    (((((dk.pow 2).div de (exp_pos _).ne').mul (hasDerivAt_sin t)).mul db)))
  simp only [weight, fluxSlope, energyIntegrand, remainder, Pi.pow_apply, Pi.mul_apply,
    Pi.div_apply, Pi.sub_apply]
  rw [ht]
  change _ = (3/2)*(K t^2*sin t^2/exp (r*cos t)) -
    (sin t^2*exp (r*cos t))*sin t^2/6 + _
  field_simp [hs, (exp_pos (r*cos t)).ne']
  ring

private theorem flux_integral_cap {F : ℝ → ℝ} {r m : ℝ} (hr : 0 ≤ r)
    (hF : ∀ t, HasDerivAt F (weight r t * (cos t-m)) t)
    (h0 : F 0 = 0) (hπ : F π = 0) :
    (∫ t in 0..π, energyIntegrand (reduced F) r t) ≤ (∫ t in 0..π, weight r t) / 12 := by
  let K := reduced F
  have hK : ContinuousOn K (Icc 0 π) := reduced_continuous hF h0 hπ
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  have hn : ∀ t ∈ Icc (0:ℝ) π, exp (r*cos t) ≠ 0 := fun t _ => (exp_pos _).ne'
  have hd : ContinuousOn (fluxSlope K r m) (Icc 0 π) := by
    unfold fluxSlope energyIntegrand remainder weight
    try dsimp only
    fun_prop (disch := first | exact hn | (intros; positivity))
  have hb : ContinuousOn (boundaryTerm F K r m) (Icc 0 π) := by
    unfold boundaryTerm; fun_prop (disch := first | exact hn | positivity)
  have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le pi_pos.le hb
    (fun t ht => boundary_deriv (hF t) (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne')
    (hd.intervalIntegrable_of_Icc pi_pos.le)
  simp [boundaryTerm, hπ, h0] at hz
  have ha : ContinuousOn (fun t => (3/2:ℝ)*energyIntegrand K r t) (Icc 0 π) := by
    unfold energyIntegrand; fun_prop (disch := first | exact hn | positivity)
  have hw : Continuous (fun t => weight r t*sin t^2/6) := by unfold weight; fun_prop
  have hle := intervalIntegral.integral_mono_on (μ := volume) pi_pos.le
    ((ha.sub hw.continuousOn).intervalIntegrable_of_Icc pi_pos.le) (hd.intervalIntegrable_of_Icc pi_pos.le)
    (fun t _ => show (3/2)*energyIntegrand K r t - weight r t*sin t^2/6 ≤ fluxSlope K r m t by
      unfold fluxSlope; apply le_add_of_nonneg_right; unfold remainder; positivity)
  rw [hz] at hle
  change (∫ t in 0..π, (3/2)*energyIntegrand K r t - weight r t*sin t^2/6) ≤ 0 at hle
  rw [intervalIntegral.integral_sub (ha.intervalIntegrable_of_Icc pi_pos.le) (hw.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hle
  change (∫ t in 0..π, energyIntegrand K r t) ≤ _
  linarith [sin_moment_cap hr]

def transverseEnergy (r : ℝ) :=
  (∫ t in 0..π, weight r t * transverseCost r (cos t)) / (∫ t in 0..π, weight r t)

def meanCos (r : ℝ) :=
  (∫ t in 0..π, weight r t * cos t) / (∫ t in 0..π, weight r t)

def polarFlux (r t : ℝ) := ∫ x in 0..t, weight r x * (cos x - meanCos r)

def parallelEnergy (r : ℝ) :=
  (∫ t in 0..π, polarFlux r t ^ 2 / weight r t) / (∫ t in 0..π, weight r t)

private theorem normalizer_pos {r : ℝ} (hr : 0 ≤ r) : 0 < ∫ t in 0..π, weight r t := by
  have hc : Continuous (fun t : ℝ => sin t^2 * exp (-r)) := by fun_prop
  have hw : Continuous (weight r) := by unfold weight; fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) pi_pos.le
    (hc.intervalIntegrable _ _) (hw.intervalIntegrable _ _) (fun t _ =>
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [mul_nonneg hr (show 0 ≤ cos t+1 by linarith [neg_one_le_cos t])])) (sq_nonneg (sin t)))
  rw [intervalIntegral.integral_mul_const] at hh
  exact (mul_pos (integral_sin_pow_pos (n := 2)) (exp_pos _)).trans_le hh

private theorem polarFlux_hasDerivAt (r t : ℝ) :
    HasDerivAt (polarFlux r) (weight r t * (cos t - meanCos r)) t := by
  have hw : Continuous (weight r) := by unfold weight; fun_prop
  have hc : Continuous (fun x => weight r x * (cos x - meanCos r)) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem polarFlux_pi {r : ℝ} (hr : 0 ≤ r) : polarFlux r π = 0 := by
  have hZ := normalizer_pos hr
  have hw : Continuous (weight r) := by unfold weight; fun_prop
  simp only [polarFlux, mul_sub]
  have ha : Continuous (fun x => weight r x * cos x) := hw.mul continuous_cos
  have hb : Continuous (fun x => weight r x * meanCos r) := hw.mul continuous_const
  rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const]
  unfold meanCos
  field_simp
  simp

/-- The radial trial speed extends continuously to both poles. -/
theorem polarSpeed_continuousOn {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (fun t => polarFlux r t / weight r t) (Icc 0 π) := by
  have h := (reduced_continuous (polarFlux_hasDerivAt r) (by simp [polarFlux]) (polarFlux_pi hr)).div
    (continuous_exp.comp (continuous_const.mul continuous_cos)).continuousOn
    (fun t _ => (exp_pos (r*cos t)).ne')
  change ContinuousOn (fun t => (polarFlux r t / sin t^2) / exp (r*cos t)) _ at h
  simpa only [weight,div_div] using h

theorem parallel_energy_cap {r : ℝ} (hr : 0 ≤ r) : parallelEnergy r ≤ 1/12 := by
  have hZ := normalizer_pos hr
  have hh := flux_integral_cap hr (polarFlux_hasDerivAt r) (by simp [polarFlux]) (polarFlux_pi hr)
  have he : (fun t => energyIntegrand (reduced (polarFlux r)) r t) =
      fun t => polarFlux r t ^ 2 / weight r t := by
    funext t
    by_cases hs : sin t = 0
    · simp [energyIntegrand,reduced,weight,hs]
    unfold energyIntegrand reduced weight
    field_simp
  rw [he] at hh
  apply (div_le_iff₀ hZ).2
  linarith

/-- Orthogonal combination of the two continuum trial-field costs on the entire staple
interval. The velocity-cost inequalities express the separate geometric transport step. -/
theorem s3_w2_bound_on_staple_interval {β r c s Lpar Lperp : ℝ} (hβ : β ≤ 7/25)
    (hr : r ∈ Set.Icc 0 (6*β)) (hUnit : c^2+s^2=1)
    (hPolar : Lpar^2 ≤ parallelEnergy r) (hField : Lperp^2 ≤ transverseEnergy r) :
    Real.sqrt (c^2*Lpar^2 + s^2*Lperp^2) ≤ 1/(2*Real.sqrt 3) := by
  apply YangMills.WilsonPolymer.s3_w2_orthogonality_bound hUnit (hPolar.trans (parallel_energy_cap hr.1))
  apply hField.trans
  apply (div_le_iff₀ (normalizer_pos hr.1)).2
  linarith [transverse_integral_cap hβ hr]

/-- Combined trial energy in an arbitrary unit direction of the staple field. -/
theorem s3_w2_orthogonality_bound {β r c s : ℝ} (hβ : β ≤ 7/25) (hr : r ∈ Icc 0 (6*β))
    (hu : c^2+s^2 = 1) :
    Real.sqrt (c^2*parallelEnergy r + s^2*transverseEnergy r) ≤ 1/(2*Real.sqrt 3) := by
  have hperp : transverseEnergy r ≤ 1/12 := by
    apply (div_le_iff₀ (normalizer_pos hr.1)).2
    linarith [transverse_integral_cap hβ hr]
  have hp := mul_le_mul_of_nonneg_left (parallel_energy_cap hr.1) (sq_nonneg c)
  have ht := mul_le_mul_of_nonneg_left hperp (sq_nonneg s)
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  linarith

/-- At the Phase IV endpoint the square of the proposed degree-12 coefficient is
940800 / 1000000. This expression has no quadrature inputs. -/
theorem phase4_endpoint_square :
    ((12 : ℝ) * (1/(2*Real.sqrt 3)) * (7/25))^2 = 940800/1000000 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  rw [mul_pow, mul_pow, div_pow, mul_pow, h]
  norm_num

/-- A degree-12 shell estimate using the actual one-link trial energy suffices for
the continuum gap at the Phase IV rate. Volume-uniform shell comparison, physical
spacing, the spectral limit, and vacuum support are independent physical inputs. -/
theorem phase4_shell_limits_imply_mass_gap {H : YangMills.HilbertSpace}
    {Labels : YangMills.FieldLabels} (T : YangMills.WightmanTheory H Labels)
    (hW0 : T.W0) (hW1 : T.W1) {R β : ℝ} (hR : 0 < R) (hβ0 : 0 ≤ β) (hβ : β ≤ 7/25) :
    let α := (12 : ℝ)*(1/(2*Real.sqrt 3))*(7/25)
    let Δ := (1/R)*Real.log (1/α)
    T.energyMomentum.diagonal T.fields.vacuum.1 (YangMills.UfbiBridge.energyGapStrip Δ) = 0 →
    (∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
      ∃ f : ℕ → ℕ → ℝ,
        (∀ k : ℕ, Tendsto (fun n => f n k) atTop
          (𝓝 (∫ p, Real.exp (-((k : ℝ)*R)*YangMills.time p) ∂(T.energyMomentum.diagonal ψ)))) ∧
        ∀ n k, 0 ≤ f n k ∧ ∃ r c s : ℝ, r ∈ Icc 0 (6*β) ∧ c^2+s^2=1 ∧
          f n (k+1) ≤ 12*β*Real.sqrt (c^2*parallelEnergy r + s^2*transverseEnergy r)*f n k) →
    YangMills.UfbiBridge.HasRelativisticMassGap T Δ := by
  intro α Δ hv hs
  have hα : 0 < α := by dsimp [α]; positivity
  have h1 : α < 1 := by have he := phase4_endpoint_square; change α^2 = _ at he; nlinarith
  apply YangMills.PhaseTwo.shell_limits_imply_relativistic_mass_gap T hW0 hW1 hR hα h1 hv
  intro ψ hψ
  obtain ⟨f, hf, hstep⟩ := hs ψ hψ
  refine ⟨f, hf, fun n k => ?_⟩
  obtain ⟨hn, r, c, s, hr, hu, hh⟩ := hstep n k
  apply hh.trans (mul_le_mul_of_nonneg_right _ hn)
  calc 12*β*Real.sqrt _ ≤ 12*β*(1/(2*Real.sqrt 3)) :=
          mul_le_mul_of_nonneg_left (s3_w2_orthogonality_bound hβ hr hu) (by positivity)
       _ ≤ α := by dsimp [α]; nlinarith [mul_le_mul_of_nonneg_right hβ (show 0 ≤ 1/(2*Real.sqrt 3) by positivity)]

#print axioms s3_w2_orthogonality_bound
#print axioms phase4_endpoint_square
#print axioms phase4_shell_limits_imply_mass_gap
#print axioms transverse_integral_cap
#print axioms parallel_energy_cap
#print axioms s3_w2_bound_on_staple_interval
end
end YangMills.OneLinkTransport
