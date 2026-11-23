-- SPDX-License-Identifier: Apache-2.0
import WilsonConditional
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real Set Filter
open scoped Topology ComplexConjugate Matrix.Norms.Frobenius
noncomputable section

private abbrev G := gaugeGroup.image

/-- Polar angle from the identity quaternion, in radians. -/
def polarAngle (u : gaugeGroup.image) := arccos (suMat u 0 0).re

private def scalarPart (u : G) := (suMat u 0 0).re
private def imagPart (j : Fin 3) (u : G) : ℝ := ![(suMat u 0 0).im, (suMat u 0 1).re, (suMat u 0 1).im] j

private theorem continuous_entry (j : Fin 2) : Continuous (fun u : G => suMat u 0 j) :=
  (continuous_apply j).comp ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val))

private theorem continuous_scalar : Continuous scalarPart := Complex.continuous_re.comp (continuous_entry 0)
private theorem continuous_imag (j : Fin 3) : Continuous (imagPart j) := by
  fin_cases j <;> first | exact Complex.continuous_im.comp (continuous_entry _) | exact Complex.continuous_re.comp (continuous_entry _)

private theorem sphere_identity (u : G) :
    scalarPart u^2 + imagPart 0 u^2 + imagPart 1 u^2 + imagPart 2 u^2 = 1 := by
  have h := congrArg (fun A : M => (A 0 0).re) u.val.prop.2
  change ((suMat u * star (suMat u)) 0 0).re = ((1 : M) 0 0).re at h
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_re] at h
  change (suMat u 0 0).re^2 + (suMat u 0 0).im^2 + (suMat u 0 1).re^2 + (suMat u 0 1).im^2 = 1
  nlinarith

private theorem scalar_range (u : G) : scalarPart u ∈ Icc (-1) 1 := by
  have hh := sphere_identity u
  constructor <;> nlinarith [sq_nonneg (imagPart 0 u), sq_nonneg (imagPart 1 u), sq_nonneg (imagPart 2 u)]

private def pairMatrix (a b : ℂ) : M := !![a,b; -conj b,conj a]
private def rotA (j : Fin 3) (t : ℝ) : ℂ := ![Complex.mk (cos t) (-sin t), Complex.mk (cos t) 0, Complex.mk (cos t) 0] j
private def rotB (j : Fin 3) (t : ℝ) : ℂ := ![(0 : ℂ), Complex.mk (-sin t) 0, Complex.mk 0 (-sin t)] j

private theorem rotate_pair (j : Fin 3) (t : ℝ) :
    ∃ k : G, ∀ u : G,
      scalarPart (u*k) = scalarPart u * cos t + imagPart j u * sin t ∧
      imagPart j (u*k) = imagPart j u * cos t - scalarPart u * sin t := by
  let A := pairMatrix (rotA j t) (rotB j t)
  have hq : A ∈ quaternionAlgebra := ⟨rfl,rfl⟩
  have hl : length A = 1 := by
    change sqrt (‖rotA j t‖^2 + ‖rotB j t‖^2) = 1
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    fin_cases j <;> simp [rotA,rotB,Complex.normSq_apply, ← sq, cos_sq_add_sin_sq]
  obtain ⟨k,hk⟩ := polar hq
  have hmat : suMat k = A := by simpa [hl,suMat] using hk.symm
  refine ⟨k,fun u => ?_⟩
  have hu : suMat (u*k) = suMat u * A := by rw [← hmat]; rfl
  fin_cases j <;> simp [scalarPart,imagPart,hu,Matrix.mul_apply,Fin.sum_univ_two,
    A,pairMatrix,rotA,rotB,Complex.mul_re,Complex.mul_im] <;> ring

private theorem integrable_haar {f : G → ℝ} (hf : Continuous f) : Integrable f su2Haar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem haar_rotate (k : G) (f : G → ℝ) (hf : Continuous f) :
    (∫ u, f (u*k) ∂su2Haar) = ∫ u, f u ∂su2Haar := by
  rw [← PhaseFour.gaugeImage_haar_map_mul_right su2Haar k, integral_map
    (continuous_mul_const k).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [PhaseFour.gaugeImage_haar_map_mul_right su2Haar k]

private def haarMoment (n : ℕ) := ∫ u, scalarPart u ^ n ∂su2Haar

/-- Differentiate the Haar-invariant moment in a real quaternion coordinate plane. -/
private theorem mixed_moment (n : ℕ) (j : Fin 3) :
    ((n:ℝ)+1) * (∫ u, scalarPart u^n * imagPart j u^2 ∂su2Haar) = haarMoment (n+2) := by
  let a := fun (t : ℝ) (u : G) => scalarPart u*cos t + imagPart j u*sin t
  let b := fun (t : ℝ) (u : G) => imagPart j u*cos t - scalarPart u*sin t
  let f := fun t u => a t u^(n+1) * b t u
  let df := fun t u => ((n:ℝ)+1) * a t u^n * b t u^2 - a t u^(n+2)
  have ca : Continuous (Function.uncurry a) := by
    exact ((continuous_scalar.comp continuous_snd).mul (continuous_cos.comp continuous_fst)).add
      (((continuous_imag j).comp continuous_snd).mul (continuous_sin.comp continuous_fst))
  have cb : Continuous (Function.uncurry b) := by
    exact (((continuous_imag j).comp continuous_snd).mul (continuous_cos.comp continuous_fst)).sub
      ((continuous_scalar.comp continuous_snd).mul (continuous_sin.comp continuous_fst))
  have cf : Continuous (Function.uncurry f) := (ca.pow _).mul cb
  have cd : Continuous (Function.uncurry df) := ((continuous_const.mul (ca.pow _)).mul (cb.pow _)).sub (ca.pow _)
  have hd (u : G) (t : ℝ) : HasDerivAt (fun x => f x u) (df t u) t := by
    have ha : HasDerivAt (fun x => a x u) (b t u) t := by
      rw [show b t u = scalarPart u * -sin t + imagPart j u*cos t by dsimp [b]; ring]
      exact ((hasDerivAt_cos t).const_mul _).add ((hasDerivAt_sin t).const_mul _)
    have hb : HasDerivAt (fun x => b x u) (-a t u) t := by
      rw [show -a t u = imagPart j u * -sin t - scalarPart u*cos t by dsimp [a]; ring]
      exact ((hasDerivAt_cos t).const_mul _).sub ((hasDerivAt_sin t).const_mul _)
    rw [show df t u = ↑(n+1 : ℕ) * a t u ^ (n+1-1) * b t u * b t u + a t u ^ (n+1) * -a t u by
      simp [df, pow_succ]; ring]
    exact (ha.pow (n+1)).mul hb
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).prod (isCompact_univ (X := G))
    |>.exists_bound_of_continuousOn cd.continuousOn
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := su2Haar) (F := f) (F' := df)
    (Icc_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))
    (.of_forall fun t => (cf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_haar (cf.comp (continuous_const.prodMk continuous_id)))
    (cd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun u t ht => hC (t,u) ⟨ht,mem_univ _⟩) (integrable_const C)
    (.of_forall fun u t _ => hd u t)).2
  have hconst : (fun t => ∫ u, f t u ∂su2Haar) = fun _ => ∫ u, scalarPart u^(n+1)*imagPart j u ∂su2Haar := by
    funext t
    obtain ⟨k,hk⟩ := rotate_pair j t
    have h := haar_rotate k (fun u => scalarPart u^(n+1)*imagPart j u) ((continuous_scalar.pow _).mul (continuous_imag j))
    simpa only [(hk _).1, (hk _).2, f,a,b] using h
  rw [hconst] at hi
  have hz := hi.unique (hasDerivAt_const (0:ℝ) _)
  simp only [df,a,b,cos_zero,sin_zero,mul_one,mul_zero,add_zero,sub_zero] at hz
  have h₁ : Integrable (fun u => ((n:ℝ)+1) * scalarPart u^n * imagPart j u^2) su2Haar :=
    integrable_haar ((continuous_const.mul (continuous_scalar.pow _)).mul ((continuous_imag j).pow _))
  have h₂ : Integrable (fun u => scalarPart u^(n+2)) su2Haar := integrable_haar (continuous_scalar.pow _)
  rw [integral_sub h₁ h₂] at hz
  simp_rw [mul_assoc, integral_const_mul] at hz
  exact sub_eq_zero.mp hz

private theorem haar_recurrence (n : ℕ) :
    ((n:ℝ)+4)*haarMoment (n+2) = ((n:ℝ)+1)*haarMoment n := by
  let term := fun (j : Fin 3) u => scalarPart u^n * imagPart j u^2
  have ht (j : Fin 3) : Integrable (term j) su2Haar :=
    integrable_haar ((continuous_scalar.pow _).mul ((continuous_imag j).pow _))
  have hp : Integrable (fun u => scalarPart u^(n+2)) su2Haar := integrable_haar (continuous_scalar.pow _)
  have h (u : G) : term 0 u + term 1 u + term 2 u + scalarPart u^(n+2) = scalarPart u^n := by
    dsimp [term]
    rw [pow_add]
    linear_combination (scalarPart u)^n * sphere_identity u
  have he := congrArg (fun f : G → ℝ => ∫ u, f u ∂su2Haar) (funext h)
  change (∫ u, term 0 u + term 1 u + term 2 u + scalarPart u^(n+2) ∂su2Haar) = haarMoment n at he
  have h01 : Integrable (fun u => term 0 u + term 1 u) su2Haar := (ht 0).add (ht 1)
  have h012 : Integrable (fun u => term 0 u + term 1 u + term 2 u) su2Haar := h01.add (ht 2)
  rw [integral_add h012 hp, integral_add h01 (ht 2), integral_add (ht 0) (ht 1)] at he
  change (∫ u, term 0 u ∂su2Haar) + (∫ u, term 1 u ∂su2Haar) + (∫ u, term 2 u ∂su2Haar) +
    haarMoment (n+2) = haarMoment n at he
  have hm (j : Fin 3) : ((n:ℝ)+1) * (∫ u, term j u ∂su2Haar) = haarMoment (n+2) := mixed_moment n j
  linear_combination ((n:ℝ)+1)*he - hm 0 - hm 1 - hm 2

private theorem haar_first : haarMoment 1 = 0 := by
  obtain ⟨k,hk⟩ := rotate_pair 0 π
  have h := haar_rotate k scalarPart continuous_scalar
  simp_rw [fun u => (hk u).1, cos_pi, sin_pi, mul_zero, add_zero, mul_neg_one, integral_neg] at h
  simp [haarMoment]; linarith

private def angleMoment (n : ℕ) := (2/π) * ∫ t in 0..π, sin t^2 * cos t^n

private theorem angle_recurrence (n : ℕ) :
    ((n:ℝ)+4)*angleMoment (n+2) = ((n:ℝ)+1)*angleMoment n := by
  let F := fun t => sin t^3 * cos t^(n+1)
  let g := fun t => ((n:ℝ)+4)*(sin t^2*cos t^(n+2)) - ((n:ℝ)+1)*(sin t^2*cos t^n)
  have hd (t : ℝ) : HasDerivAt F (g t) t := by
    convert ((hasDerivAt_sin t).pow 3).mul ((hasDerivAt_cos t).pow (n+1)) using 1 <;> try rfl
    simp [g,pow_succ]
    linear_combination ((n:ℝ)+1)*sin t^2*cos t^n*(sin_sq_add_cos_sq t)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun t _ => hd t) (hg.intervalIntegrable _ _)
  simp only [F,sin_zero,sin_pi,zero_pow (by decide : 3 ≠ 0),zero_mul,sub_zero] at hh
  have hc (k : ℕ) (a : ℝ) : Continuous (fun t => a*(sin t^2*cos t^k)) := by fun_prop
  rw [show g = fun t => ((n:ℝ)+4)*(sin t^2*cos t^(n+2)) - ((n:ℝ)+1)*(sin t^2*cos t^n) from rfl,
    intervalIntegral.integral_sub ((hc _ _).intervalIntegrable _ _) ((hc _ _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  unfold angleMoment
  linear_combination (2/π)*hh

private theorem moments_eq (n : ℕ) : haarMoment n = angleMoment n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have hp := pi_pos.ne'
    simp [haarMoment, angleMoment, integral_sin_sq, hp]
  | one => simp [haar_first,angleMoment,integral_sin_sq_mul_cos]
  | more n ih _ =>
    have hh := haar_recurrence n
    rw [ih, ← angle_recurrence n] at hh
    exact mul_left_cancel₀ (by positivity : (n:ℝ)+4 ≠ 0) hh

/-- Classes of the concrete quaternion representation determine the angular law:
the normalized Haar expectation of any continuous scalar-coordinate observable. -/
private theorem haar_polynomial (p : Polynomial ℝ) :
    (∫ u, p.eval (scalarPart u) ∂su2Haar) = (2/π)*∫ t in 0..π, sin t^2*p.eval (cos t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add,mul_add]
    have hh (p : Polynomial ℝ) : Integrable (fun u => p.eval (scalarPart u)) su2Haar :=
      integrable_haar (p.continuous.comp continuous_scalar)
    have hc (p : Polynomial ℝ) : Continuous (fun t => sin t^2 * p.eval (cos t)) :=
      (continuous_sin.pow _).mul (p.continuous.comp continuous_cos)
    rw [integral_add (hh p) (hh q), intervalIntegral.integral_add
      ((hc p).intervalIntegrable _ _) ((hc q).intervalIntegrable _ _), mul_add,hp,hq]
  | monomial n c =>
    simp only [Polynomial.eval_monomial, integral_const_mul]
    have h := moments_eq n
    unfold haarMoment angleMoment at h
    simp_rw [show ∀ t : ℝ, sin t^2 * (c*cos t^n) = c*(sin t^2*cos t^n) from fun _ => by ring,
      intervalIntegral.integral_const_mul]
    rw [h]; ring

/-- Angular partition integral at field strength r. -/
def angleNormalizer (r : ℝ) := ∫ t in 0..π, OneLinkTransport.weight r t

/-- Lebesgue density of the polar angle, with the Wilson one-link field r.
The restricted interval differs from [0,π] only by a Lebesgue-null endpoint. -/
def angleLaw (r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 π)).withDensity (fun t =>
    ENNReal.ofReal (OneLinkTransport.weight r t / angleNormalizer r))

private theorem continuous_w (r : ℝ) : Continuous (OneLinkTransport.weight r) := by
  unfold OneLinkTransport.weight; fun_prop

private theorem weight_nonneg (r t : ℝ) : 0 ≤ OneLinkTransport.weight r t :=
  mul_nonneg (sq_nonneg _) (exp_pos _).le

theorem angleNormalizer_pos (r : ℝ) : 0 < angleNormalizer r := by
  have h := intervalIntegral.integral_mono_on (μ := volume) pi_pos.le
    ((continuous_sin.pow 2 |>.mul (continuous_const (y := exp (-|r|)))).intervalIntegrable _ _)
    ((continuous_w r).intervalIntegrable _ _) (fun t _ =>
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
        have h := abs_mul r (cos t)
        have hh : |r*cos t| ≤ |r| := by rw [h]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
        exact (abs_le.mp hh).1)) (sq_nonneg _))
  change (∫ t in 0..π, sin t^2 * exp (-|r|)) ≤ angleNormalizer r at h
  rw [intervalIntegral.integral_mul_const] at h
  exact (mul_pos (integral_sin_pow_pos (n := 2)) (exp_pos _)).trans_le h

instance angleLaw_probability (r : ℝ) : IsProbabilityMeasure (angleLaw r) := by
  constructor
  rw [angleLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hc : Continuous (fun t => OneLinkTransport.weight r t / angleNormalizer r) := (continuous_w r).div_const _
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le).mp (hc.intervalIntegrable (μ := volume) 0 π)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun t => div_nonneg (weight_nonneg r t) (angleNormalizer_pos r).le)]
  rw [← intervalIntegral.integral_of_le pi_pos.le, intervalIntegral.integral_div]
  change ENNReal.ofReal (angleNormalizer r / angleNormalizer r) = 1
  simp [(angleNormalizer_pos r).ne']

private theorem integral_angleLaw (r : ℝ) (f : ℝ → ℝ) :
    (∫ t, f t ∂angleLaw r) = (∫ t in 0..π, OneLinkTransport.weight r t * f t) / angleNormalizer r := by
  have hm : Measurable (fun t => ENNReal.ofReal (OneLinkTransport.weight r t / angleNormalizer r)) :=
    ((continuous_w r).div_const _).measurable.ennreal_ofReal
  rw [angleLaw, integral_withDensity_eq_integral_toReal_smul hm (.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal (div_nonneg (weight_nonneg r _) (angleNormalizer_pos r).le),smul_eq_mul]
  rw [← intervalIntegral.integral_of_le pi_pos.le, ← intervalIntegral.integral_div]
  congr 1; funext t; ring

private theorem integral_angle_zero (f : ℝ → ℝ) :
    (∫ t, f t ∂angleLaw 0) = (2/π) * ∫ t in 0..π, sin t^2 * f t := by
  rw [integral_angleLaw]
  simp [OneLinkTransport.weight, angleNormalizer,integral_sin_sq]
  ring

private theorem int_cos {f : ℝ → ℝ} (hf : Continuous f) : Integrable (fun t => f (cos t)) (angleLaw 0) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (hf.comp continuous_cos).aestronglyMeasurable C
    (.of_forall fun t => hC _ ⟨neg_one_le_cos t,cos_le_one t⟩)

private theorem scalar_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u, f (scalarPart u) ∂su2Haar) = ∫ t, f (cos t) ∂angleLaw 0 := by
  apply eq_of_abs_sub_le_all
  intro ε hε
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf.continuousOn (ε/2) (by positivity)
  have hpEq := haar_polynomial p
  rw [← integral_angle_zero (fun t => p.eval (cos t))] at hpEq
  have ha := norm_integral_le_of_norm_le_const (μ := su2Haar) (f := fun u => p.eval (scalarPart u)-f (scalarPart u))
    (.of_forall fun u => (hp _ (scalar_range u)).le)
  have hb := norm_integral_le_of_norm_le_const (μ := angleLaw 0) (f := fun t => p.eval (cos t)-f (cos t))
    (.of_forall fun t => (hp _ ⟨neg_one_le_cos t,cos_le_one t⟩).le)
  have hInt (g : ℝ → ℝ) (hc : Continuous g) : Integrable (fun u => g (scalarPart u)) su2Haar :=
    integrable_haar (hc.comp continuous_scalar)
  rw [integral_sub (hInt _ p.continuous) (hInt _ hf)] at ha
  rw [integral_sub (int_cos p.continuous) (int_cos hf)] at hb
  simp only [probReal_univ, mul_one,Real.norm_eq_abs,abs_le] at ha hb ⊢
  constructor <;> linarith

/-- Polar-angle pushforward of the normalized Haar probability on fundamental SU(2). -/
theorem haar_polarAngle : su2Haar.map polarAngle = angleLaw 0 := by
  have hθ : Continuous polarAngle := continuous_arccos.comp continuous_scalar
  haveI := Measure.isProbabilityMeasure_map (μ := su2Haar) hθ.measurable.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hθ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  change (∫ u, f (arccos (scalarPart u)) ∂su2Haar) = _
  rw [scalar_integral (fun x => f (arccos x)) (f.continuous.comp continuous_arccos),
    integral_angle_zero, integral_angle_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le pi_pos.le] at ht
  simp only [arccos_cos ht.1 ht.2]

/-- Explicit, normalized Haar density with respect to Lebesgue measure. -/
theorem haar_polarAngle_density :
    su2Haar.map polarAngle = (volume.restrict (Ioc 0 π)).withDensity
      (fun t => ENNReal.ofReal ((2/π)*sin t^2)) := by
  rw [haar_polarAngle,angleLaw]
  congr 1
  funext t
  congr 1
  simp [OneLinkTransport.weight,angleNormalizer,integral_sin_sq]
  ring

private theorem tilted_numerator (r : ℝ) (k : G) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u, exp (r*scalarPart (u*k)) * f (polarAngle (u*k)) ∂su2Haar) =
      (2/π) * ∫ t in 0..π, OneLinkTransport.weight r t * f t := by
  let g := fun x => exp (r*x) * f (arccos x)
  have hg : Continuous g := (continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (hf.comp continuous_arccos)
  change (∫ u, g (scalarPart (u*k)) ∂su2Haar) = _
  rw [haar_rotate k (fun u => g (scalarPart u)) (hg.comp continuous_scalar),
    scalar_integral g hg, integral_angle_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le pi_pos.le] at ht
  simp [g, OneLinkTransport.weight, arccos_cos ht.1 ht.2, mul_assoc]

/-- For any field strength and pole, the polar angle measured from that pole
has the normalized density sin²(t) exp(r cos(t)) on the polar interval. -/
theorem tilted_polarAngle (r : ℝ) (k : gaugeGroup.image) :
    (su2Haar.tilted (fun u => r*(suMat (u*k) 0 0).re)).map (fun u => polarAngle (u*k)) =
      angleLaw r := by
  let field := fun u : G => r*scalarPart (u*k)
  let θ := fun u : G => polarAngle (u*k)
  have hc : Continuous field := continuous_const.mul (continuous_scalar.comp (continuous_mul_const k))
  have hθ : Continuous θ := continuous_arccos.comp (continuous_scalar.comp (continuous_mul_const k))
  haveI : IsProbabilityMeasure (su2Haar.tilted field) := isProbabilityMeasure_tilted (integrable_haar (continuous_exp.comp hc))
  haveI := Measure.isProbabilityMeasure_map (μ := su2Haar.tilted field) hθ.measurable.aemeasurable
  change (su2Haar.tilted field).map θ = angleLaw r
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hd : (∫ u, exp (field u) ∂su2Haar) = (2/π) * angleNormalizer r := by
    simpa [field, angleNormalizer] using tilted_numerator r k (fun _ => 1) continuous_const
  rw [integral_map hθ.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_tilted, integral_angleLaw, hd]
  have hp : ∀ u, (exp (field u) / ((2/π)*angleNormalizer r)) • f (θ u) =
      (exp (field u)*f (θ u)) / ((2/π)*angleNormalizer r) := fun u => by rw [smul_eq_mul]; ring
  simp_rw [hp, integral_div]
  rw [show (∫ u, exp (field u) * f (θ u) ∂su2Haar) = _ from tilted_numerator r k f f.continuous]
  field_simp [pi_pos.ne', (angleNormalizer_pos r).ne']

/-- Angular distribution of the actual energy resampling law at every background. -/
theorem heatBath_polarAngle {l : ℕ+} (hl : 1 < l.val) (β : ℝ)
    (U : Configuration gaugeGroup l) (e : Edge l) : ∃ k : gaugeGroup.image,
    (heatBath β U e).map (fun v => polarAngle (v*k)) = angleLaw (fieldStrength β U e) := by
  obtain ⟨k,hk⟩ := heatBath_eq_tilt hl β U e
  exact ⟨k, hk ▸ tilted_polarAngle _ k⟩

/-- Radial integration for any observable integrable under the actual angular
law. A single pole works for all such observables at the fixed background. -/
theorem heatBath_radial_integral {l : ℕ+} (hl : 1 < l.val) (β : ℝ)
    (U : Configuration gaugeGroup l) (e : Edge l) :
    let r := fieldStrength β U e
    ∃ k : gaugeGroup.image, ∀ f : ℝ → ℝ, Integrable f (angleLaw r) →
      (∫ v, f (polarAngle (v*k)) ∂heatBath β U e) =
        (∫ t in 0..π, OneLinkTransport.weight r t * f t) / angleNormalizer r := by
  obtain ⟨k,hk⟩ := heatBath_polarAngle hl β U e
  refine ⟨k,fun f hf => ?_⟩
  rw [← hk] at hf
  have hθ : Continuous (fun v : G => polarAngle (v*k)) :=
    continuous_arccos.comp (continuous_scalar.comp (continuous_mul_const k))
  rw [← integral_map hθ.measurable.aemeasurable hf.aestronglyMeasurable, hk, integral_angleLaw]

private theorem angle_integrable {r : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 π)) :
    Integrable f (angleLaw r) := by
  have hac : angleLaw r ≪ volume.restrict (Ioc 0 π) := withDensity_absolutelyContinuous _ _
  have hm := ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc).mono_ac hac
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply Integrable.of_bound hm C
  filter_upwards [hac.ae_le (ae_restrict_mem measurableSet_Ioc)] with t ht
  exact hC t ⟨ht.1.le,ht.2⟩

/-- Both radial trial costs have mean at most 1/12 under the Wilson resampling
measure at the same pole. The polar quotient extends continuously to the endpoints. -/
theorem heatBath_trial_cost_caps {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hmax : β ≤ 7/25) (U : Configuration gaugeGroup l) (e : Edge l) :
    let r := fieldStrength β U e
    ∃ k : gaugeGroup.image,
      (∫ v, (OneLinkTransport.polarFlux r (polarAngle (v*k)) /
        OneLinkTransport.weight r (polarAngle (v*k)))^2 ∂heatBath β U e) ≤ 1/12 ∧
      (∫ v, OneLinkTransport.transverseCost r (cos (polarAngle (v*k))) ∂heatBath β U e) ≤ 1/12 := by
  let r := fieldStrength β U e
  have hr : r ∈ Icc 0 (6*β) := fieldStrength_mem hβ U e
  obtain ⟨k,hk⟩ := heatBath_radial_integral hl β U e
  refine ⟨k,?_,?_⟩
  · have hd := hk (fun t => (OneLinkTransport.polarFlux r t / OneLinkTransport.weight r t)^2)
      (angle_integrable ((OneLinkTransport.polarSpeed_continuousOn hr.1).pow 2))
    have h (t : ℝ) : OneLinkTransport.weight r t *
        (OneLinkTransport.polarFlux r t / OneLinkTransport.weight r t)^2 =
        OneLinkTransport.polarFlux r t^2 / OneLinkTransport.weight r t := by
      by_cases hw : OneLinkTransport.weight r t = 0
      · simp [hw]
      · field_simp
    change (∫ v, (OneLinkTransport.polarFlux r (polarAngle (v*k)) /
      OneLinkTransport.weight r (polarAngle (v*k)))^2 ∂heatBath β U e) ≤ 1/12
    rw [hd]
    change (∫ t in 0..π, OneLinkTransport.weight r t *
      (OneLinkTransport.polarFlux r t / OneLinkTransport.weight r t)^2) / angleNormalizer r ≤ 1/12
    simp_rw [h]
    exact OneLinkTransport.parallel_energy_cap hr.1
  · have hc : Continuous (fun t => OneLinkTransport.transverseCost r (cos t)) := by
      unfold OneLinkTransport.transverseCost; fun_prop
    have hd := hk _ (angle_integrable hc.continuousOn)
    change (∫ v, OneLinkTransport.transverseCost r (cos (polarAngle (v*k))) ∂heatBath β U e) ≤ 1/12
    rw [hd, div_le_iff₀ (angleNormalizer_pos _)]
    simpa only [angleNormalizer,div_eq_mul_inv,one_mul,mul_comm,mul_one] using
      OneLinkTransport.transverse_integral_cap hmax hr

/-- The regular conditional law has the same angle distribution for Wilson-marginal
almost every background. Its pole can depend on that background. -/
theorem condKernel_polarAngle {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    ∀ᵐ b ∂(splitLaw β e).fst, ∃ k : gaugeGroup.image,
      ((splitLaw β e).condKernel b).map (fun v => polarAngle (v*k)) =
        angleLaw (fieldStrength β ((splitLink e).symm (b,1)) e) := by
  filter_upwards [heatBath_eq_condKernel β e] with b hb
  rw [← hb]
  exact heatBath_polarAngle hl β _ e

#print axioms haar_polarAngle_density
#print axioms haar_polarAngle
#print axioms angleLaw_probability
#print axioms tilted_polarAngle
#print axioms heatBath_polarAngle
#print axioms heatBath_radial_integral
#print axioms heatBath_trial_cost_caps
#print axioms condKernel_polarAngle

end
end YangMills.PeriodicWilson
