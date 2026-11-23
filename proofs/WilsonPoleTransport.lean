-- SPDX-License-Identifier: Apache-2.0
import WilsonLinkTransport
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real Set Filter
open scoped Topology ENNReal NNReal Matrix.Norms.Frobenius
noncomputable section
private abbrev G := gaugeGroup.image
private abbrev period := 2*π

/-- The unit-speed circle subgroup through the diagonal axis conjugated by n. -/
private def circle (n : G) (t : ℝ) : G := n * diagonalLink t * n⁻¹

@[fun_prop] private theorem circle_cont (n : G) : Continuous (circle n) :=
  (continuous_const.mul continuous_diag).mul continuous_const

@[simp] private theorem circle_zero (n : G) : circle n 0 = 1 := by simp [circle]
private theorem circle_add (n : G) (a b : ℝ) : circle n (a+b) = circle n a * circle n b := by
  rw [circle,diagonalLink_add]; unfold circle; group
private theorem circle_periodic (n : G) : Function.Periodic (circle n) period := by
  intro t; simp only [circle,diagonalLink_periodic t]

private def rho (r : ℝ) (u : G) := exp (r*(suMat u 0 0).re)
@[fun_prop] private theorem rho_cont (r : ℝ) : Continuous (rho r) :=
  continuous_exp.comp (continuous_const.mul continuous_scalar_link)
private theorem rho_pos (r : ℝ) (u : G) : 0 < rho r u := exp_pos _
private theorem rho_bounds {r : ℝ} (hr : 0 ≤ r) (u : G) :
    exp (-r) ≤ rho r u ∧ rho r u ≤ exp r := by
  unfold rho
  rw [← cos_polarAngle]
  constructor <;> apply exp_le_exp.mpr
  · simpa using mul_le_mul_of_nonneg_left (neg_one_le_cos (polarAngle u)) hr
  · simpa using mul_le_mul_of_nonneg_left (cos_le_one (polarAngle u)) hr

-- Measure backwards along the circle in units of unnormalized tilted mass.
private def sweptMass (r : ℝ) (n u : G) (b : ℝ) :=
  ∫ x in 0..b, rho r (u*circle n (-x))

private theorem swept_cont (r : ℝ) (n : G) : Continuous (Function.uncurry (sweptMass r n)) :=
  intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun u x => rho r (u*circle n (-x))) (by unfold Function.uncurry; fun_prop)

private theorem swept_deriv (r : ℝ) (n u : G) (b : ℝ) :
    HasDerivAt (sweptMass r n u) (rho r (u*circle n (-b))) b := by
  have hc : Continuous (fun x => rho r (u*circle n (-x))) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem swept_strict (r : ℝ) (n u : G) : StrictMono (sweptMass r n u) :=
  strictMono_of_deriv_pos fun b => by rw [(swept_deriv r n u b).deriv]; exact rho_pos ..

private theorem swept_bounds {r b : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) (n u : G) :
    exp (-r)*b ≤ sweptMass r n u b ∧ sweptMass r n u b ≤ exp r*b := by
  have hc : Continuous (fun x => rho r (u*circle n (-x))) := by fun_prop
  have hl := intervalIntegral.integral_mono_on (μ := volume) hb intervalIntegrable_const (hc.intervalIntegrable _ _)
    (fun x _ => (rho_bounds hr (u*circle n (-x))).1)
  have hh := intervalIntegral.integral_mono_on (μ := volume) hb (hc.intervalIntegrable _ _) intervalIntegrable_const
    (fun x _ => (rho_bounds hr (u*circle n (-x))).2)
  simpa [sweptMass,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using And.intro hl hh

private theorem exists_retreat {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) (u : G) :
    ∃ b : ℝ, 0 ≤ b ∧ sweptMass r n u b = c := by
  let B := (c:ℝ) / exp (-r)
  have hB : 0 ≤ B := div_nonneg c.2 (exp_pos _).le
  have h : (c:ℝ) ≤ sweptMass r n u B := calc
    _ = exp (-r)*B := by dsimp [B]; field_simp
    _ ≤ _ := (swept_bounds hr hB n u).1
  have hc : Continuous (sweptMass r n u) := (swept_cont r n).comp (continuous_const.prodMk continuous_id)
  obtain ⟨b,hb,he⟩ := intermediate_value_Icc hB hc.continuousOn
    (show (c:ℝ) ∈ Icc (sweptMass r n u 0) (sweptMass r n u B) from ⟨by simp [sweptMass],h⟩)
  exact ⟨b,hb.1,he⟩

private def retreat {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) (u : G) :=
  (exists_retreat hr n c u).choose
private theorem retreat_spec {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) (u : G) :
    0 ≤ retreat hr n c u ∧ sweptMass r n u (retreat hr n c u) = c :=
  (exists_retreat hr n c u).choose_spec

private theorem retreat_joint_cont {r : ℝ} (hr : 0 ≤ r) (n : G) :
    Continuous (fun p : ℝ≥0 × G => retreat hr n p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_order.mpr
  have hc (b : ℝ) : Continuous (fun q : ℝ≥0 × G => sweptMass r n q.2 b) :=
    (swept_cont r n).comp (continuous_snd.prodMk continuous_const)
  have hd : Continuous (fun q : ℝ≥0 × G => (q.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  constructor
  · intro b hb
    have hlt := swept_strict r n p.2 hb
    rw [(retreat_spec hr n p.1 p.2).2] at hlt
    filter_upwards [(isOpen_lt (hc b) hd).mem_nhds hlt] with q hq
    apply (swept_strict r n q.2).lt_iff_lt.mp
    rwa [(retreat_spec hr n q.1 q.2).2]
  · intro b hb
    have hlt := swept_strict r n p.2 hb
    rw [(retreat_spec hr n p.1 p.2).2] at hlt
    filter_upwards [(isOpen_lt hd (hc b)).mem_nhds hlt] with q hq
    apply (swept_strict r n q.2).lt_iff_lt.mp
    rwa [(retreat_spec hr n q.1 q.2).2]

@[fun_prop] private theorem retreat_cont {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) :
    Continuous (retreat hr n c) := by
  exact (retreat_joint_cont hr n).comp (f := fun u : G => (c,u)) (continuous_const.prodMk continuous_id)

private def massShift {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) (u : G) :=
  u * circle n (-(retreat hr n c u))
@[fun_prop] private theorem massShift_cont {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) :
    Continuous (massShift hr n c) := by unfold massShift; fun_prop

-- On a lifted orbit t ↦ u A(t), the mass shift has Jacobian w(t)/w(S(t)).
private theorem orbit_change_of_variables {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0)
    (u : G) (f : G → ℝ) (hf : Continuous f) :
    (∫ t in 0..period, rho r (u*circle n t) * f (massShift hr n c (u*circle n t))) =
    ∫ t in 0..period, rho r (u*circle n t) * f (u*circle n t) := by
  let x := fun t => u*circle n t
  let w := fun t => rho r (x t)
  let S := fun t => t - retreat hr n c (x t)
  let W := fun t => ∫ a in 0..t, w a
  have cx : Continuous x := continuous_const.mul (circle_cont _)
  have cw : Continuous w := (rho_cont _).comp cx
  have cs : Continuous S := continuous_id.sub ((retreat_cont hr n c).comp cx)
  have dW (t : ℝ) : HasDerivAt W (w t) t := intervalIntegral.integral_hasDerivAt_right
    (cw.intervalIntegrable _ _) cw.aestronglyMeasurable.stronglyMeasurableAtFilter cw.continuousAt
  have shift (t : ℝ) : massShift hr n c (x t) = x (S t) := by
    unfold massShift x S; rw [sub_eq_add_neg,circle_add,mul_assoc]
  have clock (t : ℝ) : W (S t) = W t - c := by
    have he := (retreat_spec hr n c (x t)).2
    have hw (a : ℝ) : rho r (x t * circle n (-a)) = w (t-a) := by
      dsimp [x,w]; rw [sub_eq_add_neg,circle_add,mul_assoc]
    unfold sweptMass at he
    simp_rw [hw,intervalIntegral.integral_comp_sub_left, sub_zero] at he
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (cw.intervalIntegrable (μ := volume) 0 (S t)) (cw.intervalIntegrable _ t)
    change (∫ a in S t..t, w a) = c at he
    dsimp [W]; linarith only [hsum,he]
  have dS (t : ℝ) : HasDerivAt S (w t / w (S t)) t :=
    HasDerivAt.of_comp_left cs.continuousAt (dW _) ((dW t).sub_const (c:ℝ))
      (rho_pos _ _).ne' (.of_forall clock)
  have cjac : Continuous (fun t => w t / w (S t)) := cw.div (cw.comp cs) (fun _ => (rho_pos _ _).ne')
  let F := fun t => w t * f (x t)
  have cF : Continuous F := cw.mul (hf.comp cx)
  have hp (t : ℝ) : x (t+period) = x t := by dsimp [x]; rw [circle_periodic]
  have hF : Function.Periodic F period := by intro t; dsimp [F,w]; rw [hp]
  have hS : S period = S 0 + period := by
    have h0 : x period = x 0 := by simpa using hp 0
    dsimp [S]; rw [h0]; ring
  have changeVars := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := period)
    (fun t _ => dS t) cjac.continuousOn cF
  have hfun (t : ℝ) : (F ∘ S) t * (w t / w (S t)) = w t * f (massShift hr n c (x t)) := by
    have hnonzero : w (S t) ≠ 0 := (rho_pos r _).ne'
    rw [shift]; dsimp [Function.comp,F]; field_simp [hnonzero]
  simp_rw [hfun] at changeVars
  rw [hS] at changeVars
  exact changeVars.trans (by simpa using hF.intervalIntegral_add_eq (S 0) 0)

-- Haar averaging turns an identity on every circle orbit into a group integral identity.
private theorem haar_orbit_average (n : G) (F : G → ℝ) (hF : Continuous F) :
    (∫ u, (∫ t in 0..period, F (u*circle n t)) ∂su2Haar) = period * ∫ u, F u ∂su2Haar := by
  have hc : Continuous (fun z : ℝ × G => F (z.2*circle n z.1)) := by fun_prop
  obtain ⟨M,hM⟩ := isCompact_univ (X := G) |>.exists_bound_of_continuousOn hF.continuousOn
  have hi : Integrable (Function.uncurry fun t u => F (u*circle n t))
      ((volume.restrict (uIoc 0 period)).prod su2Haar) := by
    rw [uIoc_of_le (by positivity : 0 ≤ period)]
    exact Integrable.of_bound hc.aestronglyMeasurable M (.of_forall fun z => hM _ (mem_univ _))
  rw [← intervalIntegral_integral_swap hi]
  have hh (t : ℝ) : (∫ u, F (u*circle n t) ∂su2Haar) = ∫ u, F u ∂su2Haar := by
    have hp := preserve_right (circle n t)
    rw [← integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable,hp.map_eq]
  simp_rw [hh]
  simp [intervalIntegral.integral_const,smul_eq_mul]

private theorem massShift_preserves {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) :
    MeasurePreserving (massShift hr n c) (poleLaw r 1) (poleLaw r 1) := by
  let T := massShift hr n c
  have hT : Continuous T := massShift_cont hr n c
  haveI := Measure.isProbabilityMeasure_map (μ := poleLaw r 1) hT.aemeasurable
  refine ⟨hT.measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT.aemeasurable f.continuous.aestronglyMeasurable]
  have hperiod : period ≠ 0 := by positivity
  have eqInt : (∫ u, rho r u * f (T u) ∂su2Haar) = ∫ u, rho r u * f u ∂su2Haar := by
    apply mul_left_cancel₀ hperiod
    rw [← haar_orbit_average n (fun u => rho r u * f (T u)) ((rho_cont r).mul (f.continuous.comp hT)),
      ← haar_orbit_average n (fun u => rho r u * f u) ((rho_cont r).mul f.continuous)]
    exact integral_congr_ae (.of_forall fun u => orbit_change_of_variables hr n c u f f.continuous)
  unfold poleLaw
  simp_rw [integral_tilted,mul_one,smul_eq_mul,div_mul_eq_mul_div,integral_div]
  exact congrArg (fun x => x / ∫ u, rho r u ∂su2Haar) eqInt

private theorem change_pole (r : ℝ) (k j : G) :
    MeasurePreserving (fun u => u*k*j⁻¹) (poleLaw r k) (poleLaw r j) := by
  have hc : Continuous (fun u : G => u*k*j⁻¹) := (continuous_mul_const k).mul continuous_const
  refine ⟨hc.measurable,?_⟩
  rw [← orbitLink_law r k,← orbitLink_law r j,Measure.map_map hc.measurable (continuous_orbit k).measurable]
  congr 1
  funext z
  change orbitLink k z.1 z.2 * k * j⁻¹ = orbitLink j z.1 z.2
  unfold orbitLink; group

private def massStep (r d : ℝ) (hd : 0 ≤ d) : ℝ≥0 := ⟨d / cosh r, div_nonneg hd (cosh_pos _).le⟩

private theorem retreat_distance {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (n u : G) :
    |d - retreat hr n (massStep r d hd) u| ≤ tanh r * d := by
  let c := massStep r d hd
  let b := retreat hr n c u
  have hb := retreat_spec hr n c u
  have hh := swept_bounds hr hb.1 n u
  rw [hb.2] at hh
  have hlo : (c:ℝ)*exp (-r) ≤ b := calc
    _ ≤ (exp r*b)*exp (-r) := mul_le_mul_of_nonneg_right hh.2 (exp_pos _).le
    _ = b := by rw [exp_neg]; field_simp
  have hhi : b ≤ (c:ℝ)*exp r := calc
    b = (exp (-r)*b)*exp r := by rw [exp_neg]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh.1 (exp_pos _).le
  have hminus : (c:ℝ)*exp (-r) = (1-tanh r)*d := by
    change d / cosh r * exp (-r) = _
    rw [← cosh_sub_sinh,tanh_eq_sinh_div_cosh]
    field_simp [(cosh_pos r).ne']
  have hplus : (c:ℝ)*exp r = (1+tanh r)*d := by
    change d / cosh r * exp r = _
    rw [← cosh_add_sinh,tanh_eq_sinh_div_cosh]
    field_simp [(cosh_pos r).ne']
  rw [hminus] at hlo; rw [hplus] at hhi
  change |d-b| ≤ _
  exact abs_le.mpr ⟨by linarith only [hhi],by linarith only [hlo]⟩

private theorem compensated_rotation {r : ℝ} (hr : 0 ≤ r) (k j n : G) (d : ℝ)
    (hn : j⁻¹*k = circle n d) (c : ℝ≥0) :
    ∃ T : G → G, Continuous T ∧ MeasurePreserving T (poleLaw r k) (poleLaw r j) ∧
      ∀ u, linkGeodesic u (T u) ≤ |d - retreat hr n c (u*k)| := by
  let T := fun u : G => massShift hr n c (u*k)*j⁻¹
  have hp₁ : MeasurePreserving (fun u : G => u*k) (poleLaw r k) (poleLaw r 1) := by
    simpa only [inv_one,mul_one] using change_pole r k 1
  have hp₂ : MeasurePreserving (fun v : G => v*j⁻¹) (poleLaw r 1) (poleLaw r j) := by
    simpa only [inv_one,mul_one] using change_pole r 1 j
  have hT : Continuous T := ((massShift_cont hr n c).comp (continuous_mul_const k)).mul continuous_const
  refine ⟨T,hT,hp₂.comp ((massShift_preserves hr n c).comp hp₁),?_⟩
  intro u
  let b := retreat hr n c (u*k)
  have hTk : T u*k = (u*k)*circle n (d-b) := by
    change (u*k*circle n (-b)*j⁻¹)*k = _
    rw [mul_assoc _ j⁻¹ k,hn, mul_assoc, ← circle_add]
    congr 2; ring
  calc
    linkGeodesic u (T u) = linkGeodesic (u*k) (T u*k) := (linkGeodesic_mul_right ..).symm
    _ = linkGeodesic (circle n 0) (circle n (d-b)) := by
      rw [hTk,circle_zero,← linkGeodesic_mul_left 1 _ (u*k),mul_one]
    _ = linkGeodesic (diagonalLink 0) (diagonalLink (d-b)) := by
      unfold circle; rw [linkGeodesic_mul_right,linkGeodesic_mul_left]
    _ ≤ |d-b| := by simpa only [zero_sub,abs_neg] using diagonalLink_distance_le 0 (d-b)

private theorem pole_circle (k j : G) : ∃ n : G, j⁻¹*k = circle n (linkGeodesic k⁻¹ j⁻¹) := by
  obtain ⟨n,hn⟩ := link_conjugate_diagonal (j⁻¹*k)
  have he : polarAngle (j⁻¹*k) = linkGeodesic k⁻¹ j⁻¹ := calc
    _ = linkGeodesic j⁻¹ k⁻¹ := by simp [linkGeodesic]
    _ = _ := by simp only [linkGeodesic_eq_angle]; exact InnerProductGeometry.angle_comm ..
  exact ⟨n,he ▸ hn⟩

/-- A pointwise displacement bound for the compensated rotation. -/
theorem pole_transport_map {r : ℝ} (hr : 0 ≤ r) (k j : G) :
    ∃ T : G → G, Continuous T ∧ MeasurePreserving T (poleLaw r k) (poleLaw r j) ∧
      ∀ u, linkGeodesic u (T u) ≤ tanh r * linkGeodesic k⁻¹ j⁻¹ := by
  obtain ⟨n,hn⟩ := pole_circle k j
  have hd : 0 ≤ linkGeodesic k⁻¹ j⁻¹ := arccos_nonneg _
  obtain ⟨T,hT,hp,hm⟩ := compensated_rotation hr k j n _ hn (massStep r _ hd)
  exact ⟨T,hT,hp,fun u => (hm u).trans (retreat_distance hr hd n (u*k))⟩

-- Mean-square speed under the centered tilt. The reciprocal weight compensates
-- the pole rotation along each circle orbit.
private def partition (r : ℝ) := ∫ u, rho r u ∂su2Haar

private theorem partition_angle (r : ℝ) : partition r = (2/π)*angleNormalizer r := by
  simpa [partition,rho,angleNormalizer] using tilted_haar_numerator r 1 (fun _ => 1) continuous_const

private theorem partition_pos (r : ℝ) : 0 < partition r := by
  rw [partition_angle]; exact mul_pos (by positivity) (angleNormalizer_pos _)

private theorem partition_even (r : ℝ) : partition (-r) = partition r := by
  simp only [partition_angle,angleNormalizer]
  congr 1
  have h (t : ℝ) : OneLinkTransport.weight (-r) t = OneLinkTransport.weight r (π-t) := by
    simp [OneLinkTransport.weight,sin_pi_sub,cos_pi_sub]
  simp_rw [h,intervalIntegral.integral_comp_sub_left,sub_self,sub_zero]

private theorem partition_gaussian {r : ℝ} (hr : 0 ≤ r) : partition r ≤ exp (r^2/8) := by
  let F := fun t => partition t * exp (-(t^2/8))
  have hder (t : ℝ) : HasDerivAt (partition) ((2/π)*∫ x in 0..π, OneLinkTransport.weight t x*cos x) t := by
    simpa only [funext partition_angle,angleNormalizer] using (weightMass_hasDerivAt t π).const_mul (2/π)
  have hF (t : ℝ) : HasDerivAt F
      (((2/π)*∫ x in 0..π, OneLinkTransport.weight t x*cos x) * exp (-(t^2/8)) -
        partition t * (t/4) * exp (-(t^2/8))) t := by
    apply HasDerivAt.congr_deriv ((hder t).mul ((((hasDerivAt_id t).pow 2).div_const 8).neg.exp))
    simp only [id_eq,Pi.pow_apply,Pi.neg_apply]; ring
  have mono : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt).continuousOn
    · exact (show Differentiable ℝ F from fun t => (hF t).differentiableAt).differentiableOn
    intro t ht
    have ht0 : 0 ≤ t := interior_subset ht
    let w := OneLinkTransport.weight t
    have hw : Continuous w := by unfold w OneLinkTransport.weight; fun_prop
    have hprim (x : ℝ) : HasDerivAt (fun y => sin y^3 * exp (t*cos y))
        (3*(w x*cos x)-t*(w x*sin x^2)) x := by
      apply HasDerivAt.congr_deriv (((hasDerivAt_sin x).pow 3).mul (((hasDerivAt_cos x).const_mul t).exp))
      simp only [Pi.pow_apply]; unfold w OneLinkTransport.weight; ring
    have ha : Continuous (fun x => 3*(w x*cos x)) := continuous_const.mul (hw.mul continuous_cos)
    have hb : Continuous (fun x => t*(w x*sin x^2)) := continuous_const.mul (hw.mul (continuous_sin.pow 2))
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
      (fun x _ => hprim x) ((ha.sub hb).intervalIntegrable (μ := volume) _ _)
    rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
    simp only [sin_pi,sin_zero,zero_pow (by decide : 3 ≠ 0),zero_mul,sub_zero] at he
    have hm := mul_le_mul_of_nonneg_left (OneLinkTransport.sin_moment_cap ht0) ht0
    change t*(∫ x in 0..π, w x*sin x^2) ≤ t*((3/4)*∫ x in 0..π, w x) at hm
    have hh : (∫ x in 0..π, w x*cos x) ≤ (∫ x in 0..π, w x)*(t/4) := by linarith only [he,hm]
    rw [(hF t).deriv,partition_angle]
    apply sub_nonpos.mpr
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hh (by positivity)
  have h := mono (show (0:ℝ) ∈ Ici 0 from show (0:ℝ) ≤ 0 from le_rfl) (show r ∈ Ici 0 from hr) hr
  have hzero : partition 0 = 1 := by simp [partition,rho]
  simpa [F,hzero,exp_neg,← div_eq_mul_inv,div_le_one (exp_pos _)] using h

private def rotationSpeed (r : ℝ) (u : G) := 1 - (rho r u)⁻¹

@[fun_prop] private theorem speed_cont (r : ℝ) : Continuous (rotationSpeed r) :=
  continuous_const.sub ((rho_cont r).inv₀ fun u => (rho_pos r u).ne')

private theorem rotation_energy {r : ℝ} (hr : 0 ≤ r) :
    (∫ u, rotationSpeed r u^2 ∂poleLaw r 1) ≤ (r/2)^2 := by
  have hi (s : ℝ) : Integrable (rho s) su2Haar :=
    (rho_cont s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf (u : G) : rho r u * rotationSpeed r u^2 = rho r u - 2 + rho (-r) u := by
    have he : rho (-r) u = (rho r u)⁻¹ := by simp [rho,exp_neg]
    rw [he]; unfold rotationSpeed; field_simp [(rho_pos r u).ne']; ring
  rw [poleLaw,integral_tilted]
  simp only [mul_one,smul_eq_mul,div_mul_eq_mul_div]
  change (∫ u, (rho r u * rotationSpeed r u^2)/partition r ∂su2Haar) ≤ _
  simp_rw [hf,integral_div]
  have hiSub : Integrable (fun u => rho r u - 2) su2Haar := (hi r).sub (integrable_const _)
  rw [integral_add hiSub (hi (-r)),integral_sub (hi r) (integrable_const (2:ℝ))]
  change (partition r - _ + partition (-r)) / partition r ≤ _
  rw [integral_const,probReal_univ,one_smul,partition_even]
  have hg := one_div_le_one_div_of_le (partition_pos r) (partition_gaussian hr)
  have h := Real.add_one_le_exp (-(r^2/8))
  rw [exp_neg,← one_div] at h
  have he : (partition r-2+partition r)/partition r = 2*(1-1/partition r) := by field_simp [(partition_pos r).ne']; ring
  rw [he]; linarith only [hg,h]

private theorem retreat_energy {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (n : G) :
    (∫ u, (d - retreat hr n d.toNNReal u)^2 ∂poleLaw r 1) ≤ (r/2*d)^2 := by
  let μ := poleLaw r 1
  let B := fun (t : ℝ) (u : G) => retreat hr n t.toNNReal u
  let S := fun (t : ℝ) (u : G) => massShift hr n t.toNNReal u
  let v := fun t u => rotationSpeed r (S t u)
  have cB : Continuous (Function.uncurry B) := (retreat_joint_cont hr n).comp
    (f := fun p : ℝ × G => (p.1.toNNReal,p.2)) ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  have cS : Continuous (Function.uncurry S) := continuous_snd.mul ((circle_cont n).comp cB.neg)
  have cv : Continuous (Function.uncurry v) := (speed_cont r).comp cS
  have bz (u : G) : B 0 u = 0 := (swept_strict r n u).injective (by
    rw [(retreat_spec hr n _ u).2]; simp [sweptMass])
  have step (u : G) : (d-B d u)^2 ≤ d * ∫ t in 0..d, v t u^2 := by
    rcases hd.eq_or_lt with h | h
    · simp [← h,bz]
    have cb : Continuous (fun t => B t u) := cB.comp (f := fun t => (t,u)) (continuous_id.prodMk continuous_const)
    have cf : Continuous (fun t => v t u) := cv.comp (f := fun t => (t,u)) (continuous_id.prodMk continuous_const)
    have derivB {t : ℝ} (ht : 0 < t) : HasDerivAt (fun x => B x u) (rho r (S t u))⁻¹ t := by
      have he : ∀ᶠ x in 𝓝 t, sweptMass r n u (B x u) = x := by
        filter_upwards [Ioi_mem_nhds ht] with x hx
        exact (retreat_spec hr n _ u).2.trans (Real.coe_toNNReal x hx.le)
      simpa only [one_div,S,massShift,B] using HasDerivAt.of_comp_left cb.continuousAt (swept_deriv r n u (B t u))
        (hasDerivAt_id t) (rho_pos _ _).ne' he
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.le
      (continuous_id.sub cb).continuousOn (fun t ht => (hasDerivAt_id t).sub (derivB ht.1))
      (cf.intervalIntegrable (μ := volume) _ _)
    have he' : (∫ t in 0..d, v t u) = d-B d u := by simpa [bz,v,rotationSpeed] using he
    simpa only [sub_zero] using interval_square_increment h cf he'
  obtain ⟨M,hM⟩ := isCompact_univ (X := G) |>.exists_bound_of_continuousOn ((speed_cont r).pow 2).continuousOn
  have hi : Integrable (Function.uncurry fun t u => v t u^2) ((volume.restrict (Ioc 0 d)).prod μ) :=
    Integrable.of_bound (cv.pow 2).aestronglyMeasurable M (.of_forall fun z => hM _ (mem_univ _))
  have hi' : Integrable (fun u => ∫ t in 0..d, v t u^2) μ := by
    simp_rw [intervalIntegral.integral_of_le hd]; exact hi.integral_prod_right
  have idem (t : ℝ) : (∫ u, v t u^2 ∂μ) = ∫ u, rotationSpeed r u^2 ∂μ := by
    have hp := massShift_preserves hr n t.toNNReal
    calc _ = ∫ u, rotationSpeed r u^2 ∂μ.map (S t) :=
            (integral_map hp.measurable.aemeasurable (f := fun u => rotationSpeed r u^2)
              ((speed_cont r).pow 2).aestronglyMeasurable).symm
         _ = _ := by rw [show μ.map (S t) = μ from hp.map_eq]
  have hb := integral_mono (((continuous_const.sub (retreat_cont hr n d.toNNReal)).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := μ)) (hi'.const_mul d) step
  rw [integral_const_mul, ← intervalIntegral_integral_swap (f := fun t u => v t u^2)
    (by simpa only [uIoc_of_le hd] using hi)] at hb
  simp_rw [idem,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hb
  apply hb.trans
  calc d*(d*_) ≤ d*(d*(r/2)^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rotation_energy hr) hd) hd
       _ = _ := by ring

/-- A full-link transport map whose root mean square geodesic displacement is at
most half the field strength times the angle between poles. -/
theorem mean_square_pole_transport {r : ℝ} (hr : 0 ≤ r) (k j : G) :
    ∃ T : G → G, Continuous T ∧ MeasurePreserving T (poleLaw r k) (poleLaw r j) ∧
      (∫ u, linkGeodesic u (T u)^2 ∂poleLaw r k) ≤ (r/2 * linkGeodesic k⁻¹ j⁻¹)^2 := by
  let d := linkGeodesic k⁻¹ j⁻¹
  have hd : 0 ≤ d := arccos_nonneg _
  obtain ⟨n,hn⟩ := pole_circle k j
  obtain ⟨T,hT,hp,hm⟩ := compensated_rotation hr k j n d hn d.toNNReal
  refine ⟨T,hT,hp,?_⟩
  let f := fun u : G => (d-retreat hr n d.toNNReal u)^2
  have cf : Continuous f := (continuous_const.sub (retreat_cont hr n _)).pow 2
  have cdist := continuous_geodesic.comp (continuous_id.prodMk hT)
  have cp : MeasurePreserving (fun u : G => u*k) (poleLaw r k) (poleLaw r 1) := by
    simpa using change_pole r k 1
  calc _ ≤ ∫ u, f (u*k) ∂poleLaw r k := integral_mono
          ((cdist.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          ((cf.comp (continuous_mul_const k)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (fun u => (pow_le_pow_left₀ (arccos_nonneg _) (hm u) 2).trans_eq (sq_abs _))
       _ = ∫ u, f u ∂poleLaw r 1 := by
          rw [← cp.map_eq,integral_map cp.measurable.aemeasurable cf.aestronglyMeasurable]
       _ ≤ _ := retreat_energy hr hd n

private theorem geodesic_comm (u v : G) : linkGeodesic u v = linkGeodesic v u := by
  simp only [linkGeodesic_eq_angle]; exact InnerProductGeometry.angle_comm ..

theorem linkWassersteinSq_symm (μ ν : Measure G) : linkWassersteinSq μ ν = linkWassersteinSq ν μ := by
  suffices h : ∀ μ ν : Measure G, linkWassersteinSq μ ν ≤ linkWassersteinSq ν μ from le_antisymm (h μ ν) (h ν μ)
  intro μ ν
  apply le_iInf
  intro γ
  let γ' : {P : Measure (G × G) // P.fst = μ ∧ P.snd = ν} :=
    ⟨γ.val.map Prod.swap,by simpa only [Measure.fst_map_swap] using γ.prop.2,
      by simpa only [Measure.snd_map_swap] using γ.prop.1⟩
  apply (iInf_le _ γ').trans_eq
  change (∫⁻ z, ENNReal.ofReal (linkGeodesic z.1 z.2 ^ 2) ∂γ.val.map Prod.swap) = _
  have hc : Measurable (fun z : G × G => ENNReal.ofReal (linkGeodesic z.1 z.2 ^ 2)) :=
    (continuous_geodesic.pow 2).measurable.ennreal_ofReal
  rw [lintegral_map hc measurable_swap]
  exact lintegral_congr fun z => congrArg (fun a => ENNReal.ofReal (a^2)) (geodesic_comm z.2 z.1)

theorem rms_triangle {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (P : Measure X) [IsFiniteMeasure P]
    {f g h : X → ℝ} (cf : Continuous f) (cg : Continuous g) (ch : Continuous h)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : 0 ≤ᵐ[P] g) (hh0 : 0 ≤ᵐ[P] h) (htri : ∀ z, f z ≤ g z+h z)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbase : (∫ z, g z^2 ∂P) ≤ R^2) (hmove : (∫ z, h z^2 ∂P) ≤ C^2) :
    (∫ z, f z^2 ∂P) ≤ (R+C)^2 := by
  have hi : Integrable (fun z => f z^2) P := (cf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have intg : Integrable (fun z => g z^2) P := (cg.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have inth : Integrable (fun z => h z^2) P := (ch.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have intgh : Integrable (fun z => g z*h z) P := (cg.mul ch).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hg0 hh0
      (cg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (ch.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow] at hcs
  have hcross : (∫ z, g z*h z ∂P) ≤ R*C := hcs.trans (mul_le_mul
    ((sqrt_le_sqrt hbase).trans_eq (sqrt_sq hR)) ((sqrt_le_sqrt hmove).trans_eq (sqrt_sq hC))
    (sqrt_nonneg _) hR)
  have hpoint (z : X) : f z^2 ≤ (g z^2 + 2*(g z*h z)) + h z^2 := calc
    _ ≤ (g z+h z)^2 := pow_le_pow_left₀ (hf0 z) (htri z) 2
    _ = _ := by ring
  have hprod : Integrable (fun z => 2*(g z*h z)) P := intgh.const_mul 2
  have hsum : Integrable (fun z => g z^2 + 2*(g z*h z)) P := intg.add hprod
  have hm := integral_mono hi (hsum.add inth) hpoint
  change (∫ z, f z^2 ∂P) ≤ ∫ z, (g z^2 + 2*(g z*h z)) + h z^2 ∂P at hm
  rw [integral_add hsum inth,integral_add intg hprod,integral_const_mul] at hm
  change (∫ z, g z^2 ∂P) ≤ R^2 at hbase
  linarith only [hm,hbase,hcross,hmove]

private theorem continuous_move (T : G → G) (hT : Continuous T) :
    Continuous (fun u => linkGeodesic u (T u)) := by
  unfold linkGeodesic polarAngle
  exact continuous_arccos.comp (continuous_scalar_link.comp (continuous_id.mul hT.inv))

-- Modify one endpoint of a coupling whose root mean square cost is at most R.
private theorem transfer_cost (P : Measure (G × G)) [IsProbabilityMeasure P] (T : G → G)
    (hT : Continuous T) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbase : (∫ z, linkGeodesic z.1 z.2^2 ∂P) ≤ R^2)
    (hmove : (∫ u, linkGeodesic u (T u)^2 ∂P.snd) ≤ C^2) :
    linkWassersteinSq P.fst (P.snd.map T) ≤ ENNReal.ofReal ((R+C)^2) := by
  let M := fun z : G × G => (z.1,T z.2)
  have hM : Continuous M := continuous_fst.prodMk (hT.comp continuous_snd)
  have hmarg : (P.map M).fst = P.fst ∧ (P.map M).snd = P.snd.map T := by
    constructor
    · exact Measure.fst_map_prodMk (hT.comp continuous_snd).measurable
    · rw [show (P.map M).snd = P.map (fun z => T z.2) from Measure.snd_map_prodMk measurable_fst]
      exact (Measure.map_map hT.measurable measurable_snd).symm
  let γ : {Q : Measure (G × G) // Q.fst = P.fst ∧ Q.snd = P.snd.map T} := ⟨P.map M,hmarg⟩
  apply (iInf_le _ γ).trans
  let f := fun z : G × G => linkGeodesic z.1 (T z.2)
  let g := fun z : G × G => linkGeodesic z.1 z.2
  have cf : Continuous f := by
    unfold f linkGeodesic polarAngle
    exact continuous_arccos.comp (continuous_scalar_link.comp (continuous_fst.mul (hT.comp continuous_snd).inv))
  have cg : Continuous g := continuous_geodesic
  have hc : Measurable (fun z : G × G => ENNReal.ofReal (linkGeodesic z.1 z.2^2)) :=
    (cg.pow 2).measurable.ennreal_ofReal
  change (∫⁻ z, ENNReal.ofReal (linkGeodesic z.1 z.2 ^ 2) ∂P.map M) ≤ _
  rw [lintegral_map hc hM.measurable]
  change (∫⁻ z, ENNReal.ofReal (f z^2) ∂P) ≤ _
  have hi : Integrable (fun z => f z^2) P := (cf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun z => sq_nonneg (f z))]
  apply ENNReal.ofReal_le_ofReal
  let h := fun z : G × G => linkGeodesic z.2 (T z.2)
  have ch₀ := continuous_move T hT
  have ch : Continuous h := ch₀.comp continuous_snd
  have move : (∫ z, h z^2 ∂P) ≤ C^2 := by
    change (∫ u, linkGeodesic u (T u)^2 ∂P.map Prod.snd) ≤ C^2 at hmove
    rw [integral_map (f := fun u => linkGeodesic u (T u)^2) measurable_snd.aemeasurable
      (ch₀.pow 2).aestronglyMeasurable] at hmove
    exact hmove
  exact rms_triangle P cf cg ch (fun _ => arccos_nonneg _) (.of_forall fun _ => arccos_nonneg _)
    (.of_forall fun _ => arccos_nonneg _) (fun z => geo_triangle z.1 z.2 (T z.2)) hR hC hbase move

private theorem endpoint_transport_bound {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) {C : ℝ} (hC : 0 ≤ C)
    (T : G → G) (hT : Continuous T) (hp : MeasurePreserving T (poleLaw s k) (poleLaw s j))
    (hmove : (∫ u, linkGeodesic u (T u)^2 ∂poleLaw s k) ≤ C^2) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + C)^2) := by
  let P := linkCoupling r s k k
  obtain ⟨hfst,hsnd⟩ := linkCoupling_marginals r s k k
  haveI : IsProbabilityMeasure P := ⟨by
    change linkCoupling r s k k univ = 1
    rw [← Measure.fst_univ,hfst,measure_univ]⟩
  have hR : 0 ≤ |s-r|/sqrt 12 := by positivity
  have hbase : (∫ z, linkGeodesic z.1 z.2^2 ∂P) ≤ (|s-r|/sqrt 12)^2 := by
    rw [div_pow,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12),linkCoupling_common_cost]
    exact radialCoupling_cost hr hs
  have hmm : (∫ u, linkGeodesic u (T u)^2 ∂P.snd) ≤ C^2 := by simpa only [P,hsnd] using hmove
  have h := transfer_cost P T hT hR hC hbase hmm
  simpa only [P,hfst,hsnd,hp.map_eq] using h

private theorem endpoint_pole_bound {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + tanh s * linkGeodesic k⁻¹ j⁻¹)^2) := by
  obtain ⟨T,hT,hp,hmove⟩ := pole_transport_map hs k j
  have htan : 0 ≤ tanh s := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hs) (cosh_pos _).le
  apply endpoint_transport_bound hr hs k j (C := tanh s * linkGeodesic k⁻¹ j⁻¹) (mul_nonneg htan (arccos_nonneg _)) T hT hp
  have hc := continuous_move T hT
  let C := tanh s * linkGeodesic k⁻¹ j⁻¹
  calc _ ≤ ∫ _u, C^2 ∂poleLaw s k := integral_mono
         ((hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
         (integrable_const _) (fun u => pow_le_pow_left₀ (arccos_nonneg _) (hmove u) 2)
       _ = _ := by simp [C]

private theorem endpoint_mean_square_bound {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + (s/2) * linkGeodesic k⁻¹ j⁻¹)^2) := by
  obtain ⟨T,hT,hp,hmove⟩ := mean_square_pole_transport hs k j
  exact endpoint_transport_bound hr hs k j (mul_nonneg (by positivity) (arccos_nonneg _)) T hT hp hmove

/-- Full-link squared Wasserstein bound for any two nonnegative field strengths.
The pole-rotation term is suppressed by the smaller strength and vanishes at zero. -/
theorem strength_weighted_pole_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + tanh (min r s) * linkGeodesic k⁻¹ j⁻¹)^2) := by
  rcases le_total s r with h | h
  · simpa only [min_eq_right h] using endpoint_pole_bound hr hs k j
  · rw [linkWassersteinSq_symm, min_eq_left h,abs_sub_comm,geodesic_comm k⁻¹ j⁻¹]
    exact endpoint_pole_bound hs hr j k

/-- For arbitrary poles, rotate at the smaller strength using the mean-square
circle speed and couple the radial increment at a common pole. -/
theorem mean_square_pole_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + min r s/2 * linkGeodesic k⁻¹ j⁻¹)^2) := by
  rcases le_total s r with h | h
  · simpa only [min_eq_right h] using endpoint_mean_square_bound hr hs k j
  · rw [linkWassersteinSq_symm,min_eq_left h,abs_sub_comm,geodesic_comm k⁻¹ j⁻¹]
    exact endpoint_mean_square_bound hs hr j k

#print axioms mean_square_pole_transport
#print axioms mean_square_pole_wasserstein

/-- The strength-weighted direction bound on actual periodic heat baths, including
zero staples and arbitrary changes of background. -/
theorem heatBath_strength_weighted_pole {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    let r := fieldStrength β U e
    let s := fieldStrength β V e
    ∃ k j : G, heatBath β U e = poleLaw r k ∧ heatBath β V e = poleLaw s j ∧
      linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤
        ENNReal.ofReal ((|s-r|/sqrt 12 + tanh (min r s) * linkGeodesic k⁻¹ j⁻¹)^2) := by
  obtain ⟨k,hk⟩ := heatBath_eq_tilt hl β U e
  obtain ⟨j,hj⟩ := heatBath_eq_tilt hl β V e
  refine ⟨k,j,hk,hj,?_⟩
  rw [hk,hj]
  exact strength_weighted_pole_wasserstein (fieldStrength_mem hβ U e).1 (fieldStrength_mem hβ V e).1 k j

#print axioms pole_transport_map
#print axioms linkWassersteinSq_symm
#print axioms strength_weighted_pole_wasserstein
#print axioms heatBath_strength_weighted_pole
end
end YangMills.PeriodicWilson
