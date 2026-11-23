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

@[fun_prop] private theorem retreat_cont {r : ℝ} (hr : 0 ≤ r) (n : G) (c : ℝ≥0) :
    Continuous (retreat hr n c) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hlt := swept_strict r n u hb
    rw [(retreat_spec hr n c u).2] at hlt
    have hc : Continuous (fun v => sweptMass r n v b) := (swept_cont r n).comp (continuous_id.prodMk continuous_const)
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hlt] with v hv
    apply (swept_strict r n v).lt_iff_lt.mp
    rwa [(retreat_spec hr n c v).2]
  · intro b hb
    have hlt := swept_strict r n u hb
    rw [(retreat_spec hr n c u).2] at hlt
    have hc : Continuous (fun v => sweptMass r n v b) := (swept_cont r n).comp (continuous_id.prodMk continuous_const)
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hlt] with v hv
    apply (swept_strict r n v).lt_iff_lt.mp
    rwa [(retreat_spec hr n c v).2]

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

/-- A deterministic coupling of two equal-strength full Wilson tilts. The map
moves every link by at most tanh(r) times the round distance between pole centers. -/
theorem pole_transport_map {r : ℝ} (hr : 0 ≤ r) (k j : G) :
    ∃ T : G → G, Continuous T ∧ MeasurePreserving T (poleLaw r k) (poleLaw r j) ∧
      ∀ u, linkGeodesic u (T u) ≤ tanh r * linkGeodesic k⁻¹ j⁻¹ := by
  let d := polarAngle (j⁻¹*k)
  have hd : 0 ≤ d := arccos_nonneg _
  have hdist : d = linkGeodesic k⁻¹ j⁻¹ := calc
    _ = linkGeodesic j⁻¹ k⁻¹ := by simp [d,linkGeodesic]
    _ = _ := by simp only [linkGeodesic_eq_angle]; exact InnerProductGeometry.angle_comm ..
  obtain ⟨n,hn⟩ := link_conjugate_diagonal (j⁻¹*k)
  change j⁻¹*k = circle n d at hn
  let c := massStep r d hd
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
    _ ≤ _ := by rw [← hdist]; exact retreat_distance hr hd n (u*k)

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

-- Modify one endpoint of a coupling whose root mean square cost is at most R.
private theorem transfer_cost (P : Measure (G × G)) [IsProbabilityMeasure P] (T : G → G)
    (hT : Continuous T) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbase : (∫ z, linkGeodesic z.1 z.2^2 ∂P) ≤ R^2) (hmove : ∀ u, linkGeodesic u (T u) ≤ C) :
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
  have hmean : (∫ z, g z ∂P) ≤ R := by
    have hv := ProbabilityTheory.variance_nonneg g P
    rw [ProbabilityTheory.variance_eq_sub (cg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hv
    change 0 ≤ (∫ z, g z^2 ∂P) - (∫ z, g z ∂P)^2 at hv
    change (∫ z, g z^2 ∂P) ≤ R^2 at hbase
    nlinarith only [hv,hbase,hR,sq_nonneg ((∫ z, g z ∂P)-R)]
  have hpoint (z : G × G) : f z^2 ≤ g z^2 + (2*C)*g z + C^2 := by
    have h : f z ≤ g z+C := (geo_triangle z.1 z.2 (T z.2)).trans (add_le_add_right (hmove z.2) _)
    calc _ ≤ (g z+C)^2 := pow_le_pow_left₀ (arccos_nonneg _ : 0 ≤ f z) h 2
         _ = _ := by ring
  have hg2 : Integrable (fun z => g z^2) P := (cg.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun z => (2*C)*g z) P := (cg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  have hsum : Integrable (fun z => g z^2 + (2*C)*g z) P := hg2.add hl
  have h := integral_mono hi (hsum.add (integrable_const (C^2))) hpoint
  change (∫ z, f z^2 ∂P) ≤ ∫ z, g z^2 + (2*C)*g z + C^2 ∂P at h
  rw [integral_add hsum (integrable_const (C^2)),integral_add hg2 hl,integral_const_mul,integral_const] at h
  simp only [probReal_univ,one_smul] at h
  change (∫ z, g z^2 ∂P) ≤ R^2 at hbase
  linarith only [h,hbase,mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ 2*C)]

private theorem endpoint_pole_bound {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + tanh s * linkGeodesic k⁻¹ j⁻¹)^2) := by
  let P := linkCoupling r s k k
  obtain ⟨hfst,hsnd⟩ := linkCoupling_marginals r s k k
  haveI : IsProbabilityMeasure P := ⟨by
    change linkCoupling r s k k univ = 1
    rw [← Measure.fst_univ,hfst,measure_univ]⟩
  obtain ⟨T,hT,hp,hmove⟩ := pole_transport_map hs k j
  have hR : 0 ≤ |s-r|/sqrt 12 := by positivity
  have htan : 0 ≤ tanh s := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hs) (cosh_pos _).le
  have hbase : (∫ z, linkGeodesic z.1 z.2^2 ∂P) ≤ (|s-r|/sqrt 12)^2 := by
    rw [div_pow,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12),linkCoupling_common_cost]
    exact radialCoupling_cost hr hs
  have hC : 0 ≤ tanh s * linkGeodesic k⁻¹ j⁻¹ := mul_nonneg htan (arccos_nonneg _)
  have h := transfer_cost P T hT hR hC hbase hmove
  simpa only [P,hfst,hsnd,hp.map_eq] using h

/-- Full-link squared Wasserstein bound for any two nonnegative field strengths.
The pole-rotation term is suppressed by the smaller strength and vanishes at zero. -/
theorem strength_weighted_pole_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r|/sqrt 12 + tanh (min r s) * linkGeodesic k⁻¹ j⁻¹)^2) := by
  rcases le_total s r with h | h
  · simpa only [min_eq_right h] using endpoint_pole_bound hr hs k j
  · rw [linkWassersteinSq_symm, min_eq_left h,abs_sub_comm,geodesic_comm k⁻¹ j⁻¹]
    exact endpoint_pole_bound hs hr j k

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
