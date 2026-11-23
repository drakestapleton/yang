-- SPDX-License-Identifier: Apache-2.0
import WilsonPlaquetteClustering
import Mathlib.Analysis.Fourier.AddCircle

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real Filter Set
open scoped Topology ComplexConjugate
noncomputable section
private abbrev G := gaugeGroup.image
private abbrev Config (l : ℕ+) := Configuration gaugeGroup l
private abbrev law (l : ℕ+) (β : ℝ) := wilsonLaw gaugeGroup l β su2Haar

private def hol {l : ℕ+} (p : Face l) (U : Config l) := plaquette U p.1 p.2.val.1 p.2.val.2
private def x (u : G) := (suMat u 0 0).re

private theorem plaquette_scalar {l : ℕ+} (p : Face l) (U : Config l) :
    wilsonPlaquetteTrace p U = x (hol p U) := by
  rw [wilsonPlaquetteTrace,scalar_trace]
  change 2*x (hol p U)/2 = _
  ring

/-- Half the real fundamental trace of the same oriented plaquette traversed n times. -/
def windingTrace {l : ℕ+} (p : Face l) (n : ℕ) (U : Config l) :=
  (suMat ((hol p U)^n)).trace.re / 2

theorem windingTrace_gauge_invariant {l : ℕ+} (p : Face l) (n : ℕ) (Ω : Site l → G) (U : Config l) :
    windingTrace p n (gaugeAct Ω U) = windingTrace p n U := by
  have hpow (a b : G) : (a*b*a⁻¹)^n = a*b^n*a⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,ih,pow_succ]; group
  simp only [windingTrace,hol,plaquette_gauge_covariant,hpow,scalar_trace,scalar_conjugate]

private theorem x_cube (u : G) : x (u^3) = 4*(x u)^3-3*x u := by
  let t := polarAngle u
  obtain ⟨h,hh⟩ := link_conjugate_diagonal u
  have he : u^3 = h * diagonalLink (3*t) * h⁻¹ := by
    rw [show 3*t = (t+t)+t by ring,diagonalLink_add,diagonalLink_add]
    conv_lhs => rw [hh]
    change (h*diagonalLink t*h⁻¹)^3 = _
    simp only [pow_succ,pow_zero,one_mul]; group
  rw [he,x,scalar_conjugate]
  change cos (3*t) = 4*(x u)^3-3*x u
  rw [cos_three_mul]; rw [show cos t = x u from cos_polarAngle u]

private theorem triple (u : G) : (suMat (u^3)).trace.re/2 = 4*(x u)^3-3*x u := by
  rw [scalar_trace]; change 2*x (u^3)/2 = _; rw [x_cube]; ring

private theorem continuous_hol {l : ℕ+} (p : Face l) : Continuous (hol p) := by
  unfold hol plaquette; fun_prop

private theorem haar_update (l : ℕ+) (U : Config l) (e : Edge l) : heatBath 0 U e = su2Haar := by
  simp [heatBath]

private def tail {l : ℕ+} (p : Face l) (U : Config l) :=
  U (corners p).2.1 * ((U (corners p).2.2.1)⁻¹ * (U (corners p).2.2.2)⁻¹)

private theorem hol_update_first {l : ℕ+} (hl : 1 < l.val) (p : Face l) (U : Config l) (u : G) :
    hol p (Function.update U (corners p).1 u) = u * tail p U := by
  obtain ⟨ab,ac,ad,_,_,_⟩ := corners_distinct hl p
  change Function.update U (corners p).1 u (corners p).1 * _ = _
  unfold tail
  change Function.update U _ u _ * (Function.update U _ u (corners p).2.1 *
    ((Function.update U _ u (corners p).2.2.1)⁻¹ * (Function.update U _ u (corners p).2.2.2)⁻¹)) = _
  change (corners p).1 ≠ (corners p).2.1 at ab
  change (corners p).1 ≠ (corners p).2.2.1 at ac
  change (corners p).1 ≠ (corners p).2.2.2 at ad
  rw [Function.update_self,Function.update_of_ne (Ne.symm ab),Function.update_of_ne (Ne.symm ac),Function.update_of_ne (Ne.symm ad)]

/-- Every individual plaquette has the Haar law at zero Wilson coupling.
The first link can be resampled independently of its other three corners. -/
theorem wilson_plaquette_haar_integral {l : ℕ+} (hl : 1 < l.val) (p : Face l) (f : G → ℝ) (hf : Continuous f) :
    (∫ U, f (plaquette U p.1 p.2.val.1 p.2.val.2) ∂law l 0) = ∫ u, f u ∂su2Haar := by
  let F := fun U : Config l => f (hol p U)
  haveI := wilson_probability l 0
  have step (U : Config l) : heatBathUpdate 0 (corners p).1 F U = ∫ u, f u ∂su2Haar := by
    simp only [heatBathUpdate,F,haar_update,hol_update_first hl]
    have hp := preserve_right (tail p U)
    exact (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm.trans
      (congrArg (fun μ => ∫ u, f u ∂μ) hp.map_eq)
  have stat := heatBathUpdate_stationary 0 (corners p).1 (hf.comp (continuous_hol p))
  change (∫ U, heatBathUpdate 0 (corners p).1 F U ∂law l 0) = _ at stat
  simpa only [step,integral_const,probReal_univ,one_smul,Function.comp_apply,hol] using stat.symm

private def cubeTrace (u : G) := 4*(x u)^3-3*x u
private theorem continuous_cube : Continuous cubeTrace := by
  exact (continuous_const.mul (continuous_scalar_link.pow 3)).sub (continuous_const.mul continuous_scalar_link)

private theorem zero_moments {l : ℕ+} (hl : 1 < l.val) (p : Face l) :
    (∫ U, wilsonPlaquetteTrace p U ∂law l 0) = 0 ∧
    (∫ U, windingTrace p 3 U ∂law l 0) = 0 ∧
    (∫ U, wilsonPlaquetteTrace p U * windingTrace p 3 U ∂law l 0) = -(1/4:ℝ) := by
  have h3 (U : Config l) : windingTrace p 3 U = cubeTrace (hol p U) := triple _
  have hp (u : G) : x u * cubeTrace u = 4*(x u)^4-3*(x u)^2 := by unfold cubeTrace; ring
  have hi (n : ℕ) (c : ℝ) : Integrable (fun u => c * (x u)^n) su2Haar :=
    (continuous_const.mul (continuous_scalar_link.pow n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨m1,m2,m3,m4⟩ := haar_trace_moments
  change (∫ u, x u ∂su2Haar) = 0 at m1
  change (∫ u, x u^2 ∂su2Haar) = _ at m2
  change (∫ u, x u^3 ∂su2Haar) = _ at m3
  change (∫ u, x u^4 ∂su2Haar) = _ at m4
  simp_rw [plaquette_scalar,h3]
  refine ⟨(wilson_plaquette_haar_integral hl p x continuous_scalar_link).trans m1,?_,?_⟩
  · rw [show (∫ U, cubeTrace (hol p U) ∂law l 0) = _ from wilson_plaquette_haar_integral hl p cubeTrace continuous_cube]
    unfold cubeTrace
    rw [integral_sub (hi 3 4) (by simpa using hi 1 3),integral_const_mul,integral_const_mul,m1,m3]; ring
  · have h := wilson_plaquette_haar_integral hl p (fun u => x u * cubeTrace u) (continuous_scalar_link.mul continuous_cube)
    change (∫ U, x (hol p U)*cubeTrace (hol p U) ∂law l 0) = _ at h
    rw [h]; simp_rw [hp]
    rw [integral_sub (hi 4 4) (hi 2 3),integral_const_mul,integral_const_mul,m2,m4]; norm_num

theorem wilson_winding_covariance_zero {l : ℕ+} (hl : 1 < l.val) (p : Face l) :
    wilsonCovariance 0 (wilsonPlaquetteTrace p) (windingTrace p 3) = -(1/4:ℝ) := by
  obtain ⟨h,_,hh⟩ := zero_moments hl p
  simp only [wilsonCovariance,h,hh,zero_mul,sub_zero]

/-- The U(1) control uses real parts of the first and third characters of the
circle with probability Haar measure. Their connected correlation vanishes. -/
theorem u1_winding_covariance {T : ℝ} [Fact (0 < T)] :
    (∫ u : AddCircle T, (fourier 1 u).re*(fourier 3 u).re ∂AddCircle.haarAddCircle) -
      (∫ u : AddCircle T, (fourier 1 u).re ∂AddCircle.haarAddCircle) *
      (∫ u : AddCircle T, (fourier 3 u).re ∂AddCircle.haarAddCircle) = 0 := by
  let μ : Measure (AddCircle T) := AddCircle.haarAddCircle
  have hi (n : ℤ) : Integrable (fun u : AddCircle T => (fourier n u : ℂ).re) μ :=
    (Complex.continuous_re.comp (fourier n).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have mean (n : ℤ) (hn : n ≠ 0) : (∫ u : AddCircle T, (fourier n u).re ∂μ) = 0 := by
    have hc := congrFun (fourierCoeff_fourier (T := T) n) 0
    have he : (∫ u : AddCircle T, fourier n u ∂μ) = 0 := by
      simpa only [fourierCoeff,neg_zero,fourier_zero,one_smul,Pi.single_eq_of_ne (Ne.symm hn)] using hc
    have hreal := integral_re (𝕜 := ℂ) ((fourier n).continuous.integrable_of_hasCompactSupport
      (μ := μ) (HasCompactSupport.of_compactSpace _))
    change (∫ u : AddCircle T, (fourier n u).re ∂μ) = (∫ u : AddCircle T, fourier n u ∂μ).re at hreal
    rw [hreal,he]; rfl
  have hprod (u : AddCircle T) : (fourier 1 u).re*(fourier 3 u).re =
      ((fourier 4 u).re+(fourier (-2) u).re)/2 := by
    rw [show (4:ℤ)=1+3 by decide,show (-2:ℤ)=1+(-3) by decide,fourier_add,fourier_add,fourier_neg]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]; ring
  change _ - (∫ u : AddCircle T, (fourier 1 u).re ∂μ) * _ = 0
  simp_rw [hprod]
  rw [integral_div,integral_add (hi 4) (hi (-2)),mean 4 (by decide),mean (-2) (by decide),mean 1 (by decide)]
  ring

private def onFace {l : ℕ+} (p : Face l) (e : Edge l) : Prop :=
  e = (corners p).1 ∨ e = (corners p).2.1 ∨ e = (corners p).2.2.1 ∨ e = (corners p).2.2.2

/-- The two outgoing edges based at the corner of a face determine that face
among faces containing both links, even on the side-two torus. -/
private theorem same_face_of_base_edges {l : ℕ+} (hl : 1 < l.val) {p q : Face l}
    (h1 : onFace p (corners q).1) (h4 : onFace p (corners q).2.2.2) : q = p := by
  haveI : Fact (1 < l.val) := ⟨hl⟩
  let i := p.2.val.1
  let j := p.2.val.2
  let sh := fun t : Axis => (Pi.single t (1 : ZMod l.val) : Site l)
  have hij : i < j := p.2.prop
  have hdiff : p.1 + sh i ≠ p.1 + sh j := by
    intro h
    have he := congrFun (add_left_cancel h) i
    simp [sh,hij.ne] at he
  have classify (a : Axis) (h : onFace p (q.1,a)) :
      (a = i ∧ (q.1 = p.1 ∨ q.1 = p.1+sh j)) ∨ (a = j ∧ (q.1 = p.1 ∨ q.1 = p.1+sh i)) := by
    change (q.1,a) = (p.1,i) ∨ (q.1,a) = (p.1+sh i,j) ∨ (q.1,a) = (p.1+sh j,i) ∨ (q.1,a) = (p.1,j) at h
    simp only [Prod.mk.injEq] at h
    tauto
  have ha := classify q.2.val.1 h1
  have hb := classify q.2.val.2 h4
  have hord := q.2.prop
  have hdir : q.2.val.1 = i ∧ q.2.val.2 = j := by
    rcases ha with ⟨he,_⟩ | ⟨he,_⟩ <;> rcases hb with ⟨hf,_⟩ | ⟨hf,_⟩ <;>
      rw [he,hf] at hord <;> first | exact ⟨he,hf⟩ | exact False.elim (lt_irrefl _ hord) | exact False.elim (hij.not_gt hord)
  have hbase : q.1 = p.1 := by
    rcases ha with ⟨_,h⟩ | ⟨h,_⟩
    · rcases hb with ⟨h',_⟩ | ⟨_,h'⟩
      · exact False.elim (hij.ne (h'.symm.trans hdir.2))
      rcases h with h | h <;> rcases h' with h' | h' <;> first | exact h | exact h' | exact False.elim (hdiff (h'.symm.trans h))
    exact False.elim (hij.ne (hdir.1.symm.trans h))
  exact Prod.ext hbase (Subtype.ext (Prod.ext hdir.1 hdir.2))

private theorem hol_update_outside {l : ℕ+} {p : Face l} {e : Edge l} (hout : ¬ onFace p e)
    (U : Config l) (u : G) : hol p (Function.update U e u) = hol p U := by
  change Function.update U e u (corners p).1 * (Function.update U e u (corners p).2.1 *
    ((Function.update U e u (corners p).2.2.1)⁻¹ * (Function.update U e u (corners p).2.2.2)⁻¹)) = _
  rw [Function.update_of_ne (Ne.symm fun h => hout (Or.inl h)),
    Function.update_of_ne (Ne.symm fun h => hout (.inr (.inl h))),
    Function.update_of_ne (Ne.symm fun h => hout (.inr (.inr (.inl h)))),
    Function.update_of_ne (Ne.symm fun h => hout (.inr (.inr (.inr h))))]
  rfl

private theorem continuous_once {l : ℕ+} (p : Face l) : Continuous (wilsonPlaquetteTrace p) := by
  have eq := funext (plaquette_scalar p)
  rw [eq]; exact continuous_scalar_link.comp (continuous_hol p)

/-- Distinct faces have a private outgoing link which kills the cross term
under independent Haar resampling at beta zero. -/
private theorem different_faces {l : ℕ+} (hl : 1 < l.val) {p q : Face l} (hpq : q ≠ p)
    (f : G → ℝ) (hf : Continuous f) :
    (∫ U, f (hol p U) * wilsonPlaquetteTrace q U ∂law l 0) = 0 := by
  have hex : ∃ e, ¬ onFace p e ∧ (e = (corners q).1 ∨ e = (corners q).2.2.2) := by
    by_cases h : onFace p (corners q).1
    · exact ⟨_,fun h' => hpq (same_face_of_base_edges hl h h'),.inr rfl⟩
    exact ⟨_,h,.inl rfl⟩
  obtain ⟨e,hout,he⟩ := hex
  let F := fun U : Config l => f (hol p U) * wilsonPlaquetteTrace q U
  have hx (b : G) : (∫ u, x (u*b) ∂su2Haar) = 0 := by
    have h := preserve_right b
    rw [←integral_map (f := x) h.measurable.aemeasurable continuous_scalar_link.aestronglyMeasurable,h.map_eq]
    exact haar_trace_moments.1
  have step (U : Config l) : heatBathUpdate 0 e F U = 0 := by
    simp only [heatBathUpdate,F,haar_update,hol_update_outside hout,plaquette_scalar,integral_const_mul]
    suffices hz : (∫ u, x (hol q (Function.update U e u)) ∂su2Haar) = 0 by rw [hz,mul_zero]
    rcases he with rfl | rfl
    · simp_rw [hol_update_first hl]; exact hx _
    let b := U (corners q).1 * U (corners q).2.1 * (U (corners q).2.2.1)⁻¹
    have hh (u : G) : x (hol q (Function.update U (corners q).2.2.2 u)) = x (u*b⁻¹) := by
      obtain ⟨_,_,ad,_,bd,cd⟩ := corners_distinct hl q
      have hm : hol q (Function.update U (corners q).2.2.2 u) = b*u⁻¹ := by
        change Function.update U _ u (corners q).1 * (Function.update U _ u (corners q).2.1 *
          ((Function.update U _ u (corners q).2.2.1)⁻¹ * (Function.update U _ u (corners q).2.2.2)⁻¹)) = _
        change (corners q).1 ≠ (corners q).2.2.2 at ad
        change (corners q).2.1 ≠ (corners q).2.2.2 at bd
        change (corners q).2.2.1 ≠ (corners q).2.2.2 at cd
        rw [Function.update_of_ne ad,Function.update_of_ne bd,Function.update_of_ne cd,Function.update_self]
        dsimp [b]; group
      rw [hm,x,x,relative_scalar,relative_scalar,real_inner_comm]
    simp_rw [hh]; exact hx _
  have stat := heatBathUpdate_stationary 0 e ((hf.comp (continuous_hol p)).mul (continuous_once q))
  change (∫ U, heatBathUpdate 0 e F U ∂law l 0) = ∫ U, F U ∂law l 0 at stat
  simpa only [step,integral_zero] using stat.symm

private def action {l : ℕ+} (U : Config l) : ℝ := -wilsonEnergy U
private theorem action_sum {l : ℕ+} (U : Config l) :
    action U = ∑ q : Face l, (wilsonPlaquetteTrace q U - 1) := by
  unfold action wilsonEnergy
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  change -(1-wilsonPlaquetteTrace q U) = _
  ring

private theorem weighted_derivative {l : ℕ+} (μ : Measure (Config l)) [IsProbabilityMeasure μ]
    {f : Config l → ℝ} (hf : Continuous f) :
    HasDerivAt (fun t : ℝ => ∫ U, exp (t*action U)*f U ∂μ)
      (∫ U, action U*f U ∂μ) 0 := by
  have cA : Continuous (action (l := l)) := by
    simp_rw [show (action (l := l)) = fun U => ∑ q : Face l, (wilsonPlaquetteTrace q U-1) from funext action_sum]
    exact continuous_finsetSum _ fun q _ => (continuous_once q).sub continuous_const
  let D := fun (t : ℝ) (U : Config l) => exp (t*action U)*action U*f U
  let B := fun U : Config l => exp |action U| * |action U| * |f U|
  have hi {g : Config l → ℝ} (hg : Continuous g) : Integrable g μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have cont (t : ℝ) : Continuous (fun U : Config l => exp (t*action U)*f U) :=
    (continuous_exp.comp (continuous_const.mul cA)).mul hf
  have diff (t : ℝ) (U : Config l) :
      HasDerivAt (fun s : ℝ => exp (s*action U)*f U) (D t U) t := by
    simpa [D] using (((hasDerivAt_id t).mul_const (action U)).exp.mul_const (f U))
  have bound (U : Config l) (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) : ‖D t U‖ ≤ B U := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mpr ⟨ht.1.le,ht.2.le⟩ : |t| ≤ 1) (abs_nonneg (action U))
    rw [one_mul,←abs_mul] at h
    have he := exp_le_exp.mpr ((le_abs_self _).trans h)
    simp only [D,B,Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (abs_nonneg _)) (abs_nonneg _)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun t U => exp (t*action U)*f U)
    (F' := D) (bound := B) (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))
    (.of_forall fun t => (cont t).aestronglyMeasurable) (hi (cont 0))
    (show AEStronglyMeasurable (D 0) μ from (((continuous_exp.comp (continuous_const.mul cA)).mul cA).mul hf).aestronglyMeasurable)
    (.of_forall bound) (hi (((continuous_exp.comp cA.abs).mul cA.abs).mul hf.abs))
    (.of_forall fun U t _ => diff t U)
  simpa [D] using hd.2

private theorem centered_response {l : ℕ+} (hl : 1 < l.val) (p : Face l)
    (f : G → ℝ) (hf : Continuous f) (hmf : ∫ u, f u ∂su2Haar = 0) :
    HasDerivAt (fun β : ℝ => ∫ U, f (hol p U) ∂law l β) (∫ u, x u*f u ∂su2Haar) 0 := by
  let μ := Measure.pi (fun _ : Edge l => su2Haar)
  let F := fun U : Config l => f (hol p U)
  have cF : Continuous F := hf.comp (continuous_hol p)
  have htilt (t : ℝ) : law l t = μ.tilted (fun U => t * action U) := by
    change μ.tilted (fun U => -t * wilsonEnergy U) = _
    congr 1; funext U; dsimp [action]; ring
  have hzero : law l 0 = μ := by rw [htilt]; simp
  have hm : (∫ U, F U ∂μ) = 0 := hzero ▸ (wilson_plaquette_haar_integral hl p f hf).trans hmf
  have hcross := wilson_plaquette_haar_integral hl p (fun u => x u*f u) (continuous_scalar_link.mul hf)
  rw [hzero] at hcross
  have pair (q : Face l) :
      (∫ U, wilsonPlaquetteTrace q U * F U ∂μ) = if q=p then (∫ u, x u*f u ∂su2Haar) else 0 := by
    by_cases h : q=p
    · subst q; rw [if_pos rfl]
      simp_rw [plaquette_scalar]; exact hcross
    rw [if_neg h,←hzero]
    simpa only [F,mul_comm] using different_faces hl h f hf
  have hi {f : Config l → ℝ} (cf : Continuous f) : Integrable f μ :=
    cf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have cs (q : Face l) : Continuous (fun U => (wilsonPlaquetteTrace q U-1)*F U) :=
    ((continuous_once q).sub continuous_const).mul cF
  have hder : (∫ U, action U * F U ∂μ) = (∫ u, x u*f u ∂su2Haar) := by
    simp_rw [action_sum,Finset.sum_mul]
    rw [integral_finsetSum _ fun q _ => hi (cs q)]
    have ev (q : Face l) : (∫ U, (wilsonPlaquetteTrace q U-1)*F U ∂μ) = if q=p then (∫ u, x u*f u ∂su2Haar) else 0 := by
      simp_rw [sub_mul,one_mul]
      rw [integral_sub (f := fun U => wilsonPlaquetteTrace q U*F U) (g := F)
        (hi ((continuous_once q).mul cF)) (hi cF),pair,hm,sub_zero]
    simp only [ev,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  let num := fun t : ℝ => ∫ U, exp (t*action U)*F U ∂μ
  let den := fun t : ℝ => ∫ U, exp (t*action U) ∂μ
  have hn : HasDerivAt num (∫ u, x u*f u ∂su2Haar) 0 := hder ▸ weighted_derivative μ cF
  have hd : HasDerivAt den (∫ U, action U ∂μ) 0 := by
    simpa only [mul_one,den] using weighted_derivative μ (f := fun _ => (1:ℝ)) continuous_const
  have n0 : num 0 = 0 := by simpa [num,F] using hm
  have d0 : den 0 = 1 := by simp [den]
  have he (t : ℝ) : (∫ U, F U ∂law l t) = num t /den t := by
    rw [htilt,integral_tilted]
    simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div,num,den]
  change HasDerivAt (fun t => ∫ U, F U ∂law l t) _ 0
  simp_rw [he]
  change HasDerivAt (num / den) _ 0
  simpa only [n0,d0,mul_one,zero_mul,sub_zero,one_pow,div_one] using hn.div hd (by rw [d0]; norm_num)

/-- At beta zero the linear response of any continuous one-plaquette observable
to the full Wilson action is its Haar pairing with the fundamental trace. -/
theorem wilson_plaquette_response_zero {l : ℕ+} (hl : 1 < l.val) (p : Face l)
    (f : G → ℝ) (hf : Continuous f) :
    HasDerivAt (fun β : ℝ => ∫ U, f (plaquette U p.1 p.2.val.1 p.2.val.2) ∂law l β)
      (∫ u, (suMat u 0 0).re * f u ∂su2Haar) 0 := by
  let m := ∫ u, f u ∂su2Haar
  let g := fun u => f u - m
  have hi := hf.integrable_of_hasCompactSupport (μ := su2Haar) (HasCompactSupport.of_compactSpace _)
  have hg : ∫ u, g u ∂su2Haar = 0 := by simp [g,m,integral_sub hi (integrable_const _)]
  have hd := (centered_response hl p g (hf.sub continuous_const) hg).add_const m
  have expect (β : ℝ) : (∫ U, g (hol p U) ∂law l β) + m = ∫ U, f (hol p U) ∂law l β := by
    haveI := wilson_probability l β
    have c := hf.comp (continuous_hol p)
    have hi' : Integrable (fun U => f (hol p U)) (law l β) :=
      c.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp [g,integral_sub hi' (integrable_const _)]
  have score : (∫ u, x u*g u ∂su2Haar) = ∫ u, x u*f u ∂su2Haar := by
    have hf' : Integrable (fun u => x u*f u) su2Haar :=
      (continuous_scalar_link.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hx' : Integrable x su2Haar := continuous_scalar_link.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hz : (∫ u, x u ∂su2Haar) = 0 := haar_trace_moments.1
    simp only [g,mul_sub,integral_sub hf' (hx'.mul_const m),integral_mul_const,hz,zero_mul,sub_zero]
  change HasDerivAt (fun β => (∫ U, g (hol p U) ∂law l β) + m) (∫ u, x u*g u ∂su2Haar) 0 at hd
  simp_rw [expect,score] at hd
  exact hd

/-- An increasing function of the primitive normalized trace does pass the
first-order test at zero coupling. -/
theorem wilson_increasing_trace_response_nonneg {l : ℕ+} (hl : 1 < l.val) (p : Face l)
    (f : ℝ → ℝ) (cf : Continuous f) (hm : MonotoneOn f (Icc (-1) 1)) :
    0 ≤ deriv (fun β : ℝ => ∫ U, f (wilsonPlaquetteTrace p U) ∂law l β) 0 := by
  let g := fun u : G => f (x u)
  have cg : Continuous g := cf.comp continuous_scalar_link
  let h := fun u : G => x u * (g u-f 0)
  have nonneg (u : G) : 0 ≤ h u := by
    have hx : x u ∈ Icc (-1:ℝ) 1 := by
      rw [show x u = cos (polarAngle u) from (cos_polarAngle u).symm]
      exact ⟨neg_one_le_cos _,cos_le_one _⟩
    have hz : (0:ℝ) ∈ Icc (-1:ℝ) 1 := by constructor <;> norm_num
    rcases le_total 0 (x u) with hs | hs
    · exact mul_nonneg hs (sub_nonneg.mpr (hm hz hx hs))
    exact mul_nonneg_of_nonpos_of_nonpos hs (sub_nonpos.mpr (hm hx hz hs))
  have hg : Integrable (fun u => x u*g u) su2Haar :=
    (continuous_scalar_link.mul cg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hx : Integrable x su2Haar := continuous_scalar_link.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (∫ u, x u ∂su2Haar) = 0 := haar_trace_moments.1
  have hid : (∫ u, h u ∂su2Haar) = ∫ u, x u*g u ∂su2Haar := by
    simp only [h,mul_sub,integral_sub hg (hx.mul_const (f 0)),integral_mul_const,hz,zero_mul,sub_zero]
  have hd := (wilson_plaquette_response_zero hl p g cg).deriv
  simp_rw [plaquette_scalar]
  change 0 ≤ deriv (fun β : ℝ => ∫ U, g (hol p U) ∂law l β) 0
  exact (integral_nonneg nonneg (μ := su2Haar)).trans_eq (hid.trans hd.symm)

/-- The primitive and triply wound loops respond with opposite signs to the
same bare Wilson coupling on the same four-torus. -/
theorem wilson_primitive_derivative_zero {l : ℕ+} (hl : 1 < l.val) (p : Face l) :
    HasDerivAt (fun β : ℝ => ∫ U, wilsonPlaquetteTrace p U ∂law l β) (1/4:ℝ) 0 := by
  have hd := wilson_plaquette_response_zero hl p x continuous_scalar_link
  simp_rw [plaquette_scalar]
  have hpair : (∫ u, x u*x u ∂su2Haar) = 1/4 := by simpa only [sq,x] using haar_trace_moments.2.1
  change HasDerivAt _ (∫ u, x u*x u ∂su2Haar) _ at hd
  rwa [hpair] at hd

theorem wilson_winding_derivative_zero {l : ℕ+} (hl : 1 < l.val) (p : Face l) :
    HasDerivAt (fun β : ℝ => ∫ U, windingTrace p 3 U ∂law l β) (-(1/4:ℝ)) 0 := by
  have hd := wilson_plaquette_response_zero hl p cubeTrace continuous_cube
  have hpair := wilson_plaquette_haar_integral hl p (fun u => x u*cubeTrace u) (continuous_scalar_link.mul continuous_cube)
  have h3 (U : Config l) : windingTrace p 3 U = cubeTrace (hol p U) := triple _
  have hcross := (zero_moments hl p).2.2
  simp_rw [plaquette_scalar,h3] at hcross
  have he : (∫ u, x u*cubeTrace u ∂su2Haar) = -(1/4:ℝ) := hpair.symm.trans hcross
  change HasDerivAt _ (∫ u, x u*cubeTrace u ∂su2Haar) _ at hd
  simp_rw [h3]; rwa [he] at hd

/-- The failure already occurs on every nontrivial interval starting at zero. -/
theorem wilson_winding_not_monotone {l : ℕ+} (hl : 1 < l.val) (p : Face l) {b : ℝ} (hb : 0 < b) :
    ¬ MonotoneOn (fun β : ℝ => ∫ U, windingTrace p 3 U ∂law l β) (Icc 0 b) := by
  intro hm
  have hd := (wilson_winding_derivative_zero hl p).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hb 0 ⟨le_rfl,hb.le⟩)
  have hh := hm.derivWithin_nonneg (x := 0)
  rw [hd] at hh
  norm_num at hh

#print axioms haar_trace_moments
#print axioms windingTrace_gauge_invariant
#print axioms wilson_plaquette_haar_integral
#print axioms u1_winding_covariance
#print axioms wilson_winding_covariance_zero
#print axioms wilson_plaquette_response_zero
#print axioms wilson_increasing_trace_response_nonneg
#print axioms wilson_primitive_derivative_zero
#print axioms wilson_winding_derivative_zero
#print axioms wilson_winding_not_monotone
end
end YangMills.PeriodicWilson
