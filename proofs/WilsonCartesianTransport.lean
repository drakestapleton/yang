-- SPDX-License-Identifier: Apache-2.0
import WilsonCouplingTriangle
import WilsonFieldResponse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real Set Filter InnerProductGeometry
open scoped ENNReal Topology ComplexConjugate Matrix.Norms.Frobenius
noncomputable section
private abbrev G := gaugeGroup.image
private abbrev V := EuclideanSpace ℝ (Fin 4)

private theorem pole_representation (x : V) : ∃ k : G, x = ‖x‖ • linkCoordinates k := by
  let a : ℂ := ⟨x 0,x 1⟩
  let b : ℂ := ⟨x 2,x 3⟩
  let A : M := !![a,b; -conj b,conj a]
  have ha : A ∈ quaternionAlgebra := ⟨rfl,rfl⟩
  obtain ⟨k,hk⟩ := polar ha
  have rep : x = length A • linkCoordinates k := calc
    x = matrixCoordinates A := by ext i; fin_cases i <;> rfl
    _ = matrixCoordinates (length A • suMat k) := congrArg matrixCoordinates hk
    _ = length A • linkCoordinates k := by ext i; fin_cases i <;> simp [linkCoordinates,matrixCoordinates]
  have hn : ‖x‖ = length A := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ length A from sqrt_nonneg _),coordinates_norm,mul_one]
      using congrArg norm rep
  exact ⟨k,hn ▸ rep⟩

private def pole (x : V) := (pole_representation x).choose
private theorem rep (x : V) : x = ‖x‖ • linkCoordinates (pole x) := (pole_representation x).choose_spec
private def fieldLaw (x : V) := poleLaw ‖x‖ (pole x)
private instance (x : V) : IsProbabilityMeasure (fieldLaw x) := poleLaw_probability ..

private theorem coords_inj : Function.Injective linkCoordinates := by
  intro u v h
  have entry (i : Fin 4) := congrArg (fun z : V => z i) h
  have a : suMat u 0 0 = suMat v 0 0 := Complex.ext (entry 0) (entry 1)
  have b : suMat u 0 1 = suMat v 0 1 := Complex.ext (entry 2) (entry 3)
  apply Subtype.ext; apply Subtype.ext
  change suMat u = suMat v
  ext i j : 2
  fin_cases i <;> fin_cases j
  · exact a
  · exact b
  · exact u.prop.2.trans ((congrArg (fun z : ℂ => -conj z) b).trans v.prop.2.symm)
  · exact u.prop.1.trans ((congrArg (fun z : ℂ => conj z) a).trans v.prop.1.symm)

private theorem fieldLaw_pole {r : ℝ} (hr : 0 ≤ r) (k : G) :
    fieldLaw (r • linkCoordinates k) = poleLaw r k := by
  have hn : ‖r • linkCoordinates k‖ = r := by simp [norm_smul,abs_of_nonneg hr,coordinates_norm]
  unfold fieldLaw
  rw [hn]
  rcases hr.eq_or_lt with h | h
  · subst r; simp [poleLaw]
  have he := rep (r • linkCoordinates k)
  rw [hn] at he
  have hp : k = pole (r • linkCoordinates k) := coords_inj ((smul_right_injective _ h.ne') he)
  rw [← hp]

private def fieldDistance (x y : V) := sqrt (linkWassersteinSq (fieldLaw x) (fieldLaw y)).toReal

private theorem field_finite (x y : V) : linkWassersteinSq (fieldLaw x) (fieldLaw y) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (cartesian_field_mean_square (norm_nonneg x) (norm_nonneg y) (pole x) (pole y))

private theorem dist_sq (x y : V) : ENNReal.ofReal (fieldDistance x y ^ 2) =
    linkWassersteinSq (fieldLaw x) (fieldLaw y) := by
  rw [fieldDistance,sq_sqrt ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (field_finite x y)]

private theorem field_bound {x y : V} {R : ℝ} (hr : 0 ≤ R) :
    fieldDistance x y ≤ R ↔ linkWassersteinSq (fieldLaw x) (fieldLaw y) ≤ ENNReal.ofReal (R^2) := by
  rw [← dist_sq, ENNReal.ofReal_le_ofReal_iff (sq_nonneg R)]
  exact (sq_le_sq₀ (sqrt_nonneg _) hr).symm

private theorem field_triangle (x y z : V) : fieldDistance x z ≤ fieldDistance x y + fieldDistance y z :=
  (field_bound (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))).2
    (linkWassersteinSq_triangle_bound (sqrt_nonneg _) (sqrt_nonneg _)
      (dist_sq x y).ge (dist_sq y z).ge)

private theorem field_coarse (x y : V) : fieldDistance x y ≤ sqrt (1/12+π^2/16)*‖x-y‖ := by
  apply (field_bound (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).2
  have h := cartesian_field_mean_square (norm_nonneg x) (norm_nonneg y) (pole x) (pole y)
  simpa only [fieldLaw,←rep x,←rep y,mul_pow,sq_sqrt (by positivity : (0:ℝ) ≤ 1/12+π^2/16)] using h

private theorem field_continuous (x : V) : Continuous (fieldDistance x) := by
  apply LipschitzWith.continuous (K := (sqrt (1/12+π^2/16)).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ (sqrt_nonneg _),abs_le]
  constructor
  · have h := (field_triangle x y z).trans (add_le_add_right (field_coarse y z) _)
    linarith only [h]
  · have h := (field_triangle x z y).trans (add_le_add_right (field_coarse z y) _)
    rw [norm_sub_rev z y] at h; linarith only [h]

-- Near a nonzero field the normalized direction is continuous. The angular
-- arc-to-chord ratio therefore tends to one as the second field approaches it.
private theorem local_angular_estimate {c : ℝ} (hc : 1 < c) {x : V} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, linkGeodesic (pole x) (pole y) ≤
      c * (2*sin (linkGeodesic (pole x) (pole y)/2)) := by
  have ha : Tendsto (fun y : V => angle x y) (𝓝 x) (𝓝 0) := by
    simpa only [Function.comp_def,angle_self hx] using
      ((continuousAt_angle (x := (x,x)) hx hx).comp (continuousAt_const.prodMk continuousAt_id)).tendsto
  have ht : Tendsto (fun y : V => sinc (angle x y/2)) (𝓝 x) (𝓝 1) := by
    simpa only [Function.comp_def,zero_div,sinc_zero] using (continuous_sinc.tendsto _).comp (ha.div_const 2)
  have hfrac : 1/c < 1 := (div_lt_one (by linarith)).2 hc
  filter_upwards [ht.eventually (Ioi_mem_nhds hfrac),isOpen_ne.mem_nhds hx] with y hy hy0
  have he : angle x y = linkGeodesic (pole x) (pole y) := by
    conv_lhs => rw [rep x,rep y]
    rw [angle_smul_left_of_pos _ _ (norm_pos_iff.mpr hx),angle_smul_right_of_pos _ _ (norm_pos_iff.mpr hy0),
      linkGeodesic_eq_angle]
  let d := linkGeodesic (pole x) (pole y)
  have hnn : 0 ≤ d := arccos_nonneg _
  change 1/c < sinc (angle x y/2) at hy
  rw [he] at hy
  rcases hnn.eq_or_lt with hd | hd
  · change d ≤ c*(2*sin (d/2)); rw [← hd]; simp
  have hhalf : 0 < d/2 := by positivity
  change 1/c < sinc (d/2) at hy
  rw [sinc_of_ne_zero hhalf.ne',div_lt_div_iff₀ (by linarith : 0 < c) hhalf] at hy
  change d ≤ c*(2*sin (d/2))
  linarith only [hy]

private theorem field_local {c : ℝ} (hc : 1 < c) (x : V) :
    ∀ᶠ y in 𝓝 x, fieldDistance x y ≤ (c/sqrt 3)*‖x-y‖ := by
  have hL : (1/sqrt 12 : ℝ)^2 = 1/12 := by rw [div_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 12)]; norm_num
  have hB : (c/sqrt 3)^2 = c^2/3 := by rw [div_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hc0 : 0 ≤ c := by linarith
  by_cases hx : x = 0
  · subst x
    filter_upwards with y
    apply (field_bound (mul_nonneg (div_nonneg hc0 (sqrt_nonneg _)) (norm_nonneg _))).2
    have h := mean_square_pole_wasserstein (r := 0) le_rfl (norm_nonneg y) (pole 0) (pole y)
    simp only [fieldLaw,norm_zero,sub_zero,min_eq_left (norm_nonneg y),zero_div,zero_mul,add_zero,
      zero_sub,norm_neg,abs_of_nonneg (norm_nonneg y),mul_pow,hB] at h ⊢
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 12)]
    nlinarith only [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ c^2 by nlinarith [sq_nonneg (c-1)]) (sq_nonneg ‖y‖),sq_nonneg ‖y‖]
  filter_upwards [local_angular_estimate hc hx] with y hangle
  let r := ‖x‖
  let s := ‖y‖
  let D := linkGeodesic (pole x) (pole y)
  let m := min r s
  let a := |s-r|
  let b := 2*m*sin (D/2)
  have hr : 0 ≤ r := norm_nonneg _
  have hs : 0 ≤ s := norm_nonneg _
  have hm : 0 ≤ m := le_min hr hs
  have hd : 0 ≤ D := arccos_nonneg _
  have hdπ : D ≤ π := arccos_le_pi _
  have hsin : 0 ≤ sin (D/2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have hb0 : 0 ≤ b := mul_nonneg (by linarith) hsin
  have hmm : m^2 ≤ r*s := by
    rcases le_total r s with h | h
    · simp only [m,min_eq_left h,sq]; exact mul_le_mul_of_nonneg_left h hr
    · simp only [m,min_eq_right h,sq]; exact mul_le_mul_of_nonneg_right h hs
  have hcos : cos D = inner ℝ (linkCoordinates (pole x)) (linkCoordinates (pole y)) :=
    (cos_polarAngle _).trans (relative_scalar _ _)
  have hv : ‖x-y‖^2 = a^2+4*r*s*sin (D/2)^2 := by
    calc _ = ‖r • linkCoordinates (pole x)-s • linkCoordinates (pole y)‖^2 := by
                exact congrArg (fun z : V => ‖z‖^2) (congrArg₂ (·-·) (rep x) (rep y))
         _ = _ := by
                rw [norm_sub_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
                  abs_of_nonneg hr,abs_of_nonneg hs,coordinates_norm,coordinates_norm,
                  real_inner_smul_left,real_inner_smul_right,← hcos]
                have he := cos_two_mul_eq_one_sub (D/2)
                rw [show 2*(D/2)=D by ring] at he
                dsimp only [a]; rw [sq_abs,he]; ring
  have hch : a^2 + b^2 ≤ ‖x-y‖^2 := by
    rw [hv]; dsimp only [b]
    nlinarith only [mul_le_mul_of_nonneg_right hmm (sq_nonneg (sin (D/2)))]
  have hh : m/2*D ≤ c*(b/2) := by
    have he := mul_le_mul_of_nonneg_left hangle hm
    dsimp only [b]; change m*D ≤ m*(c*(2*sin (D/2))) at he; linarith only [he]
  have hstep : a/sqrt 12 + m/2*D ≤ c*(a/sqrt 12+b/2) := by
    have hnon : 0 ≤ a/sqrt 12 := div_nonneg (abs_nonneg _) (sqrt_nonneg _)
    have hrad := mul_le_mul_of_nonneg_right hc.le hnon; linarith only [hh,hrad]
  have hcs : (a/sqrt 12 + b/2)^2 ≤ (a^2+b^2)/3 := by
    let L := 1/sqrt 12
    have he : (L*a+b/2)^2 + (a/2-L*b)^2 = (L^2+1/4)*(a^2+b^2) := by ring
    change L^2 = 1/12 at hL; rw [hL] at he
    rw [show a/sqrt 12 = L*a by dsimp [L]; ring]
    linarith only [he,sq_nonneg (a/2-L*b)]
  apply (field_bound (mul_nonneg (div_nonneg hc0 (sqrt_nonneg _)) (norm_nonneg _))).2
  have hp := mean_square_pole_wasserstein hr hs (pole x) (pole y)
  rw [pole_inverse_distance] at hp
  apply hp.trans (ENNReal.ofReal_le_ofReal ?_)
  change (a/sqrt 12 + m/2*D)^2 ≤ _
  calc _ ≤ (c*(a/sqrt 12+b/2))^2 := pow_le_pow_left₀ (add_nonneg (div_nonneg (abs_nonneg _) (sqrt_nonneg _)) (mul_nonneg (div_nonneg hm (by norm_num)) hd)) hstep 2
       _ ≤ c^2 * (‖x-y‖^2/3) := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hcs.trans (by linarith only [hch])) (sq_nonneg _)
       _ = _ := by rw [mul_pow,hB]; ring

private theorem segment_bound {c : ℝ} (hc : 1 < c) (x y : V) :
    fieldDistance x y ≤ (c/sqrt 3)*‖x-y‖ := by
  let p := fun t : ℝ => x + t • (y-x)
  let B := c/sqrt 3 * ‖y-x‖
  have cp : Continuous p := continuous_const.add (continuous_id.smul continuous_const)
  have chord (t u : ℝ) : ‖p t-p u‖ = |u-t| * ‖y-x‖ := by
    have he : p t-p u = (t-u) • (y-x) := by dsimp [p]; rw [sub_smul]; abel
    rw [he,norm_smul,Real.norm_eq_abs,abs_sub_comm]
  let E := {t : ℝ | fieldDistance x (p t) ≤ B*t}
  have hclosed : IsClosed E := isClosed_le ((field_continuous x).comp cp) (continuous_const.mul continuous_id)
  have start : 0 ∈ E := by
    have hh := field_coarse x x
    simpa [E,p] using hh
  have one : (1:ℝ) ∈ E := by
    apply ((hclosed.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin start ?_) (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    intro t ht
    have hloc := (cp.tendsto t).eventually (field_local hc (p t))
    filter_upwards [nhdsWithin_le_nhds hloc,self_mem_nhdsWithin] with u hu htu
    change fieldDistance x (p u) ≤ B*u
    have hh := field_triangle x (p t) (p u)
    have he : fieldDistance x (p t) ≤ B*t := ht.1
    rw [chord,abs_of_nonneg (sub_nonneg.mpr htu.le)] at hu
    dsimp only [B] at he ⊢
    linarith only [he,hu,hh]
  change fieldDistance x (p 1) ≤ B*1 at one
  simpa [p,B,norm_sub_rev y x] using one

/-- Subdividing the straight Cartesian segment removes the global arc-to-chord
penalty. A segment through the zero field uses its radial bound at that point. -/
theorem straight_field_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤ ENNReal.ofReal
      (‖r • linkCoordinates k-s • linkCoordinates j‖^2/3) := by
  let x := r • linkCoordinates k
  let y := s • linkCoordinates j
  have hc : fieldDistance x y ≤ (1/sqrt 3)*‖x-y‖ := by
    have ht : Tendsto (fun c : ℝ => c/sqrt 3 * ‖x-y‖) (𝓝[>] 1) (𝓝 (1/sqrt 3 * ‖x-y‖)) :=
      ((continuous_id.div_const _).mul continuous_const).continuousWithinAt
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with c h using segment_bound h x y
  have hh := (field_bound (mul_nonneg (by positivity : 0 ≤ 1/sqrt 3) (norm_nonneg _))).1 hc
  simpa only [x,y,fieldLaw_pole hr,fieldLaw_pole hs,mul_pow,div_pow,one_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 3),
    one_div,inv_mul_eq_div] using hh

#print axioms straight_field_wasserstein
end
end YangMills.PeriodicWilson
