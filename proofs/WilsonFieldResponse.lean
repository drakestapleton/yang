-- SPDX-License-Identifier: Apache-2.0
import WilsonPoleTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real Set
open scoped Matrix.Norms.Frobenius ENNReal
noncomputable section
private abbrev G := gaugeGroup.image

private theorem tanh_le_strength {x : ℝ} (hx : 0 ≤ x) : tanh x ≤ x := by
  rw [tanh_eq_sinh_div_cosh,div_le_iff₀ (cosh_pos _)]
  have h := intervalIntegral.integral_mono_on (μ := volume) hx (continuous_cosh.intervalIntegrable _ _) intervalIntegrable_const
    (fun t ht => (show cosh t ≤ cosh x from cosh_le_cosh.mpr (by simpa only [abs_of_nonneg ht.1,abs_of_nonneg hx] using ht.2)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_sinh t)
    (continuous_cosh.intervalIntegrable _ _),intervalIntegral.integral_const,sinh_zero,sub_zero,sub_zero,smul_eq_mul] at h
  exact h

private theorem inverse_distance (k j : G) : linkGeodesic k⁻¹ j⁻¹ = linkGeodesic k j := calc
  _ = linkGeodesic (k*k⁻¹*j) (k*j⁻¹*j) := by rw [linkGeodesic_mul_right,linkGeodesic_mul_left]
  _ = linkGeodesic j k := by simp [mul_assoc]
  _ = _ := by simp only [linkGeodesic_eq_angle]; exact InnerProductGeometry.angle_comm ..

/-- A uniform Lipschitz estimate in the Cartesian staple field. Its squared constant
contains the radial contribution 1/12 and the round arc-to-chord factor π²/4. -/
theorem cartesian_field_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤ ENNReal.ofReal
      ((1/12 + π^2/4) * ‖r • linkCoordinates k - s • linkCoordinates j‖^2) := by
  apply (strength_weighted_pole_wasserstein hr hs k j).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [inverse_distance]
  let D := linkGeodesic k j
  let m := min r s
  let a := |s-r|
  let b := 2/π*m*D
  let L := (sqrt 12)⁻¹
  let B := π/2
  have hm : 0 ≤ m := le_min hr hs
  have hD : 0 ≤ D := arccos_nonneg _
  have hpi : π ≠ 0 := pi_pos.ne'
  have hchord := cos_le_one_sub_mul_cos_sq (show |D| ≤ π from by rw [abs_of_nonneg hD]; exact arccos_le_pi _)
  have hchord2 : (2/π*D)^2 ≤ 2*(1-cos D) := by
    have he : (2/π*D)^2 = 2*(2/π^2*D^2) := by field_simp
    rw [he]; linarith only [hchord]
  have hmm : m^2 ≤ r*s := by
    dsimp [m]
    rcases le_total r s with h | h
    · rw [min_eq_left h,sq]; exact mul_le_mul_of_nonneg_left h hr
    · rw [min_eq_right h,sq]; exact mul_le_mul_of_nonneg_right h hs
  have hb : b^2 ≤ 2*r*s*(1-cos D) := calc
    _ = m^2*(2/π*D)^2 := by dsimp [b]; ring
    _ ≤ m^2*(2*(1-cos D)) := mul_le_mul_of_nonneg_left hchord2 (sq_nonneg _)
    _ ≤ (r*s)*(2*(1-cos D)) := mul_le_mul_of_nonneg_right hmm (by linarith [cos_le_one D])
    _ = _ := by ring
  have hc : cos D = inner ℝ (linkCoordinates k) (linkCoordinates j) :=
    (cos_polarAngle (k*j⁻¹)).trans (relative_scalar k j)
  have hv : ‖r • linkCoordinates k - s • linkCoordinates j‖^2 = a^2 + 2*r*s*(1-cos D) := by
    rw [norm_sub_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr,
      abs_of_nonneg hs,coordinates_norm,coordinates_norm,real_inner_smul_left,real_inner_smul_right,← hc]
    dsimp only [a]; rw [sq_abs]; ring
  have hBb : B*b = m*D := by dsimp [B,b]; field_simp
  have hL : L^2 = 1/12 := by simp [L,inv_pow,Real.sq_sqrt]
  have hB : B^2 = π^2/4 := by dsimp [B]; ring
  have htan : 0 ≤ tanh m := by rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hm) (cosh_pos _).le
  have hstep : a/sqrt 12 + tanh m*D ≤ L*a+B*b := by
    rw [hBb,div_eq_inv_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_right (tanh_le_strength hm) hD) _
  have hnn : 0 ≤ a/sqrt 12 + tanh m*D := add_nonneg (div_nonneg (abs_nonneg _) (sqrt_nonneg _)) (mul_nonneg htan hD)
  calc
    _ ≤ (L*a+B*b)^2 := pow_le_pow_left₀ hnn hstep 2
    _ ≤ (L^2+B^2)*(a^2+b^2) := by nlinarith only [sq_nonneg (L*b-B*a)]
    _ ≤ (L^2+B^2)*‖r • linkCoordinates k-s • linkCoordinates j‖^2 := by
      rw [hv]; exact mul_le_mul_of_nonneg_left (add_le_add_right hb _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by rw [hL,hB]

private theorem matrixCoordinates_smul_sub (a b : ℝ) (A B : M) :
    matrixCoordinates (a • A - b • B) = a • matrixCoordinates A - b • matrixCoordinates B := by
  ext i; fin_cases i <;> simp [matrixCoordinates]

private theorem matrixCoordinates_norm {A : M} (ha : A ∈ quaternionAlgebra) :
    ‖matrixCoordinates A‖ = ‖A‖/sqrt 2 := by
  have he : ‖matrixCoordinates A‖^2 = (length A)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,length,Real.sq_sqrt (by positivity)]
    simp [matrixCoordinates,Fin.sum_univ_four,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hlen : ‖matrixCoordinates A‖ = length A := (sq_eq_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp he
  rw [hlen,frobenius_eq ha]; field_simp

/-- The full-link response to all changed neighboring links, counted with their
periodic plaquette multiplicities. The bound covers every background and zero staples. -/
theorem periodic_neighbor_wasserstein {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal
      ((1/12+π^2/4)*(β * ∑ i ∈ incidences e,
        linkChord (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1) / sqrt 2)^2) := by
  let r := fieldStrength β U e
  let s := fieldStrength β V e
  obtain ⟨k,hk,hproj⟩ := su2_field_pole_with_matrix β U e
  obtain ⟨j,hj,hproj'⟩ := su2_field_pole_with_matrix β V e
  rw [heatBath_eq_tilt_of_projection hl β U e k hproj,heatBath_eq_tilt_of_projection hl β V e j hproj']
  change linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤ _
  apply (cartesian_field_wasserstein (fieldStrength_mem hβ U e).1 (fieldStrength_mem hβ V e).1 k j).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  let AU : M := stapleMatrix U e
  let AV : M := stapleMatrix V e
  let A : M := AU-AV
  have hku : β • AU = r • suMat k := hk
  have hjv : β • AV = s • suMat j := hj
  have hsplit : β • A = r • suMat k - s • suMat j :=
    (smul_sub β AU AV).trans (congrArg₂ (· - ·) hku hjv)
  have ha : β • A ∈ quaternionAlgebra := hsplit ▸ quaternionAlgebra.sub_mem
    (quaternionAlgebra.smul_mem k.prop r) (quaternionAlgebra.smul_mem j.prop s)
  have he : r • linkCoordinates k - s • linkCoordinates j = matrixCoordinates (β • A) :=
    (matrixCoordinates_smul_sub r s (suMat k) (suMat j)).symm.trans (congrArg matrixCoordinates hsplit.symm)
  rw [he,matrixCoordinates_norm ha,norm_smul,Real.norm_eq_abs,abs_of_nonneg hβ,
    mul_div_assoc, ← Finset.sum_div]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (staple_perturbation hl U V e) (sqrt_nonneg _)) hβ

/-- Subunit finite-volume one-link response in the uniform neighbor distance. -/
theorem periodic_neighbor_subunit {l : ℕ+} (hl : 1 < l.val) {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ)
    (hwindow : (1/12+π^2/4)*(18*β)^2 < 1) (U V : Configuration gaugeGroup l) (e : Edge l)
    (hneighbors : ∀ i ∈ incidences e,
      linkChord (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1) / sqrt 2 ≤ δ) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) < ENNReal.ofReal (δ^2) := by
  apply (periodic_neighbor_wasserstein hl hβ U V e).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hδ)).2
  let S := ∑ i ∈ incidences e, linkChord (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1) / sqrt 2
  have hS : S ≤ 18*δ := calc
    _ ≤ ∑ _i ∈ incidences e, δ := Finset.sum_le_sum hneighbors
    _ = _ := by simp [incidence_count hl]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (sqrt_nonneg _)
  change (1/12+π^2/4)*(β*S)^2 < δ^2
  calc
    _ ≤ (1/12+π^2/4)*(β*(18*δ))^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hβ hS0) (mul_le_mul_of_nonneg_left hS hβ) 2) (by positivity)
    _ = ((1/12+π^2/4)*(18*β)^2)*δ^2 := by ring
    _ < _ := by simpa using mul_lt_mul_of_pos_right hwindow (sq_pos_of_pos hδ)

/-- The normalized matrix chord is at most the unit-sphere geodesic. -/
theorem normalized_chord_le_geodesic (u v : G) : linkChord u v / sqrt 2 ≤ linkGeodesic u v := by
  let D := linkGeodesic u v
  have hD : 0 ≤ D := arccos_nonneg _
  have hp : D ≤ π := arccos_le_pi _
  have hc : cos D = inner ℝ (linkCoordinates u) (linkCoordinates v) :=
    (cos_polarAngle (u*v⁻¹)).trans (relative_scalar u v)
  have he : matrixCoordinates (suMat u-suMat v) = linkCoordinates u-linkCoordinates v := by
    simpa only [one_smul,linkCoordinates] using matrixCoordinates_smul_sub 1 1 (suMat u) (suMat v)
  have ha : suMat u-suMat v ∈ quaternionAlgebra := quaternionAlgebra.sub_mem u.prop v.prop
  rw [linkChord,← matrixCoordinates_norm (A := suMat u - suMat v) ha,he]
  have hnorm : ‖linkCoordinates u-linkCoordinates v‖^2 = (2*sin (D/2))^2 := by
    rw [norm_sub_sq_real,coordinates_norm,coordinates_norm,← hc]
    have hcos := cos_two_mul_eq_one_sub (D/2)
    rw [show 2*(D/2)=D by ring] at hcos
    linarith only [hcos]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ D/2) (by linarith : D/2 ≤ π)
  have h := (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hs)).mp hnorm
  change ‖linkCoordinates u-linkCoordinates v‖ ≤ D
  rw [h]; linarith only [Real.sin_le (by linarith : 0 ≤ D/2)]

/-- Number of plaquette incidences at e occupied by the link a. -/
def neighborIncidenceCount {l : ℕ+} (e a : Edge l) : ℕ :=
  ∑ i ∈ incidences e, if (neighbor e i.1 i.2).1 = a then 1 else 0

/-- An entrywise upper bound on single-link geodesic Wasserstein influence.
Repeated appearances of one periodic neighbor contribute to the same entry. -/
def neighborInfluence {l : ℕ+} (β : ℝ) (e a : Edge l) :=
  sqrt (1/12+π^2/4) * β * (neighborIncidenceCount e a : ℝ)

theorem single_neighbor_wasserstein {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e a : Edge l) (hfix : ∀ b, b ≠ a → U b = V b) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤
      ENNReal.ofReal ((neighborInfluence β e a * linkGeodesic (U a) (V a))^2) := by
  apply (periodic_neighbor_wasserstein hl hβ U V e).trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : (∑ i ∈ incidences e,
      linkChord (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1) / sqrt 2) =
      (neighborIncidenceCount e a : ℝ) * (linkChord (U a) (V a) / sqrt 2) := by
    simp only [neighborIncidenceCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (neighbor e i.1 i.2).1 = a
    · simp [hi]
    · simp [hi,hfix _ hi,linkChord]
  have hm : 0 ≤ (neighborIncidenceCount e a : ℝ) := Nat.cast_nonneg _
  have hcoef : 0 ≤ neighborInfluence β e a := mul_nonneg (mul_nonneg (sqrt_nonneg _) hβ) hm
  rw [hsum]
  calc _ = (neighborInfluence β e a * (linkChord (U a) (V a) / sqrt 2))^2 := by
          unfold neighborInfluence; simp only [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1/12+π^2/4)]; ring
       _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hcoef (div_nonneg (norm_nonneg _) (sqrt_nonneg _)))
          (mul_le_mul_of_nonneg_left (normalized_chord_le_geodesic _ _) hcoef) 2

/-- Row sum of the explicit comparison matrix at every physical link. -/
theorem neighborInfluence_row {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    ∑ a : Edge l, neighborInfluence β e a = 18 * β * sqrt (1/12+π^2/4) := by
  simp only [neighborInfluence,← Finset.mul_sum,neighborIncidenceCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  simp [incidence_count hl]; ring

theorem neighborInfluence_self {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    neighborInfluence β e e = 0 := by
  have h : neighborIncidenceCount e e = 0 := Finset.sum_eq_zero fun i hi =>
    if_neg (neighbor_ne_self hl (Finset.mem_product.mp hi).1 i.2)
  simp [neighborInfluence,h]

theorem neighborInfluence_subunit_iff {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    (∑ a : Edge l, neighborInfluence β e a) < 1 ↔ β < 1 / (18*sqrt (1/12+π^2/4)) := by
  rw [neighborInfluence_row hl,lt_div_iff₀ (by positivity)]
  ring_nf

/-- An exact nonzero coupling with subunit full-link influence rows on every
periodic side at least two, without any common-pole condition. -/
theorem neighborInfluence_at_0034 {l : ℕ+} (hl : 1 < l.val) (e : Edge l) :
    ∑ a : Edge l, neighborInfluence (17/500) e a < 1 := by
  rw [neighborInfluence_row hl]
  have hπ := sq_lt_sq' (by linarith [pi_pos] : -(3.15:ℝ) < π) pi_lt_d2
  have hsq := sq_sqrt (by positivity : (0:ℝ) ≤ 1/12+π^2/4)
  nlinarith only [hπ,hsq,sq_nonneg (sqrt (1/12+π^2/4) - 250/153)]

#print axioms normalized_chord_le_geodesic
#print axioms single_neighbor_wasserstein
#print axioms neighborInfluence_self
#print axioms neighborInfluence_subunit_iff
#print axioms neighborInfluence_row
#print axioms neighborInfluence_at_0034
#print axioms cartesian_field_wasserstein
#print axioms periodic_neighbor_wasserstein
#print axioms periodic_neighbor_subunit
end
end YangMills.PeriodicWilson
