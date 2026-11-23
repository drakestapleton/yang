-- SPDX-License-Identifier: Apache-2.0
import WilsonRadialTransport
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Probability.Moments.Variance

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real Set
open scoped Matrix.Norms.Frobenius ComplexConjugate unitInterval ENNReal
noncomputable section
private abbrev G := gaugeGroup.image

private def pair (a b : ℂ) : M := !![a,b; -conj b,conj a]

private def unitPair (a b : ℂ) (h : length (pair a b) = 1) : G :=
  ⟨⟨pair a b, unitary_of_length_one (show pair a b ∈ quaternionAlgebra from ⟨rfl,rfl⟩) h⟩, ⟨rfl,rfl⟩⟩

private def phase (t : ℝ) := Complex.mk (cos t) (sin t)

/-- A diagonal SU(2) representative with eigenvalues exp(±it). -/
def diagonalLink (t : ℝ) : G := unitPair (phase t) 0 (by
  change sqrt (‖phase t‖^2 + ‖(0:ℂ)‖^2) = 1
  simp [← Complex.normSq_eq_norm_sq, phase, Complex.normSq_apply, ← sq, cos_sq_add_sin_sq])

@[fun_prop] theorem continuous_diag : Continuous diagonalLink := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun t => pair (phase t) 0)
  apply continuous_pi; intro i; apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;> simp [pair,phase,Complex.mk_eq_add_mul_I] <;> fun_prop

private theorem mat_injective : Function.Injective suMat := fun _ _ h => Subtype.ext (Subtype.ext h)
private theorem mat_mul (u v : G) : suMat (u*v) = suMat u * suMat v := rfl
private theorem mat_inv (u : G) : suMat u⁻¹ = star (suMat u) := rfl

private theorem scalar_trace (u : G) : (suMat u).trace.re = 2*(suMat u 0 0).re := by
  have hh : suMat u 1 1 = conj (suMat u 0 0) := u.prop.1
  simp [Matrix.trace,Fin.sum_univ_two,hh]; ring

private theorem scalar_conjugate (h u : G) : (suMat (h*u*h⁻¹) 0 0).re = (suMat u 0 0).re := by
  have he : (suMat (h*u*h⁻¹)).trace = (suMat u).trace := calc
    _ = (suMat (h⁻¹*(h*u))).trace := by rw [mat_mul h⁻¹, mat_mul (h*u), Matrix.trace_mul_comm]
    _ = _ := by simp
  linarith only [scalar_trace (h*u*h⁻¹), scalar_trace u, congrArg Complex.re he]

private theorem mat_add_inv (u : G) :
    suMat u + suMat u⁻¹ = ((2*(suMat u 0 0).re : ℝ) : ℂ) • (1:M) := by
  obtain ⟨hd,ho⟩ : suMat u ∈ quaternionAlgebra := u.prop
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat_inv, Matrix.star_apply, hd, ho, Complex.ext_iff] <;> ring

private def swapLink : G := unitPair 0 1 (by simp [length,pair])

private theorem mat_diag (t : ℝ) : suMat (diagonalLink t) = pair (phase t) 0 := rfl
private theorem mat_swap : suMat swapLink = pair 0 1 := rfl

private theorem diag_inverse_orbit (t : ℝ) :
    (diagonalLink t)⁻¹ = swapLink * diagonalLink t * swapLink⁻¹ := by
  apply mat_injective; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat_mul,mat_inv,mat_diag,mat_swap,pair,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

/-- The polar angle labels the conjugacy classes, including the two central links. -/
theorem link_conjugate_diagonal (u : G) :
    ∃ h : G, u = h * diagonalLink (polarAngle u) * h⁻¹ := by
  let v := diagonalLink (polarAngle u)
  have hs : (suMat v 0 0).re = (suMat u 0 0).re := cos_polarAngle u
  have he : suMat u + suMat u⁻¹ = suMat v + suMat v⁻¹ := by rw [mat_add_inv,mat_add_inv,hs]
  let A := suMat u - suMat v⁻¹
  by_cases hz : A = 0
  · have huv : u = v⁻¹ := mat_injective (sub_eq_zero.mp hz)
    exact ⟨swapLink, huv.trans (diag_inverse_orbit _)⟩
  have ha : A ∈ quaternionAlgebra := quaternionAlgebra.sub_mem u.prop (v⁻¹).prop
  obtain ⟨h,hh⟩ := polar ha
  change A = length A • suMat h at hh
  -- A intertwines u and v. Normalizing A therefore gives the conjugating link.
  have hlen : length A ≠ 0 := fun h0 => hz (by simpa [h0] using hh)
  have he' : A = suMat v - suMat u⁻¹ := by exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using he)
  have hint : suMat u * A = A * suMat v := calc
    _ = suMat u * suMat v - suMat (u*u⁻¹) := by rw [he',mul_sub,mat_mul]
    _ = suMat u * suMat v - suMat (v⁻¹*v) := by simp
    _ = A * suMat v := by rw [mat_mul]; dsimp [A]; rw [sub_mul]
  rw [hh,Matrix.mul_smul,Matrix.smul_mul] at hint
  have hc := congrArg (fun B : M => (length A)⁻¹ • B) hint
  simp only [smul_smul,inv_mul_cancel₀ hlen, one_smul] at hc
  have hgroup : u*h = h*v := mat_injective hc
  exact ⟨h, by rw [← hgroup]; simp⟩

/-- Unit-radius S³ great-circle angle between the two unit quaternions. -/
def linkGeodesic (u v : G) := polarAngle (u*v⁻¹)

/-- Conjugate the diagonal representative by h and translate back to the staple pole k. -/
def orbitLink (k : G) (t : ℝ) (h : G) := h * diagonalLink t * h⁻¹ * k⁻¹

private theorem diagonal_scalar_relative (a b : ℝ) :
    (suMat (diagonalLink a * (diagonalLink b)⁻¹) 0 0).re = cos (a-b) := by
  simp [mat_mul, mat_inv, mat_diag, pair, phase, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_two, Complex.mul_re, cos_sub]

theorem common_axis_distance (k h : G) {a b : ℝ} (ha : a ∈ Icc 0 π) (hb : b ∈ Icc 0 π) :
    linkGeodesic (orbitLink k a h) (orbitLink k b h) = |a-b| := by
  have he : orbitLink k a h * (orbitLink k b h)⁻¹ = h * (diagonalLink a * (diagonalLink b)⁻¹) * h⁻¹ := by
    unfold orbitLink; group
  rw [linkGeodesic,he,polarAngle,scalar_conjugate,diagonal_scalar_relative,← cos_abs,arccos_cos (abs_nonneg _) (abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩)]

/-- Opposite points on the equator have equal polar angle and full geodesic distance π. -/
theorem equal_angle_antipodes : ∃ u v : G, polarAngle u = polarAngle v ∧ linkGeodesic u v = π := by
  refine ⟨diagonalLink (π/2), diagonalLink (-(π/2)), ?_, ?_⟩
  · change arccos (cos (π/2)) = arccos (cos (-(π/2)))
    rw [cos_neg]
  · rw [linkGeodesic,polarAngle,diagonal_scalar_relative,show π/2 - -(π/2) = π by ring,cos_pi,arccos_neg_one]

/-- The full normalized Wilson one-link Haar tilt, in its pole representation. -/
def poleLaw (r : ℝ) (k : G) : Measure G := su2Haar.tilted (fun u => r*(suMat (u*k) 0 0).re)

theorem continuous_scalar_link : Continuous (fun u : G => (suMat u 0 0).re) :=
  Complex.continuous_re.comp ((continuous_apply 0).comp ((continuous_apply 0).comp
    (continuous_subtype_val.comp continuous_subtype_val)))

instance poleLaw_probability (r : ℝ) (k : G) : IsProbabilityMeasure (poleLaw r k) :=
  isProbabilityMeasure_tilted ((continuous_exp.comp (continuous_const.mul
    (continuous_scalar_link.comp (continuous_mul_const k)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private def rotateAt (k h u : G) := h*(u*k)*h⁻¹*k⁻¹
private theorem continuous_rotate (k : G) : Continuous (fun z : G × G => rotateAt k z.2 z.1) := by
  unfold rotateAt; fun_prop
theorem continuous_orbit (k : G) : Continuous (Function.uncurry (orbitLink k)) := by
  unfold Function.uncurry orbitLink
  exact (((continuous_snd.mul (continuous_diag.comp continuous_fst)).mul continuous_snd.inv).mul continuous_const)

theorem preserve_right (h : G) : MeasurePreserving (fun u : G => u*h) su2Haar su2Haar :=
  ⟨(continuous_mul_const _).measurable, PhaseFour.gaugeImage_haar_map_mul_right su2Haar h⟩

private theorem rotate_preserves (k h : G) (r : ℝ) :
    MeasurePreserving (rotateAt k h) (poleLaw r k) (poleLaw r k) := by
  have hp : MeasurePreserving (rotateAt k h) su2Haar su2Haar :=
    (preserve_right k⁻¹).comp ((preserve_right h⁻¹).comp ((measurePreserving_mul_left su2Haar h).comp (preserve_right k)))
  let f := fun u : G => r*(suMat (u*k) 0 0).re
  let w := fun u : G => ENNReal.ofReal (exp (f u) / ∫ x, exp (f x) ∂su2Haar)
  have hw : Measurable w := (continuous_exp.comp (continuous_const.mul
    (continuous_scalar_link.comp (continuous_mul_const k)))).div_const _ |>.measurable.ennreal_ofReal
  have hfix (u : G) : w (rotateAt k h u) = w u := by
    dsimp only [w,f,rotateAt]; rw [inv_mul_cancel_right,scalar_conjugate]
  refine ⟨hp.measurable,?_⟩
  change (su2Haar.withDensity w).map _ = su2Haar.withDensity w
  ext S hS
  rw [Measure.map_apply hp.measurable hS,withDensity_apply _ (hp.measurable hS),withDensity_apply _ hS]
  have hm := setLIntegral_map (μ := su2Haar) hS hw hp.measurable
  rw [hp.map_eq] at hm
  rw [hm]
  exact setLIntegral_congr_fun (hp.measurable hS) fun u _ => (hfix u).symm

/-- An independent Haar conjugator and a Wilson polar angle reproduce the entire
matrix-valued heat bath about the chosen pole. -/
theorem orbitLink_law (r : ℝ) (k : G) :
    ((angleLaw r).prod su2Haar).map (Function.uncurry (orbitLink k)) = poleLaw r k := by
  let μ := poleLaw r k
  let θ := fun u : G => polarAngle (u*k)
  have hθ : Continuous θ := continuous_arccos.comp (continuous_scalar_link.comp (continuous_mul_const k))
  have hcoords : MeasurePreserving θ μ (angleLaw r) := ⟨hθ.measurable, tilted_polarAngle r k⟩
  have hprod := hcoords.prod (MeasurePreserving.id su2Haar)
  rw [← hprod.map_eq, Measure.map_map (continuous_orbit k).measurable hprod.measurable]
  let F := fun z : G × G => orbitLink k (θ z.1) z.2
  let B := fun z : G × G => rotateAt k z.2 z.1
  have hF : Continuous F := by
    change Continuous (fun z : G × G => z.2 * diagonalLink (θ z.1) * z.2⁻¹ * k⁻¹)
    fun_prop
  have hB : Continuous B := continuous_rotate k
  change (μ.prod su2Haar).map F = μ
  ext S hS
  rw [Measure.map_apply hF.measurable hS, Measure.prod_apply (hF.measurable hS)]
  -- On each conjugacy class, changing the representative right-translates the Haar conjugator.
  have hfiber (u : G) : su2Haar (Prod.mk u ⁻¹' (F ⁻¹' S)) = su2Haar (Prod.mk u ⁻¹' (B ⁻¹' S)) := by
    obtain ⟨j,hj⟩ := link_conjugate_diagonal (u*k)
    have hid (h : G) : B (u,h) = F (u,h*j) := by
      change h*(u*k)*h⁻¹*k⁻¹ = (h*j)*diagonalLink (polarAngle (u*k))*(h*j)⁻¹*k⁻¹
      conv_lhs => rw [hj]
      group
    have hset : Prod.mk u ⁻¹' (B ⁻¹' S) = (fun h : G => h*j) ⁻¹' (Prod.mk u ⁻¹' (F ⁻¹' S)) :=
      Set.ext fun h => by change B (u,h) ∈ S ↔ F (u,h*j) ∈ S; rw [hid]
    rw [hset,(preserve_right j).measure_preimage (measurable_prodMk_left (hF.measurable hS)).nullMeasurableSet]
  simp_rw [hfiber]
  rw [← Measure.prod_apply (hB.measurable hS), Measure.prod_apply_symm (hB.measurable hS)]
  have hinner (h : G) : μ ((fun u => (u,h)) ⁻¹' (B ⁻¹' S)) = μ S :=
    (rotate_preserves k h r).measure_preimage hS.nullMeasurableSet
  simp_rw [hinner]
  simp

/-- Read the four real quaternion coordinates from the first matrix row. -/
def matrixCoordinates (A : M) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![(A 0 0).re,(A 0 0).im,(A 0 1).re,(A 0 1).im]

def linkCoordinates (u : G) := matrixCoordinates (suMat u)

theorem relative_scalar (u v : G) :
    (suMat (u*v⁻¹) 0 0).re = inner ℝ (linkCoordinates u) (linkCoordinates v) := by
  simp [mat_mul,mat_inv,Matrix.mul_apply,Matrix.star_apply,Fin.sum_univ_two,Complex.mul_re,
    linkCoordinates,matrixCoordinates,PiLp.inner_apply,Fin.sum_univ_four]
  ring

theorem coordinates_norm (u : G) : ‖linkCoordinates u‖ = 1 := by
  have h := relative_scalar u u
  rw [mul_inv_cancel,real_inner_self_eq_norm_sq] at h
  change (1:ℝ) = ‖linkCoordinates u‖^2 at h
  nlinarith [norm_nonneg (linkCoordinates u)]

/-- Identification with the round great-circle distance, via the angle between
unit vectors in real four-dimensional Euclidean space. -/
theorem linkGeodesic_eq_angle (u v : G) :
    linkGeodesic u v = InnerProductGeometry.angle (linkCoordinates u) (linkCoordinates v) := by
  simp [linkGeodesic,polarAngle,InnerProductGeometry.angle,relative_scalar,coordinates_norm]

theorem continuous_geodesic : Continuous (Function.uncurry linkGeodesic) :=
  continuous_arccos.comp (continuous_scalar_link.comp (continuous_fst.mul continuous_snd.inv))

private abbrev sampleSpace := unitInterval × G
private def sample (r : ℝ) (k : G) (z : sampleSpace) := orbitLink k (angleQuantile r z.1) z.2
private theorem sample_cont (r : ℝ) (k : G) : Continuous (sample r k) := by
  have hQ := continuous_Q r
  change Continuous (fun z : sampleSpace => z.2 * diagonalLink (angleQuantile r z.1) * z.2⁻¹ * k⁻¹)
  fun_prop

private theorem sample_law (r : ℝ) (k : G) :
    (volume.prod su2Haar).map (sample r k) = poleLaw r k := by
  have hQ : MeasurePreserving (angleQuantile r) volume (angleLaw r) :=
    ⟨(continuous_Q r).measurable,quantile_pushforward r⟩
  have hp := hQ.prod (MeasurePreserving.id su2Haar)
  calc
    _ = ((volume.prod su2Haar).map (Prod.map (angleQuantile r) id)).map (Function.uncurry (orbitLink k)) :=
      (Measure.map_map (continuous_orbit k).measurable hp.measurable).symm
    _ = _ := by rw [hp.map_eq,orbitLink_law]

/-- A full-link coupling using the same uniform rank and Haar conjugator for both samples. -/
def linkCoupling (r s : ℝ) (k j : G) : Measure (G × G) :=
  (volume.prod su2Haar).map (fun z : sampleSpace => (sample r k z,sample s j z))

theorem linkCoupling_marginals (r s : ℝ) (k j : G) :
    (linkCoupling r s k j).fst = poleLaw r k ∧ (linkCoupling r s k j).snd = poleLaw s j := by
  constructor
  · rw [linkCoupling, Measure.fst_map_prodMk (sample_cont s j).measurable,sample_law]
  · rw [linkCoupling, Measure.snd_map_prodMk (sample_cont r k).measurable,sample_law]

/-- At a common pole the geodesic squared cost of the lifted coupling equals the
squared cost of the original angular coupling exactly. -/
theorem linkCoupling_common_cost (r s : ℝ) (k : G) :
    (∫ z, linkGeodesic z.1 z.2 ^ 2 ∂linkCoupling r s k k) =
    ∫ z, (z.2-z.1)^2 ∂radialCoupling r s := by
  let g := fun p : unitInterval => (angleQuantile s p-angleQuantile r p)^2
  have hg : Continuous g := ((continuous_Q s).sub (continuous_Q r)).pow 2
  have hpair := (sample_cont r k).prodMk (sample_cont s k)
  have hc : Continuous (fun z : G × G => linkGeodesic z.1 z.2 ^ 2) := continuous_geodesic.pow 2
  rw [linkCoupling, integral_map hpair.aemeasurable hc.aestronglyMeasurable,
    radialCoupling, integral_map ((continuous_Q r).prodMk (continuous_Q s)).aemeasurable
      (show AEStronglyMeasurable (fun z : ℝ × ℝ => (z.2-z.1)^2) _ from
        ((continuous_snd.sub continuous_fst).pow 2).aestronglyMeasurable)]
  change (∫ z : sampleSpace, linkGeodesic (sample r k z) (sample s k z)^2 ∂volume.prod su2Haar) = ∫ p, g p
  have hpoint (z : sampleSpace) : linkGeodesic (sample r k z) (sample s k z)^2 = g z.1 := by
    unfold sample g
    rw [common_axis_distance _ _ (quantile_mem r z.1) (quantile_mem s z.1), sq_abs]; ring
  simp_rw [hpoint]
  have hp := measurePreserving_fst (μ := (volume : Measure unitInterval)) (ν := su2Haar)
  rw [← integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable,hp.map_eq]

/-- Squared Wasserstein cost for full links with the unit-radius S³ geodesic. -/
def linkWassersteinSq (μ ν : Measure G) : ℝ≥0∞ :=
  ⨅ γ : {P : Measure (G × G) // P.fst = μ ∧ P.snd = ν},
    ∫⁻ z, ENNReal.ofReal (linkGeodesic z.1 z.2 ^ 2) ∂γ.val

private theorem linkWassersteinSq_le_cost (r s : ℝ) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤ ENNReal.ofReal
      (∫ z, linkGeodesic z.1 z.2^2 ∂linkCoupling r s k j) := by
  let γ : {P : Measure (G × G) // P.fst = poleLaw r k ∧ P.snd = poleLaw s j} :=
    ⟨linkCoupling r s k j,linkCoupling_marginals r s k j⟩
  apply (iInf_le _ γ).trans_eq
  haveI : IsProbabilityMeasure (linkCoupling r s k j) :=
    Measure.isProbabilityMeasure_map ((sample_cont r k).prodMk (sample_cont s j)).aemeasurable
  exact (ofReal_integral_eq_lintegral_ofReal ((continuous_geodesic.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (.of_forall fun z => sq_nonneg (linkGeodesic z.1 z.2))).symm

theorem common_pole_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s k) ≤ ENNReal.ofReal ((s-r)^2/12) := by
  apply (linkWassersteinSq_le_cost r s k k).trans
  rw [linkCoupling_common_cost]
  exact ENNReal.ofReal_le_ofReal (radialCoupling_cost hr hs)

private theorem cost_on_samples (r s : ℝ) (k j : G) :
    (∫ z, linkGeodesic z.1 z.2^2 ∂linkCoupling r s k j) =
      ∫ z : sampleSpace, linkGeodesic (sample r k z) (sample s j z)^2 ∂volume.prod su2Haar := by
  have hc : Continuous (fun z : G × G => linkGeodesic z.1 z.2 ^ 2) := continuous_geodesic.pow 2
  exact integral_map ((sample_cont r k).prodMk (sample_cont s j)).aemeasurable hc.aestronglyMeasurable

private theorem rigid_distance (t : ℝ) (h k j : G) :
    linkGeodesic (orbitLink k t h) (orbitLink j t h) = linkGeodesic k⁻¹ j⁻¹ := by
  let q := h * diagonalLink t * h⁻¹
  have he : orbitLink k t h * (orbitLink j t h)⁻¹ = q * (k⁻¹ * j) * q⁻¹ := by
    unfold orbitLink q; group
  simp [linkGeodesic,he,polarAngle,scalar_conjugate]

theorem geo_triangle (u v w : G) :
    linkGeodesic u w ≤ linkGeodesic u v + linkGeodesic v w := by
  simp only [linkGeodesic_eq_angle]
  exact InnerProductGeometry.angle_le_angle_add_angle _ _ _

private theorem sample_distance_cont (r s : ℝ) (k j : G) :
    Continuous (fun z : sampleSpace => linkGeodesic (sample r k z) (sample s j z)) := by
  unfold linkGeodesic polarAngle
  exact continuous_arccos.comp (continuous_scalar_link.comp ((sample_cont r k).mul (sample_cont s j).inv))

/-- Full-link comparison for arbitrary poles. The direction term is the geodesic
cost of a rigid translation of the meridian, in radians. -/
theorem moving_pole_wasserstein {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k j : G) :
    linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤
      ENNReal.ofReal ((|s-r| / sqrt 12 + linkGeodesic k⁻¹ j⁻¹)^2) := by
  let μ : Measure sampleSpace := volume.prod su2Haar
  let D := linkGeodesic k⁻¹ j⁻¹
  let R := |s-r| / sqrt 12
  let g := fun z : sampleSpace => linkGeodesic (sample r k z) (sample s k z)
  let f := fun z : sampleSpace => linkGeodesic (sample r k z) (sample s j z)
  have gcon : Continuous g := sample_distance_cont r s k k
  have fcon : Continuous f := sample_distance_cont r s k j
  have hD : 0 ≤ D := arccos_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR2 : R^2 = (s-r)^2 / 12 := by
    simp [R,div_pow,sq_abs,Real.sq_sqrt]
  have hsecond : (∫ z, g z^2 ∂μ) ≤ R^2 := by
    rw [hR2,← cost_on_samples r s k k,linkCoupling_common_cost]
    exact radialCoupling_cost hr hs
  -- Nonnegative variance bounds the mean meridian displacement by its root mean square.
  have hmean : (∫ z, g z ∂μ) ≤ R := by
    have hv := ProbabilityTheory.variance_nonneg g μ
    rw [ProbabilityTheory.variance_eq_sub (gcon.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hv
    change 0 ≤ (∫ z, g z ^ 2 ∂μ) - (∫ z, g z ∂μ)^2 at hv
    nlinarith only [hv,hsecond,hR, sq_nonneg ((∫ z, g z ∂μ) - R)]
  have hpoint (z : sampleSpace) : f z^2 ≤ g z^2 + (2*D)*g z + D^2 := by
    have ht := geo_triangle (sample r k z) (sample s k z) (sample s j z)
    change f z ≤ g z + linkGeodesic (orbitLink k _ _) (orbitLink j _ _) at ht
    rw [rigid_distance] at ht
    have hsq : f z ^ 2 ≤ (g z + D)^2 := pow_le_pow_left₀ (arccos_nonneg _ : 0 ≤ f z) ht 2
    exact hsq.trans_eq (by ring)
  have hg2 : Integrable (fun z => g z^2) μ :=
    (gcon.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlin : Integrable (fun z => (2*D)*g z) μ :=
    (gcon.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  have hsum : Integrable (fun z => g z^2 + (2*D)*g z) μ := hg2.add hlin
  have hf2 : Integrable (fun z => f z^2) μ :=
    (fcon.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (linkWassersteinSq_le_cost r s k j).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [cost_on_samples]
  have hm := integral_mono hf2 (hsum.add (integrable_const (D^2))) hpoint
  change (∫ z, f z^2 ∂μ) ≤ ∫ z, g z^2 + (2*D)*g z + D^2 ∂μ at hm
  rw [integral_add hsum (integrable_const (D^2)),integral_add hg2 hlin,integral_const_mul,integral_const] at hm
  simp only [probReal_univ, one_smul] at hm
  change (∫ z, f z^2 ∂μ) ≤ (R+D)^2
  linarith only [hm,hsecond,mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ 2*D)]

/-- Every pair of periodic heat baths admits full-link transport controlled by
the change in staple strength and the separation of the two pole centers. -/
theorem heatBath_link_wasserstein {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    ∃ k j : G, heatBath β U e = poleLaw (fieldStrength β U e) k ∧
      heatBath β V e = poleLaw (fieldStrength β V e) j ∧
      linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal
        ((|fieldStrength β V e - fieldStrength β U e| / sqrt 12 + linkGeodesic k⁻¹ j⁻¹)^2) := by
  obtain ⟨k,hk⟩ := heatBath_eq_tilt hl β U e
  obtain ⟨j,hj⟩ := heatBath_eq_tilt hl β V e
  refine ⟨k,j,hk,hj,?_⟩
  rw [hk,hj]
  exact moving_pole_wasserstein (fieldStrength_mem hβ U e).1 (fieldStrength_mem hβ V e).1 k j

/-- Degree-18 response of the complete periodic Wilson heat baths whenever
their normalized Haar tilts admit the same staple pole. -/
theorem common_pole_degree18 {l : ℕ+} (hl : 1 < l.val) {β δ : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) (k : G)
    (hU : heatBath β U e = poleLaw (fieldStrength β U e) k)
    (hV : heatBath β V e = poleLaw (fieldStrength β V e) k)
    (hneighbors : ∀ i ∈ incidences e,
      linkChord (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1) / sqrt 2 ≤ δ) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal (27*β^2*δ^2) := by
  rw [hU,hV]
  exact (common_pole_wasserstein (fieldStrength_mem hβ U e).1 (fieldStrength_mem hβ V e).1 k).trans
    (ENNReal.ofReal_le_ofReal (fieldStrength_degree18_sq hl hβ U V e hneighbors))

/-- The staple matrix of a fixed background supplies a single pole for all couplings. -/
theorem heatBath_fixed_pole {l : ℕ+} (hl : 1 < l.val) (U : Configuration gaugeGroup l) (e : Edge l) :
    ∃ k : G, ∀ β : ℝ, heatBath β U e = poleLaw (fieldStrength β U e) k := by
  obtain ⟨k,hk⟩ := su2_field_pole 1 U e
  refine ⟨k,fun β => heatBath_eq_tilt_of_projection hl β U e k (fun v => ?_)⟩
  have h := hk v
  simp only [one_mul] at h
  rw [h]
  unfold fieldStrength
  ring

/-- Full-link transport at a fixed periodic background for all nonnegative bare
couplings. The six staples give the uniform squared coefficient three. -/
theorem heatBath_beta_wasserstein {l : ℕ+} (hl : 1 < l.val) {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (U : Configuration gaugeGroup l) (e : Edge l) :
    linkWassersteinSq (heatBath β U e) (heatBath γ U e) ≤ ENNReal.ofReal (3*(γ-β)^2) := by
  obtain ⟨k,hk⟩ := heatBath_fixed_pole hl U e
  rw [hk β,hk γ]
  apply (common_pole_wasserstein (fieldStrength_mem hβ U e).1 (fieldStrength_mem hγ U e).1 k).trans
  apply ENNReal.ofReal_le_ofReal
  let L := fieldStrength 1 U e
  have hL : L ∈ Icc 0 6 := by simpa [L] using fieldStrength_mem (by norm_num : (0:ℝ) ≤ 1) U e
  have he : fieldStrength γ U e - fieldStrength β U e = (γ-β)*L := by dsimp [L,fieldStrength]; ring
  have hL2 := sq_le_sq' (by linarith [hL.1] : -(6:ℝ) ≤ L) hL.2
  rw [he,mul_pow]
  linarith only [mul_le_mul_of_nonneg_left hL2 (sq_nonneg (γ-β))]

@[simp] theorem diagonalLink_zero : diagonalLink 0 = 1 := by
  apply mat_injective
  change pair (phase 0) 0 = (1:M)
  ext i j; fin_cases i <;> fin_cases j <;> simp [pair,phase,Complex.ext_iff]

theorem diagonalLink_add (s t : ℝ) : diagonalLink (s+t) = diagonalLink s * diagonalLink t := by
  have hphase : phase (s+t) = phase s * phase t := by
    rw [Complex.ext_iff]; simp [phase,cos_add,sin_add,Complex.mul_re,Complex.mul_im]; ring
  apply mat_injective
  rw [mat_mul,mat_diag,mat_diag,mat_diag,hphase]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pair,Matrix.mul_apply,Fin.sum_univ_two]

theorem diagonalLink_periodic : Function.Periodic diagonalLink (2*π) := by
  intro t
  apply mat_injective
  simp [mat_diag,phase,cos_add_two_pi,sin_add_two_pi]

theorem linkGeodesic_mul_left (u v h : G) : linkGeodesic (h*u) (h*v) = linkGeodesic u v := by
  have he : h*u*(h*v)⁻¹ = h*(u*v⁻¹)*h⁻¹ := by group
  simp only [linkGeodesic,he,polarAngle,scalar_conjugate]

theorem linkGeodesic_mul_right (u v h : G) : linkGeodesic (u*h) (v*h) = linkGeodesic u v := by
  have he : u*h*(v*h)⁻¹ = u*v⁻¹ := by group
  simp only [linkGeodesic,he]

theorem diagonalLink_distance_le (a b : ℝ) : linkGeodesic (diagonalLink a) (diagonalLink b) ≤ |a-b| := by
  rw [linkGeodesic,polarAngle,diagonal_scalar_relative,←cos_abs]
  by_cases h : |a-b| ≤ π
  · rw [arccos_cos (abs_nonneg _) h]
  · exact (arccos_le_pi _).trans (le_of_not_ge h)

#print axioms heatBath_fixed_pole
#print axioms heatBath_beta_wasserstein
#print axioms moving_pole_wasserstein
#print axioms heatBath_link_wasserstein
#print axioms common_pole_degree18
#print axioms linkGeodesic_eq_angle
#print axioms linkCoupling_marginals
#print axioms linkCoupling_common_cost
#print axioms common_pole_wasserstein
#print axioms orbitLink_law
#print axioms link_conjugate_diagonal
#print axioms common_axis_distance
#print axioms equal_angle_antipodes
end
end YangMills.PeriodicWilson
