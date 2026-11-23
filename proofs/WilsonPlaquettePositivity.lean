-- SPDX-License-Identifier: Apache-2.0
import WilsonPlaquetteTransfer
import PlaquettePositiveKernel

namespace YangMills.PlaquetteTransfer
open MeasureTheory
open scoped Topology BigOperators ComplexConjugate
noncomputable section
variable {L : ℕ+}

private def coord (u : G) : Fin 4 → ℝ :=
  ![(u.val.val 0 0).re, (u.val.val 0 0).im, (u.val.val 0 1).re, (u.val.val 0 1).im]

private theorem coord_cont (i : Fin 4) : Continuous (fun u : G => coord u i) := by
  have hm : Continuous (fun u : G => (u.val.val : FundamentalSU2.M)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have c (j : Fin 2) : Continuous (fun u : G => u.val.val 0 j) :=
    (continuous_apply j).comp ((continuous_apply 0).comp hm)
  fin_cases i <;> simp [coord] <;> first | exact Complex.continuous_re.comp (c _) | exact Complex.continuous_im.comp (c _)

theorem trace_inner (u v : G) : normalizedTrace (u*v⁻¹) = ∑ i, coord u i * coord v i := by
  rw [normalizedTrace_scalar]
  let A : FundamentalSU2.M := u.val.val
  let B : FundamentalSU2.M := v.val.val
  have h : ((A * star B) 0 0).re =
      (A 0 0).re * (B 0 0).re + (A 0 0).im * (B 0 0).im +
      ((A 0 1).re * (B 0 1).re + (A 0 1).im * (B 0 1).im) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_re]
  rw [show ((u*v⁻¹).val.val 0 0).re = ((A * star B) 0 0).re from rfl, h]
  simp [A, B, coord, Fin.sum_univ_succ, add_assoc]
  rfl

abbrev Feature (L : ℕ+) := (Space L × Fin 3) × Fin 4
def features (j : Feature L) : V (Slice L) :=
  ⟨fun U => coord (U j.1) j.2, (coord_cont j.2).comp (continuous_apply j.1)⟩

theorem features_separate (U W : Slice L) (hne : U ≠ W) :
    ∃ j : Feature L, features j U ≠ features j W := by
  by_contra! h
  apply hne
  funext e
  let A : FundamentalSU2.M := (U e).val.val
  let B : FundamentalSU2.M := (W e).val.val
  have h₀ : A 0 0 = B 0 0 := Complex.ext (h (e,0)) (h (e,1))
  have h₁ : A 0 1 = B 0 1 := Complex.ext (h (e,2)) (h (e,3))
  obtain ⟨a₀,a₁⟩ := (show A ∈ FundamentalSU2.quaternionAlgebra from (U e).property)
  obtain ⟨b₀,b₁⟩ := (show B ∈ FundamentalSU2.quaternionAlgebra from (W e).property)
  apply Subtype.ext
  apply Subtype.ext
  change A = B
  have h₁₀ : A 1 0 = B 1 0 := by rw [a₁,b₁,h₁]
  have h₁₁ : A 1 1 = B 1 1 := by rw [a₀,b₀,h₀]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> first | exact h₀ | exact h₁ | exact h₁₀ | exact h₁₁

private theorem temporal_gram (U W : Slice L) (h : Vertical L) :
    temporal U W h = (Fintype.card (Space L × Fin 3) : ℝ) -
      ∑ j : Feature L, features j U * features j (changeGauge h W) := by
  have he (x : Space L) (i : Fin 3) :
      U (x,i) * h (shift x i) * (W (x,i))⁻¹ * (h x)⁻¹ = U (x,i) * (changeGauge h W (x,i))⁻¹ := by
    simp only [changeGauge]; group
  simp only [temporal, he, trace_inner, Finset.sum_sub_distrib, Fintype.sum_prod_type,
    features, ContinuousMap.coe_mk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp [Fintype.card_prod]

def amplitude (β : ℝ) : V (Slice L) :=
  ⟨fun U => Real.exp (-β * (spatial U + Fintype.card (Space L × Fin 3))/2), by
    have hs : Continuous (spatial (L := L)) := by
      unfold spatial
      apply continuous_finsetSum
      intro x _
      apply Continuous.add
      · apply Continuous.add <;> exact continuous_const.sub (face_continuous _ _ _)
      · exact continuous_const.sub (face_continuous _ _ _)
    fun_prop⟩

private def freeBond (β : ℝ) (U W : Slice L) :=
  amplitude β U * amplitude β W * Real.exp (β * ∑ j : Feature L, features j U * features j W)

private theorem free_cont (β : ℝ) :
    Continuous (fun p : Slice L × Slice L => freeBond β p.1 p.2) := by
  unfold freeBond
  fun_prop

private theorem bond_eq_free (β : ℝ) (U W : Slice L) (h : Vertical L) :
    bond β U W h = freeBond β U (changeGauge h W) := by
  have hs : spatial (changeGauge h W) = spatial W := by simp [spatial, face_gauge]
  simp only [bond, freeBond, amplitude, ContinuousMap.coe_mk, hs, temporal_gram,
    ← Real.exp_add]
  congr 1
  ring

private theorem gauge_preserves_prior (g : Vertical L) :
    MeasurePreserving (changeGauge g) (sliceLaw L) (sliceLaw L) := by
  refine measurePreserving_pi (fun _ : Space L × Fin 3 => PeriodicWilson.su2Haar)
    (fun _ => PeriodicWilson.su2Haar) (f := fun e u => g e.1 * u * (g (shift e.1 e.2))⁻¹) ?_
  intro e
  have right (k : G) : MeasurePreserving (fun u : G => u*k) PeriodicWilson.su2Haar PeriodicWilson.su2Haar :=
    ⟨(continuous_mul_const _).measurable, PhaseFour.gaugeImage_haar_map_mul_right _ _⟩
  exact (right _).comp (measurePreserving_mul_left _ _)

private theorem operator_on_physical (β : ℝ) (f : V (Slice L)) (hf : f ∈ physicalSlices L) (U : Slice L) :
    wilsonOperator L β 1 f U = ∫ W, freeBond β U W * f W ∂sliceLaw L := by
  let ν := Measure.pi (fun _ : Space L => PeriodicWilson.su2Haar)
  change (∫ W, ((∫ h, bond β U W h ∂ν) / 1) * f W ∂sliceLaw L) = _
  simp only [div_one, ← integral_mul_const]
  have hc : Continuous (fun p : Slice L × Vertical L => bond β U p.1 p.2 * f p.1) := by
    have hp : Continuous (fun p : Slice L × Vertical L => ((U,p.1),p.2)) :=
      (continuous_const.prodMk continuous_fst).prodMk continuous_snd
    exact ((bond_continuous (L := L) β).comp hp).mul (f.continuous.comp continuous_fst)
  rw [integral_integral_swap (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  let a := fun W => freeBond β U W * f W
  have ha : Continuous a := ((free_cont (L := L) β).comp (continuous_const.prodMk continuous_id)).mul f.continuous
  have he (h : Vertical L) : (∫ W, bond β U W h * f W ∂sliceLaw L) = ∫ W, a W ∂sliceLaw L := by
    simp_rw [bond_eq_free]
    have mp := gauge_preserves_prior h
    have hm := integral_map mp.measurable.aemeasurable (ha.aestronglyMeasurable (μ := (sliceLaw L).map (changeGauge h)))
    rw [mp.map_eq] at hm
    simp only [a, hf h _] at hm
    exact hm.symm
  simp_rw [he]
  simp [a]

private theorem wilson_quadratic (β : ℝ) (f : V (Slice L)) (hf : f ∈ physicalSlices L) :
    let g := amplitude β * f
    pairing (sliceLaw L) f (wilsonOperator L β 1 f) =
      ∫ p : Slice L × Slice L, (g p.1 * g p.2) *
        Real.exp (β * ∑ j : Feature L, features j p.1 * features j p.2) ∂(sliceLaw L).prod (sliceLaw L) := by
  intro g
  have hcont : Continuous (fun p : Slice L × Slice L =>
      (g p.1 * g p.2) * Real.exp (β * ∑ j : Feature L, features j p.1 * features j p.2)) := by fun_prop
  rw [integral_prod _ (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  unfold pairing
  simp_rw [operator_on_physical β f hf, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  apply integral_congr_ae
  filter_upwards with W
  simp only [g, freeBond, ContinuousMap.mul_apply]
  ring

/-- The fundamental Wilson transfer form is positive semidefinite on the
physical sector at nonnegative coupling. -/
theorem wilson_quadratic_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : V (Slice L)) (hf : f ∈ physicalSlices L) :
    0 ≤ pairing (sliceLaw L) f (wilsonOperator L β 1 f) := by
  rw [wilson_quadratic β f hf]
  exact exp_gram_nonneg _ _ _ _ hβ

/-- At positive coupling every nonzero physical slice function has strictly
positive Wilson quadratic form. There is no assumption on its transfer spectrum. -/
theorem wilson_quadratic_pos (β : ℝ) (hβ : 0 < β) (f : V (Slice L)) (hf : f ∈ physicalSlices L) (hn : f ≠ 0) :
    0 < pairing (sliceLaw L) f (wilsonOperator L β 1 f) := by
  rw [wilson_quadratic β f hf]
  apply exp_gram_pos _ _ features_separate _ _ _ hβ
  intro hz
  apply hn
  ext U
  have he := DFunLike.congr_fun hz U
  exact (mul_eq_zero.mp he).resolve_left (Real.exp_ne_zero _)

theorem word_overlap_bound (β : ℝ) (hβ : 0 < β) (f : V (Slice L)) (hf : f ∈ physicalSlices L)
    (n : ℕ) (w : Fin n → Feature L) :
    (n.factorial : ℝ)⁻¹ * β^n * (pairing (sliceLaw L) (amplitude β * word features w) f)^2 ≤
      pairing (sliceLaw L) f (wilsonOperator L β 1 f) := by
  let g := amplitude β * f
  have hs := exp_gram_series (sliceLaw L) features g β
  have h₁ := hs.summable.le_tsum n (fun _ _ => by positivity)
  rw [hs.tsum_eq] at h₁
  rw [wilson_quadratic β f hf]
  apply le_trans _ h₁
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he : pairing (sliceLaw L) (amplitude β * word features w) f = ∫ x, (g * word features w) x ∂sliceLaw L := by
    unfold pairing
    simp only [g, ContinuousMap.mul_apply]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he]
  exact Finset.single_le_sum (f := fun i : Fin n → Feature L => (∫ x, (g * word features i) x ∂sliceLaw L)^2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ w)

#print axioms wilson_quadratic_nonneg
#print axioms wilson_quadratic_pos
end
end YangMills.PlaquetteTransfer
