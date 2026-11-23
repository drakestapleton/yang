-- SPDX-License-Identifier: Apache-2.0
import PlaquetteKernelTrace

/-! The exponential of a real Gram kernel has nonnegative quadratic form.
Each Taylor coefficient integrates to a sum of squares indexed by words. -/
namespace YangMills.PlaquetteTransfer
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] {I : Type*} [Fintype I]
variable (μ : Measure X) [IsProbabilityMeasure μ]

private def integrateMap (ρ : Measure X) [IsProbabilityMeasure ρ] : V X →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂ρ
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun r f => integral_const_mul r _ }
    1 (by
      intro f
      simpa using norm_integral_le_of_norm_le_const (μ := ρ) (f := fun x => f x)
        (.of_forall f.norm_coe_le_norm))

private def separated (a b : V X) : V (X × X) :=
  (a.comp ⟨Prod.fst, continuous_fst⟩) * (b.comp ⟨Prod.snd, continuous_snd⟩)

private def gram (h : I → V X) : V (X × X) := ∑ i, separated (h i) (h i)

def word {n : ℕ} (h : I → V X) (w : Fin n → I) : V X := ∏ j, h (w j)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
private theorem gram_pow (h : I → V X) (n : ℕ) :
    gram h ^ n = ∑ w : Fin n → I, separated (word h w) (word h w) := by
  classical
  ext p
  simp only [gram, ContinuousMap.pow_apply, ContinuousMap.sum_apply, separated,
    ContinuousMap.mul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, word, ContinuousMap.prod_apply]
  rw [← Fin.prod_const, Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

private def quadratic (f : V X) : V (X × X) →L[ℝ] ℝ :=
  (integrateMap (μ.prod μ)).comp (ContinuousLinearMap.mul ℝ _ (separated f f))

private theorem quadratic_rank (f g : V X) :
    quadratic μ f (separated g g) = (∫ x, (f*g) x ∂μ)^2 := by
  change (∫ p, (f p.1 * f p.2) * (g p.1 * g p.2) ∂μ.prod μ) = _
  have he (p : X × X) : (f p.1 * f p.2) * (g p.1 * g p.2) = (f*g) p.1 * (f*g) p.2 := by
    simp only [ContinuousMap.mul_apply]; ring
  simp_rw [he]
  rw [integral_prod_mul, sq]

theorem exp_gram_series (h : I → V X) (f : V X) (b : ℝ) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * b^n *
      ∑ w : Fin n → I, (∫ x, (f * word h w) x ∂μ)^2)
    (∫ p : X × X, (f p.1 * f p.2) * Real.exp (b * ∑ i, h i p.1 * h i p.2) ∂μ.prod μ) := by
  let A := b • gram h
  have hs := (quadratic μ f).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A)
  have he (p : X × X) : NormedSpace.exp A p = Real.exp (b * ∑ i, h i p.1 * h i p.2) := by
    rw [Real.exp_eq_exp_ℝ]
    have hm := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ p : V (X × X) →ₐ[ℝ] ℝ)
      (continuous_eval_const p) A
    simpa [A, gram, separated, ContinuousMap.sum_apply] using hm
  have heq : quadratic μ f (NormedSpace.exp A) = _ :=
    integral_congr_ae (μ := μ.prod μ) (.of_forall fun p => congrArg ((f p.1 * f p.2) * ·) (he p))
  rw [heq] at hs
  simpa only [A, smul_pow, gram_pow, map_smul, map_sum, quadratic_rank, smul_eq_mul, mul_assoc] using hs

theorem exp_gram_nonneg (h : I → V X) (f : V X) (b : ℝ) (hb : 0 ≤ b) :
    0 ≤ ∫ p : X × X, (f p.1 * f p.2) * Real.exp (b * ∑ i, h i p.1 * h i p.2) ∂μ.prod μ :=
  (exp_gram_series μ h f b).nonneg fun n => by positivity

omit [SecondCountableTopology X] [Fintype I] [MeasurableSpace X] [BorelSpace X] in
theorem zero_of_word_tests (h : I → V X) (sep : ∀ x y : X, x ≠ y → ∃ i, h i x ≠ h i y)
    (ℓ : V X →L[ℝ] ℝ) (hall : ∀ (n : ℕ) (w : Fin n → I), ℓ (word h w) = 0) (f : V X) : ℓ f = 0 := by
  classical
  let A := Algebra.adjoin ℝ (Set.range h)
  have hs : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := sep x y hxy
    exact ⟨_, ⟨h i, Algebra.subset_adjoin (Set.mem_range_self i), rfl⟩, hi⟩
  have hadj : A.toSubmodule ≤ LinearMap.ker ℓ.toLinearMap := by
    rw [show A.toSubmodule = _ from Algebra.adjoin_eq_span ℝ (Set.range h), Submodule.span_le]
    intro g hg
    have hw : ∃ (n : ℕ) (w : Fin n → I), g = word h w := by
      induction hg using Submonoid.closure_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact ⟨1, fun _ => i, by simp [word]⟩
      | one => exact ⟨0, Fin.elim0, by simp [word]⟩
      | mul a b ha hb ia ib =>
        obtain ⟨n,w,rfl⟩ := ia
        obtain ⟨m,v,rfl⟩ := ib
        exact ⟨n+m, Fin.addCases w v, by simp [word, Fin.prod_univ_add]⟩
    obtain ⟨n,w,rfl⟩ := hw
    exact hall n w
  have hclosed : IsClosed (LinearMap.ker ℓ.toLinearMap : Set (V X)) := ℓ.isClosed_ker
  have hmem : f ∈ closure (A : Set (V X)) :=
    ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints A hs f
  exact (closure_minimal hadj hclosed) hmem

omit [SecondCountableTopology X] [Fintype I] in
private theorem word_moment_ne_zero [μ.IsOpenPosMeasure] (h : I → V X)
    (sep : ∀ x y : X, x ≠ y → ∃ i, h i x ≠ h i y) (f : V X) (hf : f ≠ 0) :
    ∃ (n : ℕ) (w : Fin n → I), (∫ x, (f * word h w) x ∂μ) ≠ 0 := by
  by_contra! hall
  let ℓ := (integrateMap μ).comp (ContinuousLinearMap.mul ℝ _ f)
  have hzero : ℓ f = 0 := zero_of_word_tests h sep ℓ hall f
  have hpoint : ∃ x, f x ≠ 0 := by
    by_contra! hz
    exact hf (ContinuousMap.ext fun x => hz x)
  obtain ⟨x,hx⟩ := hpoint
  have hp : 0 < ∫ x, (f*f) x ∂μ := (f*f).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun t => mul_self_nonneg _) (mul_ne_zero hx hx)
  exact hp.ne' hzero

/-- With separating features and full support the form is strictly positive. -/
theorem exp_gram_pos [μ.IsOpenPosMeasure] (h : I → V X)
    (sep : ∀ x y : X, x ≠ y → ∃ i, h i x ≠ h i y) (f : V X) (hf : f ≠ 0) (b : ℝ) (hb : 0 < b) :
    0 < ∫ p : X × X, (f p.1 * f p.2) * Real.exp (b * ∑ i, h i p.1 * h i p.2) ∂μ.prod μ := by
  obtain ⟨n,w,hw⟩ := word_moment_ne_zero μ h sep f hf
  have hn : 0 < ∑ w : Fin n → I, (∫ x, (f * word h w) x ∂μ)^2 :=
    Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨w, Finset.mem_univ _, sq_pos_of_ne_zero hw⟩
  have hs := exp_gram_series μ h f b
  exact lt_of_lt_of_le (mul_pos (mul_pos (by positivity) (pow_pos hb n)) hn)
    (hs.summable.le_tsum n (fun _ _ => by positivity) |>.trans_eq hs.tsum_eq)

#print axioms exp_gram_series
#print axioms exp_gram_pos
#print axioms exp_gram_nonneg
end
end YangMills.PlaquetteTransfer
