-- SPDX-License-Identifier: Apache-2.0
import WilsonPlaquetteHilbert

/-! Construct the normalized Wilson transfer spectrum directly on spatial Haar L². -/
namespace YangMills.PlaquetteTransfer
open Filter MeasureTheory
open scoped Topology InnerProductSpace RealInnerProductSpace ENNReal
noncomputable section
variable {L : ℕ+}

abbrev mode (L : ℕ+) (β r : ℝ) := Module.End.eigenspace (hilbertTransfer L β).toLinearMap r

private theorem modeSum (L : ℕ+) (β : ℝ) :
    IsHilbertSum ℝ (fun r : ℝ => mode L β r) (fun r => (mode L β r).subtypeₗᵢ) := by
  letI (r : ℝ) : CompleteSpace (mode L β r) := (ContinuousLinearMap.isClosed_eigenspace (hilbertTransfer L β) r).completeSpace_coe
  apply IsHilbertSum.mkInternal _ (hilbertTransfer_symmetric β).orthogonalFamily_eigenspaces
  simp [← Submodule.orthogonal_orthogonal_eq_closure, wilson_eigenspaces_total]

def component (β : ℝ) (v : SliceHilbert L) (r : ℝ) : SliceHilbert L :=
  ((modeSum L β).linearIsometryEquiv v r : mode L β r)

set_option maxHeartbeats 1400000 in
theorem component_sum (β : ℝ) (v : SliceHilbert L) : HasSum (component β v) v := by
  let E := (modeSum L β).linearIsometryEquiv
  have h := (modeSum L β).hasSum_linearIsometryEquiv_symm (E v)
  rw [show (modeSum L β).linearIsometryEquiv.symm (E v) = v from E.symm_apply_apply v] at h
  exact h.congr_fun (fun _ => rfl)

theorem component_eigen (β : ℝ) (v : SliceHilbert L) (r : ℝ) :
    hilbertTransfer L β (component β v r) = r • component β v r :=
  Module.End.mem_eigenspace_iff.mp (((modeSum L β).linearIsometryEquiv v r).property)

private theorem component_inner (β : ℝ) (v : SliceHilbert L) (r : ℝ) :
    ⟪v, component β v r⟫_ℝ = ‖component β v r‖^2 := by
  rw [real_inner_comm]
  have h := (innerSL ℝ (component β v r)).hasSum (component_sum β v)
  change (innerSL ℝ (component β v r)) v = _
  rw [← h.tsum_eq, tsum_eq_single r]
  · exact real_inner_self_eq_norm_sq (component β v r)
  · intro s hs
    exact (hilbertTransfer_symmetric (L := L) β).orthogonalFamily_eigenspaces hs.symm
      ((modeSum L β).linearIsometryEquiv v r) ((modeSum L β).linearIsometryEquiv v s)

private theorem component_range (β : ℝ) (hβ : 0 < β) (v : SliceHilbert L) (r : ℝ) (hn : component β v r ≠ 0) :
    0 ≤ r ∧ r ≤ ‖hilbertTransfer L β‖ := by
  have he := component_eigen β v r
  have eig : Module.End.HasEigenvalue (hilbertTransfer L β).toLinearMap r :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr he,hn⟩
  have hp : 0 ≤ r := by
    rcases eq_or_ne r 0 with h | h
    · exact h.ge
    · exact (positive_eigenvalue β hβ r h eig).le
  have hle := (hilbertTransfer L β).le_opNorm (component β v r)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp] at hle
  exact ⟨hp, le_of_mul_le_mul_right hle (norm_pos_iff.mpr hn)⟩

abbrev normalizedHilbert (L : ℕ+) (β : ℝ) := ‖hilbertTransfer L β‖⁻¹ • hilbertTransfer L β

private theorem component_power (β : ℝ) (v : SliceHilbert L) (r : ℝ) (n : ℕ) :
    ((normalizedHilbert L β)^n) (component β v r) =
      (r / ‖hilbertTransfer L β‖)^n • component β v r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul]
    simp only [normalizedHilbert, smul_apply, component_eigen,
      smul_smul, pow_succ, div_eq_inv_mul]

theorem functional_moment (β : ℝ) (v : SliceHilbert L) (F : SliceHilbert L →L[ℝ] ℝ) (n : ℕ) :
    HasSum (fun r => (r / ‖hilbertTransfer L β‖)^n * F (component β v r))
      (F (((normalizedHilbert L β)^n) v)) := by
  have h := (F.comp (normalizedHilbert L β ^ n)).hasSum (component_sum β v)
  simpa only [ContinuousLinearMap.comp_apply, component_power, map_smul, smul_eq_mul] using h

private theorem top_component (β : ℝ) (Ω : WilsonVacuum L β) (v : SliceHilbert L) :
    component β v ‖hilbertTransfer L β‖ =
      ⟪embedSlice L Ω.ψ, v⟫_ℝ • embedSlice L Ω.ψ := by
  let t := ‖hilbertTransfer L β‖
  let ψ := embedSlice L Ω.ψ
  obtain ⟨c,hc⟩ := Ω.simple _ (component_eigen β v t)
  have hv : hilbertTransfer L β ψ = t • ψ := by
    change hilbertTransfer L β (embedSlice L Ω.ψ) = _
    rw [hilbertTransfer_embed, Ω.eigen, map_smul]
  have h := (innerSL ℝ ψ).hasSum (component_sum β v)
  have eq : ⟪ψ,v⟫_ℝ = c := by
    change (innerSL ℝ ψ) v = _
    rw [← h.tsum_eq, tsum_eq_single t]
    · rw [innerSL_apply_apply, hc, real_inner_smul_right, real_inner_self_eq_norm_sq,
          show ‖ψ‖ = 1 from Ω.normalized]
      ring
    · intro r hr
      exact (hilbertTransfer_symmetric β).orthogonalFamily_eigenspaces hr.symm
        ⟨ψ,Module.End.mem_eigenspace_iff.mpr hv⟩ _
  change component β v t = ⟪ψ,v⟫_ℝ • ψ
  rw [eq]
  exact hc

/-- Normalized powers select the physical vacuum against every bounded linear functional. -/
theorem powers_to_vacuum (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) (v : SliceHilbert L)
    (F : SliceHilbert L →L[ℝ] ℝ) :
    Tendsto (fun n : ℕ => F (((normalizedHilbert L β)^n) v)) atTop
      (𝓝 (⟪embedSlice L Ω.ψ, v⟫_ℝ * F (embedSlice L Ω.ψ))) := by
  let t := ‖hilbertTransfer L β‖
  have ht : 0 < t := (wilson_top_eigenvalue β hβ).1
  let b := fun r => F (component β v r)
  have hb := (F.hasSum (component_sum β v)).summable.abs
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (n : ℕ) r => (r/t)^n * b r) (g := fun r => if r=t then b t else 0) hb (by
      intro r
      by_cases he : r=t
      · subst r; simp [ht.ne']
      by_cases hz : component β v r = 0
      · simp [b,hz,he]
      obtain ⟨h₁,h₂⟩ := component_range β hβ v r hz
      simpa [he] using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg h₁ ht.le)
        ((div_lt_one ht).mpr (lt_of_le_of_ne h₂ he))).mul_const (b r)) (by
      filter_upwards with n r
      by_cases hz : component β v r = 0
      · simp [b,hz]
      obtain ⟨h₁,h₂⟩ := component_range β hβ v r hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (div_nonneg h₁ ht.le) _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (div_nonneg h₁ ht.le) ((div_le_one ht).mpr h₂)))
  rw [(hasSum_ite_eq t (b t)).tsum_eq] at hlim
  simpa only [b,t,(functional_moment β v F _).tsum_eq,top_component β Ω v,map_smul,smul_eq_mul] using hlim

abbrev physicalHilbert (L : ℕ+) :=
  ((physicalSlices L).map (embedSlice L).toLinearMap).topologicalClosure

/-- In the physical Hilbert space even a discontinuous null vector must vanish.
The Taylor-coefficient lower bounds extend by continuity; their polynomial
moments detect a vector against a dense set. -/
private theorem physical_kernel_trivial (β : ℝ) (hβ : 0 < β) (v : SliceHilbert L)
    (hv : v ∈ physicalHilbert L) (hz : hilbertTransfer L β v = 0) : v = 0 := by
  let J := embedSlice L
  let T := hilbertTransfer L β
  let a := amplitude (L := L) β
  let functional := ((innerSL ℝ v).comp J).comp (ContinuousLinearMap.mul ℝ _ a)
  have tests (n : ℕ) (w : Fin n → Feature L) : functional (word features w) = 0 := by
    let c := (n.factorial : ℝ)⁻¹ * β^n
    let z := J (a * word features w)
    let S := {u : SliceHilbert L | c * ⟪z,u⟫_ℝ^2 ≤ ⟪u,T u⟫_ℝ}
    have closed : IsClosed S := isClosed_le
      (continuous_const.mul ((continuous_const.inner continuous_id).pow 2))
      (continuous_id.inner T.continuous)
    have inside : (↑((physicalSlices L).map J.toLinearMap) : Set _) ⊆ S := by
      rintro _ ⟨f,hf,rfl⟩
      change c * ⟪J (a * word features w), J f⟫_ℝ^2 ≤ ⟪J f, hilbertTransfer L β (J f)⟫_ℝ
      rw [hilbertTransfer_embed, embed_inner, embed_inner]
      exact word_overlap_bound β hβ f hf n w
    have h : c * ⟪z,v⟫_ℝ ^ 2 ≤ ⟪v,T v⟫_ℝ := (closure_minimal inside closed) hv
    have ht : T v = 0 := hz
    rw [ht, inner_zero_right] at h
    have hc : 0 < c := mul_pos (by positivity) (pow_pos hβ n)
    change ⟪v,z⟫_ℝ = 0
    rw [real_inner_comm]
    exact sq_eq_zero_iff.mp (le_antisymm (nonpos_of_mul_nonpos_right h hc) (sq_nonneg _))
  have all (f : V (Slice L)) : ⟪v,J f⟫_ℝ = 0 := by
    let invA : V (Slice L) := ⟨fun x => (a x)⁻¹, a.continuous.inv₀ (fun _ => Real.exp_ne_zero _)⟩
    have prod : a * (invA * f) = f := by
      ext x
      change a x * ((a x)⁻¹ * f x) = f x
      rw [← mul_assoc, mul_inv_cancel₀ (show a x ≠ 0 from Real.exp_ne_zero _), one_mul]
    have h := zero_of_word_tests features features_separate functional tests (invA * f)
    change ⟪v,J (a*(invA*f))⟫_ℝ = 0 at h
    rwa [prod] at h
  have hd : DenseRange J := ContinuousMap.toLp_denseRange ℝ _ ℝ (by norm_num)
  have self : ⟪v,v⟫_ℝ = 0 := hd.induction_on (p := fun w => ⟪v,w⟫_ℝ = 0) v (isClosed_eq (continuous_const.inner continuous_id) continuous_const) all
  exact inner_self_eq_zero.mp self

private theorem physical_zero_component (β : ℝ) (hβ : 0 < β) (v : SliceHilbert L) (hv : v ∈ physicalHilbert L) :
    component β v 0 = 0 := by
  apply physical_kernel_trivial β hβ
  · have hn (r : ℝ) (hr : r ≠ 0) : component β v r ∈ physicalHilbert L := by
      obtain ⟨f,hf,hp,_⟩ := eigen_representative β r hr _ (component_eigen β v r)
      exact (((physicalSlices L).map (embedSlice L).toLinearMap).le_topologicalClosure ⟨f,hp,hf⟩)
    have hs := (component_sum β v).sub (hasSum_ite_eq 0 (component β v 0))
    have closed : IsClosed (physicalHilbert L : Set (SliceHilbert L)) :=
      ((physicalSlices L).map (embedSlice L).toLinearMap).isClosed_topologicalClosure
    have hsub : v - component β v 0 ∈ physicalHilbert L := by
      apply closed.mem_of_tendsto hs
      apply Filter.Eventually.of_forall
      intro s
      apply (physicalHilbert L).sum_mem
      intro r _
      by_cases hr : r = 0
      · subst r
        simp only [if_true,sub_self,Submodule.zero_mem]
      · simpa only [if_neg hr,sub_zero] using hn r hr
    have hd := (physicalHilbert L).sub_mem hv hsub
    rwa [sub_sub_cancel] at hd
  · simpa using component_eigen β v 0

def smoothing (L : ℕ+) (β : ℝ) := ‖hilbertTransfer L β‖⁻¹ • rowTransform (kernelRow L β)

theorem normalized_apply (β t : ℝ) (f : V (Slice L)) :
    wilsonOperator L β t f = t⁻¹ • wilsonOperator L β 1 f := by
  ext x
  change (∫ y, (kernel β _ x y / t) * f y ∂sliceLaw L) =
    t⁻¹ * ∫ y, (kernel β _ x y / 1) * f y ∂sliceLaw L
  simp_rw [div_one, div_eq_inv_mul, mul_assoc, integral_const_mul]

private theorem smooth_embed (β : ℝ) (f : V (Slice L)) :
    smoothing L β (embedSlice L f) = wilsonOperator L β ‖hilbertTransfer L β‖ f := by
  rw [normalized_apply]
  exact congrArg (‖hilbertTransfer L β‖⁻¹ • ·) (rowTransform_embed β f)

private theorem normalized_embed (β : ℝ) (f : V (Slice L)) (n : ℕ) :
    ((normalizedHilbert L β)^n) (embedSlice L f) =
      embedSlice L (((wilsonOperator L β ‖hilbertTransfer L β‖)^n) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, ih]
    change ‖hilbertTransfer L β‖⁻¹ • hilbertTransfer L β (embedSlice L _) = _
    rw [hilbertTransfer_embed, normalized_apply β ‖hilbertTransfer L β‖, map_smul]

private theorem normalized_ground (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) :
    wilsonOperator L β ‖hilbertTransfer L β‖ Ω.ψ = Ω.ψ := by
  rw [normalized_apply, Ω.eigen, inv_smul_smul₀ (wilson_top_eigenvalue β hβ).1.ne']

set_option maxHeartbeats 1800000 in
/-- Taking the long closing arc of the finite trace uses only the actual Wilson
operator. One smoothing step converts weak Hilbert convergence to convergence
of each diagonal evaluation. The spatial basepoint integral is dominated uniformly. -/
theorem wilson_cut_limit (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) (F : Op (Slice L)) :
    let t := ‖hilbertTransfer L β‖
    Tendsto (fun r : ℕ => cutTrace (sliceLaw L) (F.comp (wilsonOperator L β t ^ r)) (closingKernel L β t))
      atTop (𝓝 (pairing (sliceLaw L) Ω.ψ (F Ω.ψ))) := by
  intro t
  let A := wilsonOperator L β t
  let K := closingKernel L β t
  let S := normalizedHilbert L β
  let D := smoothing L β
  let J := embedSlice L
  let B := fun (n : ℕ) (x : Slice L) => F ((A^(n+1)) (K x)) x
  have identity (n : ℕ) (x : Slice L) : (A^(n+1)) (K x) = D ((S^n) (J (K x))) := by
    rw [pow_succ', mul_apply_eq_comp, normalized_embed, smooth_embed]
  have limit (x : Slice L) : Tendsto (fun n => B n x) atTop (𝓝 (Ω.ψ x * F Ω.ψ x)) := by
    let H : SliceHilbert L →L[ℝ] ℝ := ((ContinuousMap.evalCLM ℝ x).comp F).comp D
    have h := powers_to_vacuum β hβ Ω (J (K x)) H
    have hc : ⟪J Ω.ψ, J (K x)⟫_ℝ = Ω.ψ x := by
      rw [embed_inner]
      calc
        _ = (A Ω.ψ) x := by
          apply integral_congr_ae
          filter_upwards with y
          change Ω.ψ y * (kernel β _ y x / t) = (kernel β _ x y / t) * Ω.ψ y
          rw [kernel_symmetric β y x, mul_comm]
        _ = _ := DFunLike.congr_fun (normalized_ground β hβ Ω) x
    have hd : D (J Ω.ψ) = Ω.ψ := (smooth_embed β Ω.ψ).trans (normalized_ground β hβ Ω)
    change Tendsto (fun n => F (D ((S^n) (J (K x)))) x) atTop (𝓝 (⟪J Ω.ψ,J (K x)⟫_ℝ * F (D (J Ω.ψ)) x)) at h
    simpa only [B, identity, hc, hd] using h
  have hn (n : ℕ) : ‖S^n‖ ≤ 1 := by
    have hs : ‖S‖ ≤ 1 := by
      change ‖t⁻¹ • hilbertTransfer L β‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
    induction n with
    | zero => rw [pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_one₀ ih (norm_nonneg _) hs)
  apply (tendsto_add_atTop_iff_nat 1).mp
  change Tendsto (fun r => ∫ x, B r x ∂sliceLaw L) atTop (𝓝 (∫ x, Ω.ψ x * F Ω.ψ x ∂sliceLaw L))
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖ * (‖D‖ * (‖J‖ * ‖K‖)))
  · intro n
    exact (continuous_eval.comp ((F.continuous.comp ((A^(n+1)).continuous.comp K.continuous)).prodMk continuous_id)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards with x
    change ‖F ((A^(n+1)) (K x)) x‖ ≤ _
    rw [identity]
    apply ((F _).norm_coe_le_norm x).trans
    apply (F.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (D.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply ((S^n).le_opNorm _).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) (hn n)).trans ((J.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (K.norm_coe_le_norm _) (norm_nonneg _)))
  · exact .of_forall limit

private theorem vacuumPow (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) (d : ℕ) :
    ((wilsonOperator L β ‖hilbertTransfer L β‖)^d) Ω.ψ = Ω.ψ := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ',mul_apply_eq_comp,ih,normalized_ground β hβ Ω]

set_option maxHeartbeats 1200000 in
private theorem finite_trace_limit (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) (d : ℕ) :
    let a := observable L
    let v := embedSlice L (a * Ω.ψ)
    let m := ⟪embedSlice L Ω.ψ,v⟫_ℝ
    Tendsto (fun r => connected (N := extent d r) (wilsonMoment (L := L) β PeriodicWilson.su2Haar) d) atTop
      (𝓝 (⟪v, ((normalizedHilbert L β)^d) v⟫_ℝ - m^2)) := by
  intro a v m
  let t := ‖hilbertTransfer L β‖
  let A := wilsonOperator L β t
  let M := ContinuousLinearMap.mul ℝ (V (Slice L)) a
  have hz := wilson_cut_limit β hβ Ω (A^d)
  have hn : pairing (sliceLaw L) Ω.ψ Ω.ψ = 1 := by
    rw [← embed_inner, real_inner_self_eq_norm_sq, Ω.normalized, one_pow]
  rw [show (A^d) Ω.ψ = Ω.ψ from vacuumPow β hβ Ω d, hn] at hz
  have h := ((wilson_cut_limit β hβ Ω ((M.comp (A^d)).comp M)).div hz one_ne_zero).sub
    (((wilson_cut_limit β hβ Ω (M.comp (A^d))).div hz one_ne_zero).pow 2)
  have he : pairing (sliceLaw L) Ω.ψ (M ((A^d) (M Ω.ψ))) =
      pairing (sliceLaw L) (a * Ω.ψ) ((A^d) (a * Ω.ψ)) := by
    unfold pairing
    apply integral_congr_ae
    filter_upwards with x
    change Ω.ψ x * (a x * (((A^d) (a * Ω.ψ)) x)) = (a x * Ω.ψ x) * _
    ring
  simp only [ContinuousLinearMap.comp_apply, show (A^d) Ω.ψ = Ω.ψ from vacuumPow β hβ Ω d, div_one, he] at h
  simp_rw [connected_eq_ring, ringConnected_thermal β t (wilson_top_eigenvalue β hβ).1.ne']
  change Tendsto (thermal _ _ _ _ d) _ (𝓝 (⟪embedSlice L (a*Ω.ψ), (normalizedHilbert L β ^ d) (embedSlice L (a*Ω.ψ))⟫_ℝ -
    ⟪embedSlice L Ω.ψ, embedSlice L (a*Ω.ψ)⟫_ℝ^2))
  rw [normalized_embed, embed_inner, embed_inner]
  exact h

def modeWeight (β : ℝ) (v : SliceHilbert L) (r : ℝ) := ‖component β v r‖^2

private theorem mode_moments (β : ℝ) (v : SliceHilbert L) (d : ℕ) :
    HasSum (fun r => modeWeight β v r * (r/‖hilbertTransfer L β‖)^d) ⟪v,((normalizedHilbert L β)^d) v⟫_ℝ := by
  apply (functional_moment β v (innerSL ℝ v) d).congr_fun
  intro r
  rw [innerSL_apply_apply, component_inner]
  exact mul_comm _ _

private theorem weights_summable (β : ℝ) (v : SliceHilbert L) : Summable (modeWeight β v) := by
  simpa using (mode_moments β v 0).summable

private abbrev Occupied (β : ℝ) (v : SliceHilbert L) := Function.support (modeWeight β v)

private instance (β : ℝ) (v : SliceHilbert L) : Countable (Occupied β v) :=
  (weights_summable β v).countable_support.to_subtype

/-- Positive spectral measure of a specified vector on the spatial Haar Hilbert space.
The transfer eigenvalue is divided by the vacuum eigenvalue before taking its logarithm. -/
def latticeEnergyMeasure (β : ℝ) (v : SliceHilbert L) : Measure ℝ :=
  Measure.sum fun r : Occupied β v => ENNReal.ofReal (modeWeight β v r) •
    Measure.dirac (-Real.log (r.val/‖hilbertTransfer L β‖))

private theorem occupied_range (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) (v : SliceHilbert L)
    (hphys : v ∈ physicalHilbert L) (horth : ⟪embedSlice L Ω.ψ,v⟫_ℝ = 0) (r : Occupied β v) :
    0 < r.val ∧ r.val < ‖hilbertTransfer L β‖ := by
  have hn : component β v r ≠ 0 := by
    intro h
    exact r.property (by simp [modeWeight,h])
  have hr := component_range β hβ v r hn
  refine ⟨lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_⟩
  · intro he
    exact hn (he ▸ physical_zero_component β hβ v hphys)
  · intro he
    apply hn
    rw [he,top_component β Ω,horth,zero_smul]

theorem lattice_energy_moments (β : ℝ) (hβ : 0 < β) (Ω : WilsonVacuum L β) (v : SliceHilbert L)
    (hphys : v ∈ physicalHilbert L) (horth : ⟪embedSlice L Ω.ψ,v⟫_ℝ = 0) (d : ℕ) :
    IsFiniteMeasure (latticeEnergyMeasure β v) ∧ latticeEnergyMeasure β v (Set.Iic 0) = 0 ∧
      (∫ E, Real.exp (-(d:ℝ)*E) ∂latticeEnergyMeasure β v) = ⟪v,((normalizedHilbert L β)^d) v⟫_ℝ := by
  let t := ‖hilbertTransfer L β‖
  have ht : 0 < t := (wilson_top_eigenvalue β hβ).1
  have hp (r : Occupied β v) := occupied_range β hβ Ω v hphys horth r
  have hw (r : ℝ) : 0 ≤ modeWeight β v r := sq_nonneg _
  refine ⟨⟨?_⟩,?_,?_⟩
  · simp [latticeEnergyMeasure, Measure.sum_apply,
      ← ENNReal.ofReal_tsum_of_nonneg (fun r : Occupied β v => hw r) ((weights_summable β v).subtype _)]
  · rw [latticeEnergyMeasure, Measure.sum_apply _ measurableSet_Iic]
    apply ENNReal.tsum_eq_zero.mpr
    intro r
    have e := neg_pos.mpr (Real.log_neg (div_pos (hp r).1 ht) ((div_lt_one ht).mpr (hp r).2))
    simp [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic]
    exact Or.inr (neg_pos.mp e)
  · rw [latticeEnergyMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
    have he (r : Occupied β v) : Real.exp (-(d:ℝ) * -Real.log (r.val / ‖hilbertTransfer L β‖)) =
        (r.val / ‖hilbertTransfer L β‖)^d := by
      rw [neg_mul_neg,Real.exp_nat_mul,Real.exp_log (div_pos (hp r).1 ht)]
    simp only [ENNReal.toReal_ofReal (hw _), he, smul_eq_mul]
    rw [← (mode_moments β v d).tsum_eq]
    refine tsum_subtype_eq_of_support_subset (s := Function.support (modeWeight β v))
      (f := fun r : ℝ => modeWeight β v r * (r/‖hilbertTransfer L β‖)^d) ?_
    intro r hr hz
    exact hr (by simp [show modeWeight β v r = 0 from hz])

/-- The measured observable, centered with its vacuum expectation at infinite extent. -/
def plaquetteVector (Ω : WilsonVacuum L β) : SliceHilbert L :=
  let p := embedSlice L Ω.ψ
  let v := embedSlice L (observable L * Ω.ψ)
  v - ⟪p,v⟫_ℝ • p

set_option maxHeartbeats 1200000 in
theorem wilson_plaquette_spectral_measure (β : ℝ) (hβ : 0 < β) (d : ℕ) :
    let Ω := ground L β hβ
    let ν := latticeEnergyMeasure β (plaquetteVector Ω)
    IsFiniteMeasure ν ∧ ν (Set.Iic 0) = 0 ∧
      Tendsto (fun r => connected (N := extent d r) (wilsonMoment (L := L) β PeriodicWilson.su2Haar) d)
        atTop (𝓝 (∫ E, Real.exp (-(d:ℝ)*E) ∂ν)) := by
  intro Ω ν
  let J := embedSlice L
  let p := J Ω.ψ
  let f := observable L * Ω.ψ
  let v := J f
  let m := ⟪p,v⟫_ℝ
  let z := plaquetteVector Ω
  have hz : z = v - m • p := rfl
  have hp : ⟪p,p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,show ‖p‖ = 1 from Ω.normalized, one_pow]
  have orth : ⟪p,z⟫_ℝ = 0 := by rw [hz,inner_sub_right,real_inner_smul_right,hp,mul_one,sub_self]
  have phy : z ∈ physicalHilbert L := by
    apply ((physicalSlices L).map J.toLinearMap).le_topologicalClosure
    refine ⟨f - m • Ω.ψ, (physicalSlices L).sub_mem (observable_preserves_physical Ω.physical)
      ((physicalSlices L).smul_mem m Ω.physical), ?_⟩
    change J (f - m • Ω.ψ) = v - m • p
    rw [map_sub,map_smul]
  obtain ⟨fin,supp,moment⟩ := lattice_energy_moments β hβ Ω z phy orth d
  refine ⟨fin,supp,?_⟩
  let S := normalizedHilbert L β
  have hpow : (S^d) p = p := by
    change (normalizedHilbert L β ^ d) (embedSlice L Ω.ψ) = _
    rw [normalized_embed, vacuumPow β hβ Ω]
  have hsym : S.IsSymmetric := by
    intro u w
    change ⟪‖hilbertTransfer L β‖⁻¹ • hilbertTransfer L β u,w⟫_ℝ = ⟪u,‖hilbertTransfer L β‖⁻¹ • hilbertTransfer L β w⟫_ℝ
    rw [real_inner_smul_left,real_inner_smul_right]
    exact congrArg (‖hilbertTransfer L β‖⁻¹ * ·) (hilbertTransfer_symmetric β u w)
  have hSp : S p = p := by
    have he := normalized_embed β Ω.ψ 1
    simpa only [pow_one,normalized_ground β hβ Ω] using he
  have left (n : ℕ) : ⟪p,(S^n) v⟫_ℝ = m := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',mul_apply_eq_comp]
      have e : ⟪S p,(S^n) v⟫_ℝ = ⟪p,S ((S^n) v)⟫_ℝ := hsym _ _
      rw [← e,hSp,ih]
  have hL := left d
  have hR : ⟪v,p⟫_ℝ = m := real_inner_comm _ _
  have eq : ⟪z,(S^d) z⟫_ℝ = ⟪v,(S^d) v⟫_ℝ - m^2 := by
    rw [hz,map_sub,map_smul,hpow]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hp,hL,hR]
    ring
  have lim := finite_trace_limit β hβ Ω d
  change Tendsto _ _ (𝓝 (∫ E, Real.exp (-(d:ℝ)*E) ∂latticeEnergyMeasure β z))
  rw [moment, eq]
  exact lim

#print axioms wilson_plaquette_spectral_measure
#print axioms lattice_energy_moments
#print axioms wilson_cut_limit
#print axioms powers_to_vacuum
end
end YangMills.PlaquetteTransfer
