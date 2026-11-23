-- SPDX-License-Identifier: Apache-2.0
import WilsonPlaquettePositivity

/-! The Wilson integral operator on the actual spatial Haar Hilbert space.
Compactness comes from uniform equicontinuity of the images of its unit ball. -/
namespace YangMills.PlaquetteTransfer
open MeasureTheory Filter
open scoped Topology InnerProductSpace RealInnerProductSpace
noncomputable section
variable {L : ℕ+}

abbrev SliceHilbert (L : ℕ+) := Lp ℝ 2 (sliceLaw L)
abbrev embedSlice (L : ℕ+) := ContinuousMap.toLp (E := ℝ) 2 (sliceLaw L) ℝ

def kernelRow (L : ℕ+) (β : ℝ) : C(Slice L, SliceHilbert L) :=
  ⟨fun x => embedSlice L ((normalizedKernel L β 1).curry x),
    (embedSlice L).continuous.comp (normalizedKernel L β 1).curry.continuous⟩

def rowTransform {X H : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (row : C(X,H)) : H →L[ℝ] V X :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun x => ⟪row x, f⟫_ℝ, row.continuous.inner continuous_const⟩
      map_add' := fun f g => ContinuousMap.ext fun x => inner_add_right _ _ _
      map_smul' := fun r f => ContinuousMap.ext fun x => real_inner_smul_right _ _ _ }
    ‖row‖ (by
      intro f
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (row.norm_coe_le_norm x) (norm_nonneg _)))

private theorem rowTransform_compact {X H : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (row : C(X,H)) : IsCompactOperator (rowTransform row) := by
  let F := rowTransform row
  let e := (ContinuousMap.isometryEquivBoundedOfCompact X ℝ).toHomeomorph
  let A := (e ∘ F) '' Metric.closedBall 0 1
  have point (f : BoundedContinuousFunction X ℝ) (x : X) (hf : f ∈ A) : f x ∈ Metric.closedBall 0 ‖row‖ := by
    obtain ⟨v,hv,rfl⟩ := hf
    have hv' : ‖v‖ ≤ 1 := by simpa using hv
    change dist ⟪row x, v⟫_ℝ 0 ≤ _
    rw [dist_zero_right]
    exact (norm_inner_le_norm _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hv').trans (row.norm_coe_le_norm _))
  have eqc : Equicontinuous ((↑) : A → X → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have nh := (Metric.continuousAt_iff'.mp (row.continuous.continuousAt (x := x))) ε hε
    filter_upwards [nh] with y hy
    rintro ⟨_,v,hv,rfl⟩
    have hv' : ‖v‖ ≤ 1 := by simpa using hv
    change dist ⟪row x, v⟫_ℝ ⟪row y, v⟫_ℝ < ε
    rw [dist_eq_norm, ← inner_sub_left]
    exact ((norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hv')).trans_lt
      (by simpa [← dist_eq_norm, dist_comm] using hy)
  have compact := BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall (0 : ℝ) ‖row‖) A point eqc
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall F.toLinearMap zero_lt_one).mpr
  have hA : A = e '' (F '' Metric.closedBall 0 1) := Set.image_comp e F _
  rw [hA, ← e.image_closure] at compact
  exact e.isCompact_image.mp compact

def hilbertTransfer (L : ℕ+) (β : ℝ) : SliceHilbert L →L[ℝ] SliceHilbert L :=
  (embedSlice L).comp (rowTransform (kernelRow L β))

theorem hilbertTransfer_compact (β : ℝ) : IsCompactOperator (hilbertTransfer L β) :=
  (rowTransform_compact (kernelRow L β)).clm_comp (embedSlice L)

theorem rowTransform_embed (β : ℝ) (g : V (Slice L)) :
    rowTransform (kernelRow L β) (embedSlice L g) = wilsonOperator L β 1 g := by
  ext x
  change ⟪embedSlice L ((normalizedKernel L β 1).curry x), embedSlice L g⟫_ℝ =
    ∫ y, normalizedKernel L β 1 (x,y) * g y ∂sliceLaw L
  rw [ContinuousMap.inner_toLp]
  simp [mul_comm]

theorem hilbertTransfer_embed (β : ℝ) (g : V (Slice L)) :
    hilbertTransfer L β (embedSlice L g) = embedSlice L (wilsonOperator L β 1 g) :=
  congrArg (embedSlice L) (rowTransform_embed β g)

theorem embed_inner (f g : V (Slice L)) :
    ⟪embedSlice L f, embedSlice L g⟫_ℝ = pairing (sliceLaw L) f g := by
  rw [ContinuousMap.inner_toLp]
  simp [pairing, mul_comm]

theorem hilbertTransfer_symmetric (β : ℝ) : (hilbertTransfer L β).IsSymmetric := by
  let J := embedSlice L
  let T := hilbertTransfer L β
  have hd : DenseRange J := ContinuousMap.toLp_denseRange ℝ _ ℝ (by norm_num)
  intro v w
  refine hd.induction_on v (isClosed_eq ((T.continuous).inner continuous_const)
    (continuous_id.inner continuous_const)) ?_
  intro f
  refine hd.induction_on w (isClosed_eq (continuous_const.inner continuous_id)
    (continuous_const.inner T.continuous)) ?_
  intro g
  change ⟪hilbertTransfer L β (embedSlice L f), embedSlice L g⟫_ℝ =
    ⟪embedSlice L f, hilbertTransfer L β (embedSlice L g)⟫_ℝ
  simp only [hilbertTransfer_embed, embed_inner, operator_symmetric]

/-- The actual compact self-adjoint Wilson operator admits a total family of
eigenspaces on the spatial Haar L² space, including its gauge null space. -/
theorem wilson_eigenspaces_total (β : ℝ) :
    (⨆ r : ℝ, Module.End.eigenspace (hilbertTransfer L β).toLinearMap r)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (hilbertTransfer_compact β) (hilbertTransfer_symmetric β)

/-- Every state at nonzero transfer eigenvalue has a continuous physical representative. -/
theorem eigen_representative (β r : ℝ) (hr : r ≠ 0) (v : SliceHilbert L)
    (hv : hilbertTransfer L β v = r • v) :
    ∃ f : V (Slice L), embedSlice L f = v ∧ f ∈ physicalSlices L ∧ wilsonOperator L β 1 f = r • f := by
  let f := r⁻¹ • rowTransform (kernelRow L β) v
  have id : embedSlice L f = v := by
    change embedSlice L (r⁻¹ • rowTransform (kernelRow L β) v) = v
    rw [map_smul]
    change r⁻¹ • hilbertTransfer L β v = v
    rw [hv, inv_smul_smul₀ hr]
  have eig : wilsonOperator L β 1 f = r • f := by
    apply ContinuousMap.toLp_injective (sliceLaw L) (p := 2) (𝕜 := ℝ)
    change embedSlice L (wilsonOperator L β 1 f) = embedSlice L (r • f)
    calc
      _ = hilbertTransfer L β (embedSlice L f) := (hilbertTransfer_embed β f).symm
      _ = r • embedSlice L f := by rw [id, hv]
      _ = _ := ((embedSlice L).map_smul r f).symm
  refine ⟨f, id, ?_, eig⟩
  have hf := (physicalSlices L).smul_mem r⁻¹ (operator_physical β 1 f)
  simpa only [eig, inv_smul_smul₀ hr] using hf

theorem positive_eigenvalue (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : r ≠ 0)
    (h : Module.End.HasEigenvalue (hilbertTransfer L β).toLinearMap r) : 0 < r := by
  obtain ⟨v,hv⟩ := h.exists_hasEigenvector
  obtain ⟨f,hf,hp,he⟩ := eigen_representative β r hr v hv.apply_eq_smul
  have hn : f ≠ 0 := fun hz => hv.2 (by rw [← hf, hz, map_zero])
  have hq := wilson_quadratic_pos β hβ f hp hn
  rw [he] at hq
  have hscalar : pairing (sliceLaw L) f (r • f) = r * pairing (sliceLaw L) f f := by
    unfold pairing
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (f _) r, integral_const_mul]
  rw [hscalar] at hq
  exact pos_of_mul_pos_left hq (integral_nonneg fun x => mul_self_nonneg (f x))

private theorem hilbertTransfer_ne_zero (β : ℝ) (hβ : 0 < β) : hilbertTransfer L β ≠ 0 := by
  intro hz
  have he := hilbertTransfer_embed (L := L) β (1 : V (Slice L))
  simp only [hz, zero_apply] at he
  have hn : wilsonOperator L β 1 1 = 0 :=
    ContinuousMap.toLp_injective (sliceLaw L) (p := 2) (𝕜 := ℝ) (he.symm.trans (map_zero _).symm)
  have hp := wilson_quadratic_pos β hβ (1 : V (Slice L)) (by intro g U; rfl) one_ne_zero
  simp [hn, pairing] at hp

/-- The norm is a strictly positive transfer eigenvalue of the actual compact operator. -/
theorem wilson_top_eigenvalue (β : ℝ) (hβ : 0 < β) :
    0 < ‖hilbertTransfer L β‖ ∧ Module.End.HasEigenvalue (hilbertTransfer L β).toLinearMap ‖hilbertTransfer L β‖ := by
  let T := hilbertTransfer L β
  have hT : T ≠ 0 := hilbertTransfer_ne_zero β hβ
  have hp : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hc := hilbertTransfer_compact (L := L) β
  have hs := hilbertTransfer_symmetric (L := L) β
  have hex : ∃ r : ℝ, Module.End.HasEigenvalue T.toLinearMap r ∧ r ≠ 0 := by
    by_contra! h
    exact hT ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hc hs).mp h)
  obtain ⟨r,hr,hz⟩ := hex
  have nonempty : (spectrum ℝ T).Nonempty := ⟨r, (hc.hasEigenvalue_iff_mem_spectrum hz).mp hr⟩
  obtain ⟨q,hq,eq⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty nonempty
  rw [T.spectralRadius_eq_nnnorm hs.isSelfAdjoint] at eq
  have hab : |q| = ‖T‖ := by simpa [Real.norm_eq_abs] using congrArg ENNReal.toReal eq
  have hq0 : q ≠ 0 := by intro he; rw [he, abs_zero] at hab; exact hp.ne hab
  have eigen := (hc.hasEigenvalue_iff_mem_spectrum hq0).mpr hq
  have hqpos := positive_eigenvalue β hβ q hq0 eigen
  rw [abs_of_pos hqpos] at hab
  exact ⟨hp, hab ▸ eigen⟩

private def absFun (f : V (Slice L)) : V (Slice L) := ⟨fun x => |f x|, f.continuous.abs⟩

theorem positivity_improving (β : ℝ) (f : V (Slice L)) (hn : f ≠ 0) (hf : ∀ x, 0 ≤ f x) (x : Slice L) :
    0 < wilsonOperator L β 1 f x := by
  let K := normalizedKernel L β 1
  obtain ⟨y,hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra! h
    exact hn (ContinuousMap.ext h)
  have hk (y : Slice L) : 0 < K (x,y) := by simpa [K,normalizedKernel] using kernel_pos β x y
  have hc : Continuous (fun y => K (x,y) * f y) := ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul f.continuous)
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := sliceLaw L) (HasCompactSupport.of_compactSpace _)
    (fun y => mul_nonneg (hk y).le (hf y)) (mul_ne_zero (hk y).ne' hy)

private theorem abs_top_eigen (β : ℝ) (f : V (Slice L))
    (he : wilsonOperator L β 1 f = ‖hilbertTransfer L β‖ • f) :
    wilsonOperator L β 1 (absFun f) = ‖hilbertTransfer L β‖ • absFun f := by
  let T := hilbertTransfer L β
  let J := embedSlice L
  let A := wilsonOperator L β 1
  let g := absFun f
  let radius := ‖T‖
  have hl : 0 ≤ radius := norm_nonneg _
  have hpos (x) : 0 ≤ (radius • g) x := mul_nonneg hl (abs_nonneg _)
  have hle (x) : (radius • g) x ≤ A g x := by
    let K := normalizedKernel L β 1
    have hp (y : Slice L) : 0 < K (x,y) := by simpa [K, normalizedKernel] using kernel_pos β x y
    change radius * |f x| ≤ _
    rw [← abs_of_nonneg hl, ← abs_mul, ← show (A f) x = radius * f x from DFunLike.congr_fun he x]
    have hi := norm_integral_le_integral_norm (μ := sliceLaw L) (fun y => K (x,y) * f y)
    change |∫ y, K (x,y) * f y ∂sliceLaw L| ≤ ∫ y, K (x,y) * |f y| ∂sliceLaw L
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (hp _)] using hi
  have hn : ‖J (A g)‖ ≤ ‖J (radius • g)‖ := by
    rw [J.map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl]
    exact (hilbertTransfer_embed β g) ▸ T.le_opNorm (J g)
  have hi : ⟪J (A g), J (radius • g)⟫_ℝ = ‖J (radius • g)‖ ^ 2 := by
    apply le_antisymm
    · exact (real_inner_le_norm _ _).trans (by rw [sq]; exact mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    · rw [← real_inner_self_eq_norm_sq, embed_inner, embed_inner]
      apply integral_mono
      · exact ((radius • g).continuous.mul (radius • g).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact ((A g).continuous.mul (radius • g).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact fun x => mul_le_mul_of_nonneg_right (hle x) (hpos x)
  exact ContinuousMap.toLp_injective (sliceLaw L) (p := 2) (𝕜 := ℝ) (eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) hn hi)

/-- A top eigenfunction which vanishes even at a single configuration is zero. -/
theorem top_no_node (β : ℝ) (f : V (Slice L)) (hn : f ≠ 0)
    (he : wilsonOperator L β 1 f = ‖hilbertTransfer L β‖ • f) (x : Slice L) : f x ≠ 0 := by
  have hg : absFun f ≠ 0 := by
    intro h
    apply hn
    ext y
    exact abs_eq_zero.mp (DFunLike.congr_fun h y)
  have hpos := positivity_improving β (absFun f) hg (fun _ => abs_nonneg _) x
  rw [abs_top_eigen β f he] at hpos
  change 0 < ‖hilbertTransfer L β‖ * |f x| at hpos
  intro hx
  simp [hx] at hpos

structure WilsonVacuum (L : ℕ+) (β : ℝ) where
  ψ : V (Slice L)
  positive : ∀ x, 0 < ψ x
  normalized : ‖embedSlice L ψ‖ = 1
  eigen : wilsonOperator L β 1 ψ = ‖hilbertTransfer L β‖ • ψ
  physical : ψ ∈ physicalSlices L
  simple : ∀ v : SliceHilbert L, hilbertTransfer L β v = ‖hilbertTransfer L β‖ • v →
    ∃ c : ℝ, v = c • embedSlice L ψ

set_option maxHeartbeats 1300000 in
theorem vacuum_exists (β : ℝ) (hβ : 0 < β) : Nonempty (WilsonVacuum L β) := by
  let T := hilbertTransfer L β
  let J := embedSlice L
  obtain ⟨hr,hev⟩ := wilson_top_eigenvalue (L := L) β hβ
  obtain ⟨v,hv⟩ := hev.exists_hasEigenvector
  obtain ⟨f,hf,hphy,he⟩ := eigen_representative β ‖T‖ hr.ne' v hv.apply_eq_smul
  have hn : f ≠ 0 := fun hz => hv.2 (by rw [← hf,hz,map_zero])
  let g := absFun f
  have hpos (x) : 0 < g x := abs_pos.mpr (top_no_node β f hn he x)
  have hg : g ≠ 0 := by
    intro hz
    exact (hpos 1).ne' (DFunLike.congr_fun hz 1)
  have hgn : 0 < ‖J g‖ := norm_pos_iff.mpr fun hz =>
    hg (ContinuousMap.toLp_injective (sliceLaw L) (p := 2) (𝕜 := ℝ) (hz.trans (map_zero J).symm))
  let ψ := ‖J g‖⁻¹ • g
  have hψ (x) : 0 < ψ x := mul_pos (inv_pos.mpr hgn) (hpos x)
  have eig : wilsonOperator L β 1 ψ = ‖T‖ • ψ := by
    change wilsonOperator L β 1 (‖J g‖⁻¹ • g) = ‖T‖ • ‖J g‖⁻¹ • g
    rw [map_smul, show wilsonOperator L β 1 g = ‖T‖ • g from abs_top_eigen β f he]
    exact smul_comm _ _ _
  have phys : ψ ∈ physicalSlices L := by
    have hp := (physicalSlices L).smul_mem ‖T‖⁻¹ (operator_physical β 1 ψ)
    rw [eig, inv_smul_smul₀ (show ‖T‖ ≠ 0 from hr.ne')] at hp
    exact hp
  refine ⟨⟨ψ,hψ,?_,eig,phys,?_⟩⟩
  · change ‖J (‖J g‖⁻¹ • g)‖ = 1
    rw [J.map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgn), inv_mul_cancel₀ hgn.ne']
  · intro w hw
    obtain ⟨a,ha,_,hea⟩ := eigen_representative β ‖T‖ hr.ne' w hw
    let c := a 1 / ψ 1
    let b := a - c • ψ
    have zero : b 1 = 0 := by
      change a 1 - (a 1 / ψ 1) * ψ 1 = 0
      rw [div_mul_cancel₀ _ (hψ 1).ne', sub_self]
    have eqe : wilsonOperator L β 1 b = ‖T‖ • b := by
      change wilsonOperator L β 1 (a - c • ψ) = ‖T‖ • (a - c • ψ)
      rw [map_sub, map_smul, hea, eig, smul_sub, smul_comm c ‖T‖ ψ]
    have hb : b = 0 := by by_contra hn; exact top_no_node β b hn eqe 1 zero
    have haψ : a = c • ψ := sub_eq_zero.mp hb
    exact ⟨c, by rw [← ha, haψ, map_smul]⟩

noncomputable def ground (L : ℕ+) (β : ℝ) (hβ : 0 < β) : WilsonVacuum L β :=
  Classical.choice (vacuum_exists β hβ)

#print axioms vacuum_exists
#print axioms top_no_node
#print axioms wilson_top_eigenvalue
#print axioms hilbertTransfer_compact
#print axioms hilbertTransfer_symmetric
#print axioms wilson_eigenspaces_total
end
end YangMills.PlaquetteTransfer
