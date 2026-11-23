-- SPDX-License-Identifier: Apache-2.0
import WilsonPlaquetteHilbert

/-! The finite Wilson trace on the spatial Haar Hilbert space. Parseval and
dominated convergence identify the closed kernel integral with the sum of the
basis diagonal after two bonds on an unmarked arc are cut. -/
namespace YangMills.PlaquetteTransfer
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
noncomputable section
variable {X H ι : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Parseval identifies a smoothed diagonal integral with the absolutely
summable diagonal of the corresponding Hilbert operator in every countable basis. -/
theorem diagonal_basis_sum [Countable ι] (μ : Measure X) [IsProbabilityMeasure μ]
    (row : C(X,H)) (G : H →L[ℝ] V X) (b : HilbertBasis ι ℝ H) :
    HasSum (fun i => pairing μ (rowTransform row (b i)) (G (b i)))
      (∫ x, G (row x) x ∂μ) := by
  classical
  let f (i : ι) (x : X) := ⟪b i, row x⟫_ℝ * G (b i) x
  have cont (i : ι) : Continuous (f i) := (continuous_const.inner row.continuous).mul (G (b i)).continuous
  have integ (i : ι) := (cont i).integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have lim (x : X) : HasSum (fun i => f i x) (G (row x) x) := by
    have h := (b.hasSum_repr (row x)).mapL ((ContinuousMap.evalCLM ℝ x).comp G)
    simpa only [ContinuousLinearMap.comp_apply, map_smul, ContinuousMap.evalCLM_apply,
      b.repr_apply_apply, ContinuousMap.smul_apply, smul_eq_mul, f] using h
  have bound (s : Finset ι) (x : X) : ‖∑ i ∈ s, f i x‖ ≤ ‖row‖^2 + ‖G‖^2 := by
    let F := (ContinuousMap.evalCLM ℝ x).comp G
    let z := (InnerProductSpace.toDual ℝ H).symm F
    have hz : ‖z‖ ≤ ‖G‖ := by
      change ‖(InnerProductSpace.toDual ℝ H).symm F‖ ≤ _
      rw [LinearIsometryEquiv.norm_map]
      exact ContinuousLinearMap.opNorm_le_bound F G.opNorm_nonneg (fun v =>
        ((G v).norm_coe_le_norm x).trans (G.le_opNorm v))
    have eval (i : ι) : G (b i) x = ⟪b i,z⟫_ℝ := by
      rw [real_inner_comm]; exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := F) (x := b i)).symm
    calc
      _ ≤ ∑ i ∈ s, ‖f i x‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, (‖⟪b i,row x⟫_ℝ‖^2 + ‖⟪b i,z⟫_ℝ‖^2) := by
        apply Finset.sum_le_sum
        intro i _
        change ‖⟪b i,row x⟫_ℝ * G (b i) x‖ ≤ _
        rw [eval,norm_mul]
        nlinarith [sq_nonneg (‖⟪b i,row x⟫_ℝ‖ - ‖⟪b i,z⟫_ℝ‖),
          sq_nonneg ‖⟪b i,row x⟫_ℝ‖,sq_nonneg ‖⟪b i,z⟫_ℝ‖]
      _ ≤ ‖row x‖^2 + ‖z‖^2 := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (b.orthonormal.sum_inner_products_le _) (b.orthonormal.sum_inner_products_le _)
      _ ≤ _ := by gcongr; exact row.norm_coe_le_norm x
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := (atTop : Filter (Finset ι)))
    (F := fun s x => ∑ i ∈ s, f i x) (f := fun x => G (row x) x) (fun _ => ‖row‖^2+‖G‖^2)
    (.of_forall fun s => (continuous_finsetSum _ (fun i _ => cont i)).aestronglyMeasurable)
    (.of_forall fun s => .of_forall (bound s)) (integrable_const _) (.of_forall lim)
  have ident (i : ι) : ∫ x, f i x ∂μ = pairing μ (rowTransform row (b i)) (G (b i)) := by
    unfold pairing
    apply integral_congr_ae
    filter_upwards with x
    change ⟪b i,row x⟫_ℝ * _ = ⟪row x,b i⟫_ℝ * _
    rw [real_inner_comm (b i)]
  simp_rw [integral_finsetSum _ fun i _ => integ i,ident] at h
  exact h

variable {L : ℕ+}

/-- Cut two bonds on the longer arc of the circle. On the Haar Hilbert
space this bounded operator has an absolutely summable basis diagonal. -/
def cutHilbertOperator (β : ℝ) (F : Op (Slice L)) (r : ℕ) : SliceHilbert L →L[ℝ] SliceHilbert L :=
  let T := wilsonOperator L β 1
  let D := rowTransform (kernelRow L β)
  (hilbertTransfer L β).comp ((embedSlice L).comp (F.comp ((T^r).comp D)))

private theorem basis_countable (b : HilbertBasis ι ℝ (SliceHilbert L)) : Countable ι := by
  letI : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have h : Pairwise fun i j => Disjoint (Metric.ball (b i) (1/2)) (Metric.ball (b j) (1/2)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have sq := norm_sub_sq_real (b i) (b j)
    rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one,b.orthonormal.inner_eq_zero hij] at sq
    nlinarith [norm_nonneg (b i-b j)]
  exact h.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i,Metric.mem_ball_self (by norm_num)⟩)

theorem wilson_cut_basis (β : ℝ) (F : Op (Slice L)) (r : ℕ)
    (b : HilbertBasis ι ℝ (SliceHilbert L)) :
    HasSum (fun i => ⟪b i,cutHilbertOperator β F r (b i)⟫_ℝ)
      (cutTrace (sliceLaw L) (F.comp ((wilsonOperator L β 1)^(r+1))) (closingKernel L β 1)) := by
  haveI := basis_countable b
  let T := wilsonOperator L β 1
  let D := rowTransform (kernelRow L β)
  let J := embedSlice L
  let B := F.comp ((T^r).comp D)
  have h := diagonal_basis_sum (sliceLaw L) (kernelRow L β) B b
  have hrow (x : Slice L) : kernelRow L β x = J (closingKernel L β 1 x) := by
    apply congrArg (J : V (Slice L) → SliceHilbert L)
    ext y
    exact congrArg (· / 1) (kernel_symmetric β x y)
  have value (x : Slice L) : B (kernelRow L β x) x = F ((T^(r+1)) (closingKernel L β 1 x)) x := by
    rw [hrow,pow_succ,mul_apply_eq_comp]
    change F ((T^r) (D (J _))) x = F ((T^r) (T _)) x
    rw [show ∀ f, D (J f) = T f from rowTransform_embed β]
  have term (i : ι) : pairing (sliceLaw L) (D (b i)) (B (b i)) =
      ⟪b i,cutHilbertOperator β F r (b i)⟫_ℝ := by
    rw [← embed_inner]
    exact hilbertTransfer_symmetric β (b i) (J (B (b i)))
  change HasSum (fun i => ⟪b i,cutHilbertOperator β F r (b i)⟫_ℝ)
    (∫ x, F ((T^(r+1)) (closingKernel L β 1 x)) x ∂sliceLaw L)
  simpa only [← term,← value] using h

/-- Bounded multiplication by a continuous spatial slice function on Haar L². -/
def hilbertMultiplier (a : V (Slice L)) : SliceHilbert L →L[ℝ] SliceHilbert L :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (sliceLaw L) ⊤ 2 2 (ContinuousMap.toLp ⊤ (sliceLaw L) ℝ a)

theorem hilbertMultiplier_embed (a f : V (Slice L)) :
    hilbertMultiplier a (embedSlice L f) = embedSlice L (a*f) := by
  let μ := sliceLaw L
  let J := embedSlice L
  let A := ContinuousMap.toLp ⊤ μ ℝ a
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) A (J f),
    ContinuousMap.coeFn_toLp (p := ⊤) μ (𝕜 := ℝ) a, ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℝ) f,
    ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℝ) (a*f)] with x h ha hf haf
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2 A (J f)) x = _
  rw [h,haf]
  change A x * J f x = a x * f x
  rw [show A x = a x from ha, show J f x = f x from hf]

@[simp] theorem hilbertMultiplier_one (v : SliceHilbert L) : hilbertMultiplier (1 : V (Slice L)) v = v := by
  let J := embedSlice L
  have dense : DenseRange J := ContinuousMap.toLp_denseRange ℝ _ ℝ (by norm_num)
  refine dense.induction_on v (isClosed_eq (hilbertMultiplier (1 : V (Slice L))).continuous continuous_id) ?_
  intro f
  simpa using hilbertMultiplier_embed (1 : V (Slice L)) f

set_option maxHeartbeats 1000000 in
private theorem embed_transfer_power (β : ℝ) (n : ℕ) (f : V (Slice L)) :
    embedSlice L ((wilsonOperator L β 1 ^ n) f) = (hilbertTransfer L β ^ n) (embedSlice L f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ' (wilsonOperator L β 1),pow_succ' (hilbertTransfer L β)]
    change embedSlice L (wilsonOperator L β 1 ((wilsonOperator L β 1 ^ n) f)) =
      hilbertTransfer L β ((hilbertTransfer L β ^ n) (embedSlice L f))
    rw [← hilbertTransfer_embed,ih]

set_option maxHeartbeats 1600000 in
/-- Basis trace of a two-mark kernel with two or more bonds on the unmarked arc. The initial step sits on the left by circularity of the trace. -/
theorem marked_hilbert_trace (β : ℝ) (a c : V (Slice L)) (d r : ℕ)
    (b : HilbertBasis ι ℝ (SliceHilbert L)) :
    let H := hilbertTransfer L β
    let A := hilbertMultiplier a
    let C := hilbertMultiplier c
    HasSum (fun i => ⟪b i,H (A ((H^d) (C ((H^(r+1)) (b i)))))⟫_ℝ)
      (markedRing (L := L) β a c d (r+1)) := by
  intro H A C
  let T := wilsonOperator L β 1
  let M := ContinuousLinearMap.mul ℝ (V (Slice L))
  let F := ((M a).comp (T^d)).comp (M c)
  let D := rowTransform (kernelRow L β)
  have h := wilson_cut_basis β F r b
  have eq (i : ι) : cutHilbertOperator β F r (b i) = H (A ((H^d) (C ((H^(r+1)) (b i))))) := by
    change H (embedSlice L (a * (T^d) (c * (T^r) (D (b i))))) = _
    have step : (H^(r+1)) (b i) = (H^r) (H (b i)) := by rw [pow_succ,mul_apply_eq_comp]
    let u := (T^r) (D (b i))
    have hu : embedSlice L u = (H^(r+1)) (b i) :=
      (embed_transfer_power β r (D (b i))).trans step.symm
    have hc : embedSlice L (c*u) = C ((H^(r+1)) (b i)) :=
      (hilbertMultiplier_embed c u).symm.trans (congrArg C hu)
    have hpow := (embed_transfer_power β d (c*u)).trans (congrArg (fun v => (H^d) v) hc)
    exact congrArg H ((hilbertMultiplier_embed a ((T^d) (c*u))).symm.trans (congrArg A hpow))
  rw [markedRing_trace β 1 one_ne_zero]
  simp only [one_pow,one_mul,mul_one]
  exact h.congr_fun (fun i => congrArg (inner ℝ (b i)) (eq i).symm)


/-- Sum of the Hilbert basis diagonal of the cyclically cut word H A H^d C H^(r+1). -/
def markedHilbertTrace (β : ℝ) (a c : V (Slice L)) (d r : ℕ)
    (b : HilbertBasis ι ℝ (SliceHilbert L)) : ℝ :=
  let H := hilbertTransfer L β
  ∑' i, ⟪b i,H (hilbertMultiplier a ((H^d) (hilbertMultiplier c ((H^(r+1)) (b i)))))⟫_ℝ

theorem wilson_plaquette_hilbert_trace (β : ℝ) (d r : ℕ) (b : HilbertBasis ι ℝ (SliceHilbert L)) :
    let tr := fun a c => markedHilbertTrace β a c d r b
    let a := observable L
    connected (N := extent d (r+1)) (wilsonMoment (L := L) β PeriodicWilson.su2Haar) d =
      tr a a / tr 1 1 - (tr a 1 / tr 1 1)^2 := by
  have h (a c : V (Slice L)) : markedHilbertTrace β a c d r b = markedRing β a c d (r+1) :=
    (marked_hilbert_trace β a c d r b).tsum_eq
  dsimp only
  simp only [h, connected_eq_ring,ringConnected]

#print axioms wilson_plaquette_hilbert_trace
#print axioms marked_hilbert_trace
#print axioms wilson_cut_basis
end
end YangMills.PlaquetteTransfer
