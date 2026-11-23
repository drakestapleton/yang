-- SPDX-License-Identifier: Apache-2.0
import PeriodicWilsonDS

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators ENNReal Topology
noncomputable section
private abbrev G := gaugeGroup.image
private abbrev Config (l : ℕ+) := Configuration gaugeGroup l

/-- A weighted coordinate Lipschitz bound in the physical link metric. -/
def LinkVariation {l : ℕ+} (v : Edge l → ℝ) (F : Config l → ℝ) : Prop :=
  ∀ U V, |F U-F V| ≤ ∑ a, v a * linkGeodesic (U a) (V a)

private theorem geodesic_self (u : G) : linkGeodesic u u = 0 := by
  rw [linkGeodesic_eq_angle,InnerProductGeometry.angle_self]
  exact norm_ne_zero_iff.mp (by rw [coordinates_norm]; norm_num)

private theorem link_distance_to {l : ℕ+} (U : Config l) (a : Edge l) :
    Continuous (fun V : Config l => linkGeodesic (V a) (U a)) := by
  unfold linkGeodesic polarAngle
  exact continuous_arccos.comp (continuous_scalar_link.comp ((continuous_apply a).mul continuous_const))

theorem LinkVariation.continuous {l : ℕ+} {v : Edge l → ℝ} {F : Config l → ℝ}
    (hf : LinkVariation v F) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro U
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : Continuous (fun V : Config l => ∑ a, v a * linkGeodesic (V a) (U a)) :=
    continuous_finsetSum _ fun a _ => continuous_const.mul (link_distance_to U a)
  apply squeeze_zero (fun _ => dist_nonneg) (fun V => by simpa only [Real.dist_eq] using hf V U)
  simpa only [geodesic_self,mul_zero,Finset.sum_const_zero] using hc.tendsto U

/-- Conditional expectation after resampling exactly link e. -/
def heatBathUpdate {l : ℕ+} (β : ℝ) (e : Edge l) (F : Config l → ℝ) (U : Config l) :=
  ∫ u, F (Function.update U e u) ∂heatBath β U e

/-- Coordinate weights after updating link e. Its old value is resampled. -/
def updateWeight {l : ℕ+} (β : ℝ) (v : Edge l → ℝ) (e a : Edge l) :=
  (if a=e then 0 else v a) + v e * straightInfluence β e a

/-- Bound the effect of one actual Gibbs update on a configuration observable. -/
theorem heatBathUpdate_variation {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) {F : Config l → ℝ} (hf : LinkVariation v F) (e : Edge l) :
    LinkVariation (updateWeight β v e) (heatBathUpdate β e F) := by
  intro U V
  let d := fun a => linkGeodesic (U a) (V a)
  let outside := ∑ a, (if a=e then 0 else v a) * d a
  let response := ∑ a, straightInfluence β e a * d a
  have hr : 0 ≤ response := Finset.sum_nonneg fun a _ => mul_nonneg
    (mul_nonneg (mul_nonneg (sqrt_nonneg _) hβ) (Nat.cast_nonneg _)) (arccos_nonneg _)
  have cF (W : Config l) : Continuous (fun u => F (Function.update W e u)) :=
    hf.continuous.comp (continuous_const.update (f := fun _ : G => W) e continuous_id)
  haveI := heatBath_probability hl β U e
  have bound := integral_difference_of_link_bound _ _ (cF U) (cF V) (A := outside) (hv e) hr
    (fun u w => (hf (Function.update U e u) (Function.update V e w)).trans_eq (by
      change _ = (∑ a, (if a=e then 0 else v a)*d a) + v e * linkGeodesic u w
      have singled : (∑ a : Edge l, if a=e then v a * linkGeodesic u w else 0) = v e * linkGeodesic u w := by simp
      rw [← singled]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a=e <;> simp [h,Function.update,d]))
    (heatBath_straight_influence hl hβ U V e)
  apply bound.trans_eq
  simp only [updateWeight,add_mul,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum,outside,response,d]

/-- Number of links eligible for a uniformly chosen update. -/
def edgeCount (l : ℕ+) : ℝ := Fintype.card (Edge l)
theorem edgeCount_pos (l : ℕ+) : 0 < edgeCount l := by
  unfold edgeCount; exact_mod_cast Fintype.card_pos

/-- One random-scan Markov step chooses a link uniformly and takes its heat-bath
conditional expectation. Iterates count individual updates. -/
def randomScan {l : ℕ+} (β : ℝ) (F : Config l → ℝ) (U : Config l) :=
  (∑ e, heatBathUpdate β e F U) / edgeCount l

def scanWeight {l : ℕ+} (β : ℝ) (v : Edge l → ℝ) (a : Edge l) :=
  (∑ e, updateWeight β v e a) / edgeCount l

theorem scanWeight_nonneg {l : ℕ+} {β : ℝ} (hβ : 0 ≤ β) {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) (a : Edge l) :
    0 ≤ scanWeight β v a := div_nonneg (Finset.sum_nonneg fun e _ => add_nonneg
      (by split <;> simp [hv]) (mul_nonneg (hv e) (mul_nonneg (mul_nonneg (sqrt_nonneg _) hβ) (Nat.cast_nonneg _)))) (edgeCount_pos _).le

theorem randomScan_variation {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) {F : Config l → ℝ} (hf : LinkVariation v F) :
    LinkVariation (scanWeight β v) (randomScan β F) := by
  intro U V
  let d := fun a => linkGeodesic (U a) (V a)
  rw [randomScan,randomScan,← sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos (edgeCount_pos _)]
  calc _ ≤ (∑ e, |heatBathUpdate β e F U - heatBathUpdate β e F V|) / edgeCount l :=
           div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (edgeCount_pos _).le
       _ ≤ (∑ e : Edge l, ∑ a : Edge l, updateWeight β v e a * d a) / edgeCount l :=
           div_le_div_of_nonneg_right (Finset.sum_le_sum fun e _ => heatBathUpdate_variation hl hβ hv hf e U V) (edgeCount_pos _).le
       _ = _ := by rw [Finset.sum_comm,Finset.sum_div]; simp only [scanWeight,Finset.sum_mul,div_mul_eq_mul_div,d]

def randomScanRate (l : ℕ+) (β : ℝ) := (edgeCount l - 1 + straightRow β) / edgeCount l

private theorem scanWeight_sum {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (v : Edge l → ℝ) :
    ∑ a, scanWeight β v a = randomScanRate l β * ∑ a, v a := by
  have out (e : Edge l) : (∑ a, if a=e then 0 else v a) = (∑ a, v a)-v e := by
    have singled : (∑ a : Edge l, if a=e then v a else 0) = v e := by simp
    rw [eq_sub_iff_add_eq,← singled]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _; split <;> simp_all
  simp only [scanWeight,←Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [updateWeight,Finset.sum_add_distrib,out,←Finset.mul_sum,straightInfluence_row hl,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul,randomScanRate,edgeCount]
  ring

theorem randomScanRate_subunit {l : ℕ+} {β : ℝ} (hβ : 0 ≤ β) (hw : β < sqrt 3/18) :
    0 ≤ randomScanRate l β ∧ randomScanRate l β < 1 := by
  have hn := edgeCount_pos l
  have h1 : 1 ≤ edgeCount l := by unfold edgeCount; exact_mod_cast (Fintype.card_pos (α := Edge l))
  have hrow : 0 ≤ straightRow β := div_nonneg (mul_nonneg (by norm_num) hβ) (sqrt_nonneg _)
  unfold randomScanRate
  exact ⟨div_nonneg (by linarith) hn.le,(div_lt_one hn).2 (by linarith only [straightRow_subunit.2 hw])⟩

private theorem iterate_variation {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) {F : Config l → ℝ} (hf : LinkVariation v F) (k : ℕ) :
    ∃ w : Edge l → ℝ, (∀ a, 0 ≤ w a) ∧ LinkVariation w ((randomScan β)^[k] F) ∧
      ∑ a, w a = (randomScanRate l β)^k * ∑ a, v a := by
  induction k with
  | zero => exact ⟨v,hv,hf,by simp⟩
  | succ k ih =>
    obtain ⟨w,hw,hF,hs⟩ := ih
    refine ⟨scanWeight β w,scanWeight_nonneg hβ hw,?_,?_⟩
    · rw [Function.iterate_succ_apply']; exact randomScan_variation hl hβ hw hF
    · rw [scanWeight_sum hl,hs]; ring

/-- Uniform oscillation decay of the actual iterated heat-bath operator. -/
theorem randomScan_oscillation {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) {F : Config l → ℝ} (hf : LinkVariation v F)
    (k : ℕ) (U V : Config l) :
    |((randomScan β)^[k] F) U-((randomScan β)^[k] F) V| ≤
      π * (randomScanRate l β)^k * ∑ a, v a := by
  obtain ⟨w,hw,hF,hs⟩ := iterate_variation hl hβ hv hf k
  apply (hF U V).trans
  calc _ ≤ ∑ a, w a * π := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (arccos_le_pi _) (hw a)
       _ = _ := by rw [← Finset.sum_mul,hs]; ring

/-- Resampling one link preserves the full periodic Wilson expectation. The
disintegration uses its actual conditional kernel on the other links. -/
theorem heatBathUpdate_stationary {l : ℕ+} (β : ℝ) (e : Edge l) {F : Config l → ℝ} (cf : Continuous F) :
    (∫ U, heatBathUpdate β e F U ∂wilsonLaw gaugeGroup l β su2Haar) =
    ∫ U, F U ∂wilsonLaw gaugeGroup l β su2Haar := by
  let μ := wilsonLaw gaugeGroup l β su2Haar
  let ρ := splitLaw β e
  let K := heatBathKernel β e
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  let test := fun z : Background e × G => F ((splitLink e).symm z)
  have htest : StronglyMeasurable test := (cf.measurable.comp (splitLink e).symm.measurable).stronglyMeasurable
  let m := fun b : Background e => ∫ u, test (b,u) ∂K b
  have hm : StronglyMeasurable m := htest.integral_kernel_prod_right' (κ := K)
  have pull (f : Config l → ℝ) :
      (∫ z, f ((splitLink e).symm z) ∂ρ) = ∫ U, f U ∂μ := by
    rw [show ρ = μ.map (splitLink e) from rfl,integral_map_equiv]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hi : Integrable test ρ := by
    rw [show ρ = μ.map (splitLink e) from rfl,integrable_map_equiv]
    simpa only [test,Function.comp_def,MeasurableEquiv.symm_apply_apply] using cf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have dis : ρ = ρ.fst.compProd K := wilsonLaw_disintegrates β e
  have resample (z : Background e × G) : heatBathUpdate β e F ((splitLink e).symm z) = m z.1 := by
    rcases z with ⟨b,u⟩
    simp only [heatBathUpdate,fill_update,m,test,K,heatBathKernel_apply β e b u]
  calc _ = ∫ z, heatBathUpdate β e F ((splitLink e).symm z) ∂ρ := (pull _).symm
       _ = ∫ z, m z.1 ∂ρ := integral_congr_ae (.of_forall resample)
       _ = ∫ b, m b ∂ρ.fst := (integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable).symm
       _ = ∫ z, test z ∂ρ := by
          have h := Measure.integral_compProd (by rwa [←dis] : Integrable test (ρ.fst.compProd K))
          exact h.symm.trans (congrArg (fun ν => ∫ z, test z ∂ν) dis.symm)
       _ = _ := pull F

private theorem randomScan_stationary {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) {F : Config l → ℝ} (hf : LinkVariation v F) :
    (∫ U, randomScan β F U ∂wilsonLaw gaugeGroup l β su2Haar) = ∫ U, F U ∂wilsonLaw gaugeGroup l β su2Haar := by
  let μ := wilsonLaw gaugeGroup l β su2Haar
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  have hi (e : Edge l) : Integrable (heatBathUpdate β e F) μ :=
    (heatBathUpdate_variation hl hβ hv hf e).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ U, (∑ e, heatBathUpdate β e F U) / edgeCount l ∂μ) = _
  rw [integral_div,integral_finsetSum _ (fun e _ => hi e)]
  have h (e : Edge l) : (∫ U, heatBathUpdate β e F U ∂μ) = ∫ U, F U ∂μ := heatBathUpdate_stationary β e hf.continuous
  simp only [h,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [show (Fintype.card (Edge l) : ℝ) ≠ 0 from (edgeCount_pos l).ne',edgeCount]; rfl

/-- Uniform convergence estimate to the actual periodic Wilson mean after k
uniformly chosen link updates. The decay parameter counts sampler steps. -/
theorem randomScan_wilson_mean_bound {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) {F : Config l → ℝ} (hf : LinkVariation v F)
    (k : ℕ) (U : Config l) :
    |((randomScan β)^[k] F) U - ∫ W, F W ∂wilsonLaw gaugeGroup l β su2Haar| ≤
      π * (randomScanRate l β)^k * ∑ a, v a := by
  let μ := wilsonLaw gaugeGroup l β su2Haar
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  have stat (n : ℕ) : (∫ W, ((randomScan β)^[n] F) W ∂μ) = ∫ W, F W ∂μ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨w,hw,hF,_⟩ := iterate_variation hl hβ hv hf n
      rw [Function.iterate_succ_apply',randomScan_stationary hl hβ hw hF]; exact ih
  obtain ⟨w,hw,hF,_⟩ := iterate_variation hl hβ hv hf k
  let T := (randomScan β)^[k] F
  have hi : Integrable T μ := hF.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid : T U - ∫ W, F W ∂μ = ∫ W, T U-T W ∂μ := by
    rw [integral_sub (integrable_const _) hi,integral_const,probReal_univ,one_smul,← stat k]
  rw [hid]
  let B := π * (randomScanRate l β)^k * ∑ a, v a
  calc _ ≤ ∫ W, |T U-T W| ∂μ := abs_integral_le_integral_abs
       _ ≤ ∫ _W, B ∂μ := integral_mono ((integrable_const _).sub hi).abs (integrable_const _)
          (fun W => randomScan_oscillation hl hβ hv hf k U W)
       _ = _ := by simp [B]

theorem randomScan_tendsto_wilson_mean {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (hwindow : β < sqrt 3/18) {v : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a)
    {F : Config l → ℝ} (hf : LinkVariation v F) (U : Config l) :
    Tendsto (fun k : ℕ => ((randomScan β)^[k] F) U) atTop
      (𝓝 (∫ W, F W ∂wilsonLaw gaugeGroup l β su2Haar)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hq := randomScanRate_subunit (l := l) hβ hwindow
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq.1 hq.2
  apply squeeze_zero (fun _ => dist_nonneg) (fun k => by simpa only [Real.dist_eq] using randomScan_wilson_mean_bound hl hβ hv hf k U)
  simpa only [mul_zero,zero_mul] using (ht.const_mul π).mul_const (∑ a, v a)

#print axioms heatBathUpdate_stationary
#print axioms randomScan_wilson_mean_bound
#print axioms randomScan_tendsto_wilson_mean
#print axioms heatBathUpdate_variation
#print axioms randomScanRate_subunit
#print axioms randomScan_oscillation
end
end YangMills.PeriodicWilson
