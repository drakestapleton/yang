-- SPDX-License-Identifier: Apache-2.0
import WilsonHeatBathDynamics

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory PhaseTwo UfbiBridge Real Filter Set
open scoped BigOperators Topology
noncomputable section
private abbrev Config (l : ℕ+) := Configuration gaugeGroup l
private abbrev law (l : ℕ+) (β : ℝ) := wilsonLaw gaugeGroup l β su2Haar

private theorem update_difference {l : ℕ+} {v : Edge l → ℝ} {F : Config l → ℝ}
    (hv : ∀ a, 0 ≤ v a) (hf : LinkVariation v F) (U : Config l) (e : Edge l) (u : gaugeGroup.image) :
    |F U-F (Function.update U e u)| ≤ π * v e := by
  apply (hf U (Function.update U e u)).trans
  have hs (z : gaugeGroup.image) : linkGeodesic z z = 0 := by
    rw [linkGeodesic_eq_angle,InnerProductGeometry.angle_self]
    exact norm_ne_zero_iff.mp (by rw [coordinates_norm]; norm_num)
  calc _ = ∑ a : Edge l, if a=e then v e * linkGeodesic (U e) u else 0 := by
                apply Finset.sum_congr rfl
                intro a _
                by_cases h : a=e <;> simp [h,Function.update,hs]
       _ ≤ _ := by
          have hd : linkGeodesic (U e) u ≤ π := arccos_le_pi _
          simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_comm π]
          exact mul_le_mul_of_nonneg_left hd (hv e)

private theorem update_drift {l : ℕ+} (hl : 1 < l.val) (β : ℝ) {v : Edge l → ℝ} {F : Config l → ℝ}
    (hv : ∀ a, 0 ≤ v a) (hf : LinkVariation v F) (U : Config l) (e : Edge l) :
    |F U - heatBathUpdate β e F U| ≤ π * v e := by
  let μ := heatBath β U e
  haveI : IsProbabilityMeasure μ := heatBath_probability hl β U e
  let f := fun u => F (Function.update U e u)
  have cf : Continuous f := hf.continuous.comp (continuous_const.update (f := fun _ : gaugeGroup.image => U) e continuous_id)
  have hi := cf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hid : F U - heatBathUpdate β e F U = ∫ u, F U - f u ∂μ := by
    rw [integral_sub (integrable_const _) hi,integral_const,probReal_univ,one_smul]; rfl
  rw [hid]
  calc _ ≤ ∫ u, |F U-f u| ∂μ := abs_integral_le_integral_abs
       _ ≤ ∫ _u, π*v e ∂μ := integral_mono ((integrable_const _).sub hi).abs (integrable_const _)
          (fun u => update_difference hv hf U e u)
       _ = _ := by simp

private def pairing {l : ℕ+} (β : ℝ) (F G : Config l → ℝ) := ∫ U, F U * G U ∂law l β

/-- Centering the second observable at a fixed value of link e costs only its
variation at e. The term independent of this link cancels by stationarity. -/
private theorem pairing_update {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v w : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) (hw : ∀ a, 0 ≤ w a)
    {F G : Config l → ℝ} (hf : LinkVariation v F) (hg : LinkVariation w G) (e : Edge l) :
    |pairing β F G - pairing β (heatBathUpdate β e F) G| ≤ π^2 * v e * w e := by
  let μ := law l β
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  let P := heatBathUpdate β e F
  let H := fun U : Config l => G (Function.update U e 1)
  have cP : Continuous P := (heatBathUpdate_variation hl hβ hv hf e).continuous
  have cH : Continuous H := hg.continuous.comp (continuous_id.update e continuous_const)
  have hi {f : Config l → ℝ} (cf : Continuous f) : Integrable f μ :=
    cf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have station := heatBathUpdate_stationary β e (hf.continuous.mul cH)
  have factor (U : Config l) : heatBathUpdate β e (F*H) U = P U * H U := by
    change (∫ u, F (Function.update U e u) * G (Function.update (Function.update U e u) e 1) ∂heatBath β U e) = _
    simp only [Function.update_idem,integral_mul_const]; rfl
  change (∫ U, heatBathUpdate β e (F*H) U ∂μ) = ∫ U, F U*H U ∂μ at station
  simp_rw [factor] at station
  have center : (∫ U, (F U-P U)*H U ∂μ) = 0 := by
    simp_rw [sub_mul]
    rw [integral_sub (f := fun U => F U*H U) (g := fun U => P U*H U) (hi (hf.continuous.mul cH)) (hi (cP.mul cH)),station,sub_self]
  have hid : pairing β F G - pairing β P G = ∫ U, (F U-P U)*(G U-H U) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub (f := fun U => (F U-P U)*G U) (g := fun U => (F U-P U)*H U) (hi ((hf.continuous.sub cP).mul hg.continuous)) (hi ((hf.continuous.sub cP).mul cH)),center,sub_zero]
    simp_rw [sub_mul]
    rw [integral_sub (f := fun U => F U*G U) (g := fun U => P U*G U) (hi (hf.continuous.mul hg.continuous)) (hi (cP.mul hg.continuous))]; rfl
  change |pairing β F G - pairing β P G| ≤ _
  rw [hid]
  calc _ ≤ ∫ U, |(F U-P U)*(G U-H U)| ∂μ := abs_integral_le_integral_abs
       _ ≤ ∫ _U, π^2*v e*w e ∂μ := by
          apply integral_mono (hi (((hf.continuous.sub cP).mul (hg.continuous.sub cH)).abs)) (integrable_const _)
          intro U
          change |(F U-P U)*(G U-H U)| ≤ _
          rw [abs_mul]
          exact (mul_le_mul (update_drift hl β hv hf U e) (update_difference hw hg U e 1)
            (abs_nonneg _) (mul_nonneg pi_pos.le (hv e))).trans_eq (by ring)
       _ = _ := by simp

private theorem pairing_scan {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    {v w : Edge l → ℝ} (hv : ∀ a, 0 ≤ v a) (hw : ∀ a, 0 ≤ w a)
    {F G : Config l → ℝ} (hf : LinkVariation v F) (hg : LinkVariation w G) :
    |pairing β F G - pairing β (randomScan β F) G| ≤ π^2 * (∑ e, v e*w e) / edgeCount l := by
  let μ := law l β
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  have hi (e : Edge l) : Integrable (fun U => heatBathUpdate β e F U * G U) μ :=
    ((heatBathUpdate_variation hl hβ hv hf e).continuous.mul hg.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hscan : pairing β (randomScan β F) G = (∑ e, pairing β (heatBathUpdate β e F) G) / edgeCount l := by
    unfold pairing randomScan
    simp_rw [div_mul_eq_mul_div,Finset.sum_mul]
    rw [integral_div,integral_finsetSum _ (fun e _ => hi e)]
  have hav : pairing β F G = (∑ _e : Edge l, pairing β F G)/edgeCount l := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change _ = edgeCount l * _ / edgeCount l
    field_simp [(edgeCount_pos l).ne']
  rw [hscan]
  conv_lhs => arg 1; lhs; rw [hav]
  rw [← sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos (edgeCount_pos _)]
  apply div_le_div_of_nonneg_right _ (edgeCount_pos _).le
  apply (Finset.abs_sum_le_sum_abs ..).trans
  simpa only [Finset.mul_sum,mul_assoc] using Finset.sum_le_sum (s := Finset.univ) (fun e _ => pairing_update hl hβ hv hw hf hg e)

private def weightPair {l : ℕ+} (v p : Edge l → ℝ) := ∑ e, v e*p e

private theorem scan_budget {l : ℕ+} (β : ℝ) {v w p : Edge l → ℝ} (hv : ∀ e, 0 ≤ v e)
    (hp : ∀ e, w e + ∑ a, straightInfluence β e a * p a ≤ p e) :
    weightPair v w / edgeCount l ≤ weightPair v p - weightPair (scanWeight β v) p := by
  have hout (e : Edge l) : (∑ a, (if a=e then 0 else v a) * p a) = weightPair v p - v e*p e := by
    have hsingle : (∑ a : Edge l, if a=e then v a*p a else 0) = v e*p e := by simp
    rw [eq_sub_iff_add_eq,←hsingle,←Finset.sum_add_distrib]
    unfold weightPair
    apply Finset.sum_congr rfl
    intro a _; split <;> simp_all
  have hdual : weightPair (scanWeight β v) p =
      ((edgeCount l-1)*weightPair v p + ∑ e, v e * ∑ a, straightInfluence β e a*p a)/edgeCount l := by
    change (∑ a, ((∑ e, updateWeight β v e a)/edgeCount l)*p a) = _
    simp only [div_mul_eq_mul_div,Finset.sum_mul,←Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [updateWeight,add_mul,Finset.sum_add_distrib,hout,mul_assoc,←Finset.mul_sum,
      Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    unfold weightPair edgeCount; ring
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => mul_le_mul_of_nonneg_left (hp e) (hv e))
  simp only [mul_add,Finset.sum_add_distrib] at h
  rw [hdual,le_sub_iff_add_le,←add_div,div_le_iff₀ (edgeCount_pos _)]
  unfold weightPair at *
  linarith only [h]

/-- The covariance under the full periodic Wilson law. -/
def wilsonCovariance {l : ℕ+} (β : ℝ) (F G : Config l → ℝ) :=
  (∫ U, F U * G U ∂law l β) - (∫ U, F U ∂law l β) * ∫ U, G U ∂law l β

/-- Any nonnegative profile p dominating w + A p gives a Wilson covariance
bound. The random-scan averaging factor cancels in the telescoping sum. -/
theorem wilson_covariance_comparison {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (hwindow : β < sqrt 3/18) {v w p : Edge l → ℝ}
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e)
    (hcomp : ∀ e, w e + ∑ a, straightInfluence β e a * p a ≤ p e)
    {F G : Config l → ℝ} (hf : LinkVariation v F) (hg : LinkVariation w G) :
    |wilsonCovariance β F G| ≤ π^2 * ∑ e, v e*p e := by
  let μ := law l β
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  let T := fun n : ℕ => (randomScan β)^[n] F
  have tel (n : ℕ) : ∃ u : Edge l → ℝ, (∀ e, 0 ≤ u e) ∧ LinkVariation u (T n) ∧
      |pairing β F G-pairing β (T n) G| ≤ π^2*(weightPair v p-weightPair u p) := by
    induction n with
    | zero => exact ⟨v,hv,hf,by simp [T]⟩
    | succ n ih =>
      obtain ⟨u,hu,ht,hstep⟩ := ih
      have he : T (n+1) = randomScan β (T n) := Function.iterate_succ_apply' ..
      rw [he]
      refine ⟨scanWeight β u,scanWeight_nonneg hβ hu,randomScan_variation hl hβ hu ht,?_⟩
      have hs := pairing_scan hl hβ hu hw ht hg
      have hb := mul_le_mul_of_nonneg_left (scan_budget β hu hcomp) (sq_nonneg π)
      have ha := abs_sub_le (pairing β F G) (pairing β (T n) G) (pairing β (randomScan β (T n)) G)
      rw [mul_div_assoc] at hs
      apply ha.trans ((add_le_add hstep (hs.trans hb)).trans_eq ?_)
      ring
  let M := ∫ U, F U ∂μ
  let B := |M| + π * ∑ e, v e
  have hlim : Tendsto (fun n => pairing β (T n) G) atTop (𝓝 (M * ∫ U, G U ∂μ)) := by
    rw [← integral_const_mul]
    apply tendsto_integral_of_dominated_convergence (fun U => B * |G U|)
    · intro n; obtain ⟨_,_,ht,_⟩ := tel n
      exact (ht.continuous.mul hg.continuous).aestronglyMeasurable
    · exact (hg.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul B
    · intro n; apply ae_of_all; intro U
      have h := randomScan_wilson_mean_bound hl hβ hv hf n U
      change |T n U - M| ≤ _ at h
      have hq := randomScanRate_subunit (l := l) hβ hwindow
      have hp1 := pow_le_one₀ hq.1 hq.2.le (n := n)
      have hsum : 0 ≤ ∑ e, v e := Finset.sum_nonneg fun e _ => hv e
      have hrate := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 pi_pos.le) hsum
      have ht : |T n U| ≤ B := by
        have hadd := abs_add_le (T n U - M) M
        rw [sub_add_cancel] at hadd; unfold B; linarith only [h,hadd,hrate]
      change ‖T n U * G U‖ ≤ _
      rw [Real.norm_eq_abs,abs_mul]; exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    · apply ae_of_all; intro U
      exact (randomScan_tendsto_wilson_mean hl hβ hwindow hv hf U).mul_const (G U)
  apply le_of_tendsto (((tendsto_const_nhds (x := pairing β F G)).sub hlim).abs)
  filter_upwards with n
  obtain ⟨u,hu,_,ht⟩ := tel n
  apply ht.trans
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (Finset.sum_nonneg fun e _ => mul_nonneg (hu e) (hp e))) (sq_nonneg _)

/-- A walk of exactly j neighbor incidences on the periodic Wilson lattice. -/
def IncidencePath {l : ℕ+} : ℕ → Edge l → Edge l → Prop
  | 0, e, a => e = a
  | j+1, e, a => ∃ b, 0 < neighborIncidenceCount e b ∧ IncidencePath j b a

/-- Positive coordinate weights of the two observables have no connecting
path of fewer than k periodic neighbor incidences. -/
def SupportsSeparated {l : ℕ+} (v w : Edge l → ℝ) (k : ℕ) : Prop :=
  ∀ e, v e ≠ 0 → ∀ j < k, ∀ a, IncidencePath j e a → w a = 0

private def comparisonProfile {l : ℕ+} (β B : ℝ) (w : Edge l → ℝ) : ℕ → Edge l → ℝ
  | 0, _ => B / (1-straightRow β)
  | k+1, e => w e + ∑ a, straightInfluence β e a * comparisonProfile β B w k a

private theorem comparisonProfile_bounds {l : ℕ+} (hl : 1 < l.val) {β B : ℝ}
    (hβ : 0 ≤ β) (hα : straightRow β < 1) (hB : 0 ≤ B) {w : Edge l → ℝ}
    (hw : ∀ e, 0 ≤ w e) (hb : ∀ e, w e ≤ B) (k : ℕ) (e : Edge l) :
    0 ≤ comparisonProfile β B w k e ∧ comparisonProfile β B w (k+1) e ≤ comparisonProfile β B w k e := by
  have hA (i a : Edge l) : 0 ≤ straightInfluence β i a :=
    mul_nonneg (mul_nonneg (sqrt_nonneg _) hβ) (Nat.cast_nonneg _)
  induction k generalizing e with
  | zero =>
    simp only [comparisonProfile,←Finset.sum_mul,straightInfluence_row hl]
    refine ⟨div_nonneg hB (by linarith),?_⟩
    have hid : B + straightRow β * (B/(1-straightRow β)) = B/(1-straightRow β) := by
      field_simp [(sub_pos.mpr hα).ne']; ring
    linarith only [hid,hb e]
  | succ k ih =>
    constructor
    · exact add_nonneg (hw e) (Finset.sum_nonneg fun a _ => mul_nonneg (hA e a) (ih a).1)
    · exact add_le_add_right (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih a).2 (hA e a)) _

private theorem comparisonProfile_separated {l : ℕ+} (hl : 1 < l.val) {β B : ℝ}
    (hβ : 0 ≤ β) (w : Edge l → ℝ) (k : ℕ) (e : Edge l)
    (hsep : ∀ j < k, ∀ a, IncidencePath j e a → w a = 0) :
    comparisonProfile β B w k e ≤ B/(1-straightRow β)*(straightRow β)^k := by
  induction k generalizing e with
  | zero => simp [comparisonProfile]
  | succ k ih =>
    rw [comparisonProfile,hsep 0 (Nat.zero_lt_succ _) e rfl,zero_add]
    calc _ ≤ ∑ a : Edge l, straightInfluence β e a * (B/(1-straightRow β)*(straightRow β)^k) := by
              apply Finset.sum_le_sum; intro a _
              by_cases hadj : 0 < neighborIncidenceCount e a
              · apply mul_le_mul_of_nonneg_left (ih a ?_) (mul_nonneg (mul_nonneg (sqrt_nonneg _) hβ) (Nat.cast_nonneg _))
                intro j hj b hpath
                exact hsep (j+1) (Nat.succ_lt_succ hj) b ⟨a,hadj,hpath⟩
              · simp [straightInfluence,Nat.eq_zero_of_not_pos hadj]
         _ = _ := by rw [←Finset.sum_mul,straightInfluence_row hl]; ring

/-- Exponential decay in actual finite-volume lattice separation. The
prefactor depends on the Lipschitz profiles and the row bound, uniformly in
the side of the torus. Both expectations are under the periodic Wilson law. -/
theorem wilson_spatial_clustering {l : ℕ+} (hl : 1 < l.val) {β B : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (hB : 0 ≤ B)
    {v w : Edge l → ℝ} (hv : ∀ e, 0 ≤ v e) (hw : ∀ e, 0 ≤ w e) (hb : ∀ e, w e ≤ B)
    {F G : Config l → ℝ} (hf : LinkVariation v F) (hg : LinkVariation w G)
    (k : ℕ) (hsep : SupportsSeparated v w k) :
    |wilsonCovariance β F G| ≤ (π^2*(∑ e, v e)*B/(1-straightRow β))*(straightRow β)^k := by
  have hprof := comparisonProfile_bounds hl hβ (straightRow_subunit.2 hwindow) hB hw hb k
  apply (wilson_covariance_comparison hl hβ hwindow hv hw (fun e => (hprof e).1) (fun e => (hprof e).2) hf hg).trans
  calc _ ≤ π^2 * ∑ e, v e * (B/(1-straightRow β)*(straightRow β)^k) := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
              apply Finset.sum_le_sum; intro e _
              by_cases he : v e = 0
              · simp [he]
              exact mul_le_mul_of_nonneg_left (comparisonProfile_separated hl hβ w k e (hsep e he)) (hv e)
       _ = _ := by rw [←Finset.sum_mul]; ring

/-- Shortest base-site displacement along a specified axis, with wraparound. -/
def periodicAxisDistance {l : ℕ+} (t : Axis) (e a : Edge l) : ℕ :=
  ((a.1 t - e.1 t).valMinAbs).natAbs

theorem incidencePath_axis_distance {l : ℕ+} (hl : 1 < l.val) (t : Axis) {j : ℕ}
    {e a : Edge l} (hpath : IncidencePath j e a) : periodicAxisDistance t e a ≤ j := by
  have step {i b : Edge l} (hi : 0 < neighborIncidenceCount i b) : periodicAxisDistance t i b ≤ 1 := by
    obtain ⟨q,hq,hlink⟩ : ∃ q ∈ incidences i, (neighbor i q.1 q.2).1 = b := by
      by_contra! h
      have he : neighborIncidenceCount i b = 0 := Finset.sum_eq_zero fun q hq => if_neg (h q hq)
      omega
    have hs := neighbor_axis_step i (Finset.mem_product.mp hq).1 q.2 t
    simp only at hs
    rw [hlink] at hs
    have h1 : (1 : ZMod l.val).valMinAbs = 1 := by
      simpa only [Nat.cast_one,Int.natCast_one] using (ZMod.valMinAbs_natCast_of_le_half (n := l.val) (a := 1) (by omega))
    rcases hs with h | h | h <;> simp [periodicAxisDistance,h,h1]
  induction j generalizing e a with
  | zero => change e=a at hpath; subst a; simp [periodicAxisDistance]
  | succ j ih =>
    obtain ⟨b,heb,hba⟩ := hpath
    have delta : a.1 t - e.1 t = (b.1 t-e.1 t)+(a.1 t-b.1 t) := by abel
    calc periodicAxisDistance t e a ≤ periodicAxisDistance t e b + periodicAxisDistance t b a := by
                unfold periodicAxisDistance; rw [delta]
                exact (ZMod.natAbs_valMinAbs_add_le ..).trans (Int.natAbs_add_le ..)
         _ ≤ j+1 := by have := step heb; have := ih hba; omega

/-- Separation of the two supports along any periodic coordinate implies
separation in the Wilson incidence graph, including across the seam. -/
theorem supportsSeparated_of_axis {l : ℕ+} (hl : 1 < l.val) (t : Axis) {v w : Edge l → ℝ} (k : ℕ)
    (haxis : ∀ e a, v e ≠ 0 → w a ≠ 0 → k ≤ periodicAxisDistance t e a) :
    SupportsSeparated v w k := by
  intro e he j hj a hpath
  by_contra ha
  exact (haxis e a he ha).not_gt ((incidencePath_axis_distance hl t hpath).trans_lt hj)

private theorem link_distance_variation {l : ℕ+} (e : Edge l) (g : gaugeGroup.image) :
    LinkVariation (fun a => if a=e then 1 else 0) (fun U : Config l => linkGeodesic (U e) g) := by
  intro V W
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [abs_le]
  have h1 := geo_triangle (V e) (W e) g
  have h2 := geo_triangle (W e) (V e) g
  have hs : linkGeodesic (W e) (V e) = linkGeodesic (V e) (W e) := by
    simp only [linkGeodesic_eq_angle]; exact InnerProductGeometry.angle_comm ..
  constructor <;> linarith

/-- A concrete correlation of two link angles in the periodic Wilson measure
decays in their cyclic separation along any axis, including Euclidean time. -/
theorem wilson_link_angle_clustering {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (t : Axis) (e a : Edge l) (g h : gaugeGroup.image) :
    |wilsonCovariance β (fun U => linkGeodesic (U e) g) (fun U => linkGeodesic (U a) h)| ≤
      (π^2/(1-straightRow β))*(straightRow β)^(periodicAxisDistance t e a) := by
  let v := fun i : Edge l => if i=e then (1:ℝ) else 0
  let w := fun i : Edge l => if i=a then (1:ℝ) else 0
  have hsep : SupportsSeparated v w (periodicAxisDistance t e a) := by
    apply supportsSeparated_of_axis hl t
    intro i b hi hb
    by_cases he : i=e <;> by_cases ha : b=a <;> simp_all [v,w]
  have bound := wilson_spatial_clustering hl hβ hwindow (by norm_num : (0:ℝ) ≤ 1)
    (v := v) (w := w) (fun i => by dsimp [v]; split <;> norm_num) (fun i => by dsimp [w]; split <;> norm_num)
    (fun i => by dsimp [w]; split <;> norm_num) (link_distance_variation e g) (link_distance_variation a h) _ hsep
  simpa [v] using bound

/-- Two periodic observables and coordinate Lipschitz profiles whose supports
are separated by at least k Wilson neighbor incidences. -/
structure WilsonShellPair (l : ℕ+) (k : ℕ) where
  first : Config l → ℝ
  second : Config l → ℝ
  v : Edge l → ℝ
  w : Edge l → ℝ
  B : ℝ
  hv : ∀ e, 0 ≤ v e
  hw : ∀ e, 0 ≤ w e
  hB : 0 ≤ B
  upper : ∀ e, w e ≤ B
  firstVariation : LinkVariation v first
  secondVariation : LinkVariation w second
  separation : SupportsSeparated v w k

/-- The Wilson covariance comparison is proved inside this corollary. The
continuum input identifies the shell covariances with spectral Laplace
transforms and bounds the Lipschitz prefactors uniformly for each state. -/
theorem wilson_gap_of_covariance_limits {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax) (hwindow : βmax < sqrt 3/18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val) (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Icc 0 βmax)
    (hlimit : ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
      ∃ (C : ℝ) (S : (n k : ℕ) → WilsonShellPair (l n) k), 0 ≤ C ∧
        (∀ n k, π^2 * (∑ e, (S n k).v e) * (S n k).B / (1-straightRow (β n)) ≤ C) ∧
        ∀ k : ℕ, Tendsto (fun n => wilsonCovariance (β n) (S n k).first (S n k).second) atTop
          (𝓝 (∫ p, exp (-((k:ℝ)*R)*YangMills.time p) ∂(T.energyMomentum.diagonal ψ)))) :
    HasRelativisticMassGap T ((1/R)*log (1/straightRow βmax)) := by
  have hα : 0 < straightRow βmax := div_pos (mul_pos (by norm_num) hpos) (by positivity)
  apply shell_envelopes_imply_relativistic_mass_gap T hW0 hW1 hW2 hR hα (straightRow_subunit.2 hwindow)
  intro ψ hψ
  obtain ⟨C,S,hC,hpref,hspec⟩ := hlimit ψ hψ
  refine ⟨C,fun n k => wilsonCovariance (β n) (S n k).first (S n k).second,hC,hspec,?_⟩
  intro n k
  let P := S n k
  have h := wilson_spatial_clustering (hl n) (hβ n).1 ((hβ n).2.trans_lt hwindow) P.hB
    P.hv P.hw P.upper P.firstVariation P.secondVariation k P.separation
  have hr : straightRow (β n) ≤ straightRow βmax := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hβ n).2 (by norm_num)) (sqrt_nonneg _)
  have hnn : 0 ≤ straightRow (β n) := div_nonneg (mul_nonneg (by norm_num) (hβ n).1) (sqrt_nonneg _)
  exact (le_abs_self _).trans (h.trans (mul_le_mul (hpref n k)
    (pow_le_pow_left₀ hnn hr k) (pow_nonneg hnn _) hC))

#print axioms incidencePath_axis_distance
#print axioms supportsSeparated_of_axis
#print axioms wilson_link_angle_clustering
#print axioms wilson_covariance_comparison
#print axioms wilson_spatial_clustering
#print axioms wilson_gap_of_covariance_limits
end
end YangMills.PeriodicWilson
