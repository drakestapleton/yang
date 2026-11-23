-- SPDX-License-Identifier: Apache-2.0
import WilsonPoleTransport

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal Topology
noncomputable section
private abbrev G := gaugeGroup.image
private abbrev Triple := (G × G) × G

private def squaredCost (P : Measure (G × G)) := ∫ z, linkGeodesic z.1 z.2 ^ 2 ∂P

private theorem cost_lintegral (P : Measure (G × G)) [IsFiniteMeasure P] :
    (∫⁻ z, ENNReal.ofReal (linkGeodesic z.1 z.2^2) ∂P) = ENNReal.ofReal (squaredCost P) := by
  have hc : Continuous (fun z : G × G => linkGeodesic z.1 z.2^2) := continuous_geodesic.pow 2
  have hi := hc.integrable_of_hasCompactSupport (μ := P) (HasCompactSupport.of_compactSpace _)
  exact (ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun z => sq_nonneg _)).symm

private theorem sfinite_probability {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] : SFinite μ := inferInstance

/-- Glue consecutive couplings by sampling the third link from its conditional
law given the middle link. Both pair marginals are recovered exactly. -/
theorem glue_link_couplings (P Q : Measure (G × G)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : P.snd = Q.fst) :
    ∃ L : Measure Triple, IsProbabilityMeasure L ∧ L.map Prod.fst = P ∧
      L.map (fun z => (z.1.2,z.2)) = Q := by
  haveI : IsFiniteMeasure P := inferInstance
  haveI : SFinite P := sfinite_probability P
  haveI : SFinite P.snd := sfinite_probability P.snd
  let K := Q.condKernel
  let L := P.compProd (K.prodMkLeft G)
  refine ⟨L,inferInstance,Measure.fst_compProd P (K.prodMkLeft G),?_⟩
  have hm : Measurable (fun z : Triple => (z.1.2,z.2)) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  ext S hs
  rw [Measure.map_apply hm hs]
  conv_rhs => rw [← Q.disintegrate Q.condKernel,← h]
  rw [Measure.compProd_apply (μ := P) (κ := K.prodMkLeft G) (hm hs),
    Measure.compProd_apply (μ := P.snd) (κ := Q.condKernel) hs]
  change (∫⁻ z, K z.2 (Prod.mk z.2 ⁻¹' S) ∂P) = ∫⁻ y, K y (Prod.mk y ⁻¹' S) ∂P.map Prod.snd
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_snd]

private theorem compose_cost (P Q : Measure (G × G)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hm : P.snd = Q.fst) {R S : ℝ} (hr : 0 ≤ R) (hs : 0 ≤ S)
    (hp : squaredCost P ≤ R^2) (hq : squaredCost Q ≤ S^2) :
    linkWassersteinSq P.fst Q.snd ≤ ENNReal.ofReal ((R+S)^2) := by
  obtain ⟨L,hL,hleft,hright⟩ := glue_link_couplings P Q hm
  letI := hL
  let left : Triple → G × G := Prod.fst
  let right := fun z : Triple => (z.1.2,z.2)
  let outer := fun z : Triple => (z.1.1,z.2)
  have cl : Continuous left := continuous_fst
  have cr : Continuous right := (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have co : Continuous outer := (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have h1 : (L.map outer).fst = P.fst := by
    rw [← hleft,Measure.fst,Measure.fst,Measure.map_map measurable_fst co.measurable,
      Measure.map_map measurable_fst cl.measurable]; rfl
  have h2 : (L.map outer).snd = Q.snd := by
    rw [← hright,Measure.snd,Measure.snd,Measure.map_map measurable_snd co.measurable,
      Measure.map_map measurable_snd cr.measurable]; rfl
  let γ : {A : Measure (G × G) // A.fst = P.fst ∧ A.snd = Q.snd} := ⟨L.map outer,h1,h2⟩
  apply (iInf_le _ γ).trans
  haveI := Measure.isProbabilityMeasure_map (μ := L) co.aemeasurable
  change (∫⁻ z, ENNReal.ofReal (linkGeodesic z.1 z.2^2) ∂L.map outer) ≤ _
  rw [cost_lintegral]; apply ENNReal.ofReal_le_ofReal
  let D := Function.uncurry linkGeodesic
  have hc : Continuous D := continuous_geodesic
  have push (f : Triple → G × G) (hf : Continuous f) :
      squaredCost (L.map f) = ∫ z, D (f z)^2 ∂L :=
    integral_map hf.aemeasurable (f := fun z => D z^2) (hc.pow 2).aestronglyMeasurable
  have hl : (∫ z, D (left z)^2 ∂L) ≤ R^2 := by rwa [← push left cl,hleft]
  have hh : (∫ z, D (right z)^2 ∂L) ≤ S^2 := by rwa [← push right cr,hright]
  rw [push outer co]
  exact rms_triangle L (hc.comp co) (hc.comp cl) (hc.comp cr) (fun _ => arccos_nonneg _)
    (.of_forall fun _ => arccos_nonneg _) (.of_forall fun _ => arccos_nonneg _)
    (fun z => geo_triangle z.1.1 z.1.2 z.2) hr hs hl hh

private theorem approx_coupling {μ ν : Measure G} [IsProbabilityMeasure μ] {R ε : ℝ}
    (hr : 0 ≤ R) (hε : 0 < ε) (hb : linkWassersteinSq μ ν ≤ ENNReal.ofReal (R^2)) :
    ∃ P : Measure (G × G), IsProbabilityMeasure P ∧ P.fst = μ ∧ P.snd = ν ∧
      squaredCost P ≤ (R+ε)^2 := by
  have he : ENNReal.ofReal (R^2) < ENNReal.ofReal ((R+ε)^2) :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos (by linarith))).2
      (pow_lt_pow_left₀ (by linarith) hr (by decide))
  obtain ⟨P,hp⟩ := iInf_lt_iff.mp (hb.trans_lt he)
  haveI : IsProbabilityMeasure P.val := ⟨by rw [← Measure.fst_univ,P.prop.1,measure_univ]⟩
  refine ⟨P.val,inferInstance,P.prop.1,P.prop.2,?_⟩
  change (∫⁻ z, ENNReal.ofReal (linkGeodesic z.1 z.2^2) ∂P.val) < _ at hp
  rw [cost_lintegral] at hp
  exact ((ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos (by linarith : 0 < R+ε))).1 hp).le

/-- Compose two geodesic Wasserstein upper bounds without assuming an optimal
coupling exists. The approximation error tends to zero after gluing. -/
theorem linkWassersteinSq_triangle_bound {μ ν ξ : Measure G} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {R S : ℝ} (hr : 0 ≤ R) (hs : 0 ≤ S) (h₁ : linkWassersteinSq μ ν ≤ ENNReal.ofReal (R^2))
    (h₂ : linkWassersteinSq ν ξ ≤ ENNReal.ofReal (S^2)) :
    linkWassersteinSq μ ξ ≤ ENNReal.ofReal ((R+S)^2) := by
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (((R+ε)+(S+ε))^2))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((R+S)^2))) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (((R+ε)+(S+ε))^2)) := ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨P,hP,p₁,p₂,hp⟩ := approx_coupling hr hε h₁
  obtain ⟨Q,hQ,q₁,q₂,hq⟩ := approx_coupling hs hε h₂
  have h := compose_cost P Q (p₂.trans q₁.symm) (add_nonneg hr hε.le) (add_nonneg hs hε.le) hp hq
  simpa only [p₁,q₂] using h

/-- A coupling cost controls expectations even when the two test functions use
different backgrounds, with an additive error for the unchanged coordinates. -/
theorem integral_difference_of_link_bound {μ ν : Measure G} [IsProbabilityMeasure μ]
    (f g : G → ℝ) (cf : Continuous f) (cg : Continuous g) {A B R : ℝ}
    (hb : 0 ≤ B) (hr : 0 ≤ R) (hfg : ∀ u v, |f u-g v| ≤ A+B*linkGeodesic u v)
    (hw : linkWassersteinSq μ ν ≤ ENNReal.ofReal (R^2)) :
    |(∫ u, f u ∂μ)-(∫ v, g v ∂ν)| ≤ A+B*R := by
  have ht : Tendsto (fun ε : ℝ => A+B*(R+ε)) (𝓝[>] 0) (𝓝 (A+B*R)) := by
    have hc : Continuous (fun ε : ℝ => A+B*(R+ε)) := by fun_prop
    simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨P,hP,h₁,h₂,hcost⟩ := approx_coupling hr hε hw
  let D := Function.uncurry linkGeodesic
  have cD : Continuous D := continuous_geodesic
  have hmean : (∫ z, D z ∂P) ≤ R+ε := by
    have hv := variance_nonneg D P
    rw [variance_eq_sub (cD.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hv
    change 0 ≤ (∫ z, D z^2 ∂P)-(∫ z, D z ∂P)^2 at hv
    change (∫ z, D z^2 ∂P) ≤ (R+ε)^2 at hcost
    have he : 0 ≤ R+ε := add_nonneg hr hε.le
    have ha : |∫ z, D z ∂P| ≤ R+ε :=
      ((sq_le_sq).mp ((sub_nonneg.mp hv).trans hcost)).trans_eq (abs_of_nonneg he)
    exact (le_abs_self _).trans ha
  let F := fun z : G × G => f z.1-g z.2
  have cF : Continuous F := (cf.comp continuous_fst).sub (cg.comp continuous_snd)
  have he : (∫ u, f u ∂μ)-(∫ v, g v ∂ν) = ∫ z, F z ∂P := by
    rw [← h₁,← h₂,Measure.fst,Measure.snd,integral_map measurable_fst.aemeasurable cf.aestronglyMeasurable,
      integral_map measurable_snd.aemeasurable cg.aestronglyMeasurable]
    exact (integral_sub ((cf.comp continuous_fst).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((cg.comp continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
  rw [he]
  have hi := cD.integrable_of_hasCompactSupport (μ := P) (HasCompactSupport.of_compactSpace _)
  calc _ ≤ ∫ z, |F z| ∂P := abs_integral_le_integral_abs
       _ ≤ ∫ z, A+B*D z ∂P := integral_mono
            (cF.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            ((integrable_const A).add (hi.const_mul B)) (fun z => hfg z.1 z.2)
       _ = A+B*(∫ z, D z ∂P) := by simp [integral_add (integrable_const A) (hi.const_mul B),integral_const_mul]
       _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hmean hb) _

#print axioms integral_difference_of_link_bound
#print axioms glue_link_couplings
#print axioms linkWassersteinSq_triangle_bound
end
end YangMills.PeriodicWilson
