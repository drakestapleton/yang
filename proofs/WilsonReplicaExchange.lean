-- SPDX-License-Identifier: Apache-2.0
import WilsonWordClustering

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real
noncomputable section

abbrev WilsonConfig (l : ℕ+) := Configuration gaugeGroup l
abbrev WilsonReplicas (l : ℕ+) := WilsonConfig l × WilsonConfig l
private abbrev G := gaugeGroup.image
abbrev prior (l : ℕ+) := Measure.pi (fun _ : Edge l => su2Haar)
private abbrev law (l : ℕ+) (β : ℝ) := wilsonLaw gaugeGroup l β su2Haar

/-- Two independent copies of the normalized Wilson field. -/
def replicaLaw (l : ℕ+) (β : ℝ) := (law l β).prod (law l β)

instance replicaLaw_probability (l : ℕ+) (β : ℝ) : IsProbabilityMeasure (replicaLaw l β) := by
  haveI := wilson_probability l β
  unfold replicaLaw; infer_instance

/-- Exchange both replicas on a selected set of links. -/
def exchangeLinks {l : ℕ+} (m : Edge l → Bool) (z : WilsonReplicas l) : WilsonReplicas l :=
  (fun e => if m e then z.2 e else z.1 e, fun e => if m e then z.1 e else z.2 e)

theorem exchangeLinks_involutive {l : ℕ+} (m : Edge l → Bool) : Function.Involutive (exchangeLinks m) := by
  intro z; apply Prod.ext <;> funext e <;> cases h : m e <;> simp [exchangeLinks,h]

theorem exchangeLinks_commute {l : ℕ+} (m n : Edge l → Bool) (z : WilsonReplicas l) :
    exchangeLinks m (exchangeLinks n z) = exchangeLinks n (exchangeLinks m z) := by
  apply Prod.ext <;> funext e <;> cases a : m e <;> cases b : n e <;> simp [exchangeLinks,a,b]

theorem exchange_cont {l : ℕ+} (m : Edge l → Bool) : Continuous (exchangeLinks m) := by
  apply Continuous.prodMk <;> apply continuous_pi <;> intro e <;>
    split <;> fun_prop

theorem exchange_preserving {l : ℕ+} (m : Edge l → Bool) :
    MeasurePreserving (exchangeLinks m) ((prior l).prod (prior l)) ((prior l).prod (prior l)) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow G G (Edge l)
  have he := measurePreserving_arrowProdEquivProdArrow G G (Edge l) (fun _ => su2Haar) (fun _ => su2Haar)
  let f (e : Edge l) (x : G × G) := if m e then x.swap else x
  have hf (e : Edge l) : MeasurePreserving (f e) (su2Haar.prod su2Haar) (su2Haar.prod su2Haar) := by
    cases h : m e <;> simp only [f,h, Bool.false_eq_true, if_false, if_true]
    · exact MeasurePreserving.id _
    · exact Measure.measurePreserving_swap
  have H := he.comp ((measurePreserving_pi _ _ hf).comp (he.symm E))
  convert H using 1
  funext z; apply Prod.ext <;> funext e <;> cases a : m e <;> simp [exchangeLinks, E, f, Function.comp_def, a,
    MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]

private theorem continuous_wilsonEnergy {l : ℕ+} : Continuous (wilsonEnergy (g := gaugeGroup) (l := l)) := by
  unfold wilsonEnergy
  apply continuous_finsetSum
  intro p _
  have h : Continuous (fun U : WilsonConfig l => plaquette U p.1 p.2.val.1 p.2.val.2) := by unfold plaquette; fun_prop
  exact continuous_const.sub ((Complex.continuous_re.comp
    ((continuous_subtype_val.comp (continuous_subtype_val.comp h)).matrix_trace)).div_const _)

def logWeight {l : ℕ+} (β : ℝ) (z : WilsonReplicas l) := -β*(wilsonEnergy z.1 + wilsonEnergy z.2)

theorem logWeight_cont {l : ℕ+} (β : ℝ) : Continuous (logWeight (l := l) β) :=
  continuous_const.mul ((continuous_wilsonEnergy.comp continuous_fst).add (continuous_wilsonEnergy.comp continuous_snd))

/-- Half the change of Wilson log weight from keeping to exchanging the selected links. -/
def exchangeField {l : ℕ+} (β : ℝ) (m : Edge l → Bool) (z : WilsonReplicas l) :=
  (logWeight β z - logWeight β (exchangeLinks m z))/2

theorem exchangeField_cont {l : ℕ+} (β : ℝ) (m : Edge l → Bool) : Continuous (exchangeField β m) :=
  ((logWeight_cont β).sub ((logWeight_cont β).comp (exchange_cont m))).div_const _

theorem replica_integral {l : ℕ+} (β : ℝ) (D : WilsonReplicas l → ℝ) :
    ∫ z, D z ∂replicaLaw l β =
      (∫ z, exp (logWeight β z)*D z ∂(prior l).prod (prior l)) /
        (∫ U, exp (-β*wilsonEnergy U) ∂prior l)^2 := by
  let w := fun U : WilsonConfig l => exp (-β*wilsonEnergy U)
  let Z := ∫ U, w U ∂prior l
  let f := fun U => ENNReal.ofReal (w U/Z)
  have hw : Continuous w := continuous_exp.comp (continuous_const.mul continuous_wilsonEnergy)
  have hZ : 0 < Z := integral_exp_pos (hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hf : Measurable f := (hw.measurable.div_const _).ennreal_ofReal
  change (∫ z, D z ∂((prior l).withDensity f).prod ((prior l).withDensity f)) =
    (∫ z, exp (logWeight β z)*D z ∂(prior l).prod (prior l))/Z^2
  rw [prod_withDensity hf hf, integral_withDensity_eq_integral_toReal_smul]
  · have he (z : WilsonReplicas l) : (f z.1 * f z.2).toReal • D z = exp (logWeight β z)*D z / Z^2 := by
      simp only [f, ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (exp_pos _).le hZ.le), smul_eq_mul,
        w, logWeight, mul_add, exp_add]
      ring
    simp_rw [he]; rw [integral_div]
  · exact (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  · exact .of_forall fun z => ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) (ENNReal.ofReal_lt_top)

theorem replica_tanh_continuous : Continuous Real.tanh := by
  have h : Real.tanh = fun x => sinh x / cosh x := funext tanh_eq_sinh_div_cosh
  rw [h]; exact continuous_sinh.div continuous_cosh fun x => (cosh_pos x).ne'

private theorem tanh_exchange (a b : ℝ) : (exp a + exp b)*tanh ((a-b)/2) = exp a - exp b := by
  have h := PhaseTwo.tanh_quarter_eq (2*(a-b))
  rw [show 2*(a-b)/4 = (a-b)/2 by ring, show 2*(a-b)/2 = a-b by ring, exp_sub] at h
  rw [h]
  field_simp

/-- The orbit calculation works for every finite exchange-invariant prior. -/
theorem weighted_exchange_identity {l : ℕ+} (β : ℝ) (m : Edge l → Bool)
    (μ : Measure (WilsonReplicas l)) [IsFiniteMeasure μ] (hμ : MeasurePreserving (exchangeLinks m) μ μ)
    {D : WilsonReplicas l → ℝ} (hc : Continuous D) (ha : ∀ z, D (exchangeLinks m z) = -D z) :
    (∫ z, exp (logWeight β z)*D z ∂μ) = ∫ z, exp (logWeight β z)*(D z*tanh (exchangeField β m z)) ∂μ := by
  let S := exchangeLinks m
  let f := fun z => exp (logWeight β z)*D z
  let g := fun z => exp (logWeight β z)*(D z*tanh (exchangeField β m z))
  have cf : Continuous f := (continuous_exp.comp (logWeight_cont β)).mul hc
  have cg : Continuous g := (continuous_exp.comp (logWeight_cont β)).mul (hc.mul (replica_tanh_continuous.comp (exchangeField_cont β m)))
  have emb : MeasurableEmbedding S := (show WilsonReplicas l ≃ᵐ WilsonReplicas l from
    ⟨⟨S,S,exchangeLinks_involutive m,exchangeLinks_involutive m⟩,(exchange_cont m).measurable,(exchange_cont m).measurable⟩).measurableEmbedding
  have sym (v : WilsonReplicas l → ℝ) (cv : Continuous v) :
      ∫ z, v z + v (S z) ∂μ = (∫ z, v z ∂μ) + ∫ z, v z ∂μ := by
    have cS : Continuous (fun z => v (S z)) := cv.comp (exchange_cont m)
    rw [integral_add (μ := μ) (cv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (cS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      hμ.integral_comp emb v]
  have hp (z : WilsonReplicas l) : f z + f (S z) = g z + g (S z) := by
    have hflip : exchangeField β m (S z) = -exchangeField β m z := by
      simp only [S,exchangeField,exchangeLinks_involutive m z]; ring
    simp only [f,g,hflip,tanh_neg, S,ha]
    have H := tanh_exchange (logWeight β z) (logWeight β (exchangeLinks m z))
    change (_ + _) * tanh (exchangeField β m z) = _ at H
    linear_combination -D z * H
  have h := integral_congr_ae (μ := μ) (.of_forall hp)
  rw [sym f cf, sym g cg] at h
  linarith only [h]

/-- An antisymmetric observable acquires one signed boundary factor in its
expectation. This is a change of variables under the product Haar prior. -/
theorem replica_exchange_identity {l : ℕ+} (β : ℝ) (m : Edge l → Bool) {D : WilsonReplicas l → ℝ}
    (hc : Continuous D) (ha : ∀ z, D (exchangeLinks m z) = -D z) :
    (∫ z, D z ∂replicaLaw l β) = ∫ z, D z * tanh (exchangeField β m z) ∂replicaLaw l β := by
  rw [replica_integral,replica_integral,weighted_exchange_identity β m _ (exchange_preserving m) hc ha]

def replicaDifference {l : ℕ+} (F G : WilsonConfig l → ℝ) (z : WilsonReplicas l) :=
  (F z.1-F z.2)*(G z.1-G z.2)

theorem twice_wilsonCovariance {l : ℕ+} (β : ℝ) {F G : WilsonConfig l → ℝ}
    (hF : Continuous F) (hG : Continuous G) :
    2*wilsonCovariance β F G = ∫ z, replicaDifference F G z ∂replicaLaw l β := by
  haveI := wilson_probability l β
  let μ : Measure (WilsonConfig l) := law l β
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  haveI : IsFiniteMeasure μ := ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
  haveI : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  haveI : SFinite μ := inferInstance
  have hi {f : WilsonReplicas l → ℝ} (hf : Continuous f) : Integrable f (μ.prod μ) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let H := fun z : WilsonReplicas l => F z.1*G z.1 + F z.2*G z.2 - (F z.1*G z.2 + F z.2*G z.1)
  have e (z : WilsonReplicas l) : replicaDifference F G z = H z := by dsimp [replicaDifference,H]; ring
  simp_rw [e]; unfold H
  change _ = ∫ z, _ ∂μ.prod μ
  rw [integral_sub (hi (by fun_prop)) (hi (by fun_prop)), integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    integral_add (hi (by fun_prop)) (hi (by fun_prop))]
  have hswap : (∫ z : WilsonReplicas l, F z.2*G z.1 ∂μ.prod μ) = ∫ z : WilsonReplicas l, G z.1*F z.2 ∂μ.prod μ :=
    integral_congr_ae (.of_forall fun _ => mul_comm ..)
  rw [hswap, integral_prod_mul (μ := μ) (ν := μ) F G, integral_prod_mul (μ := μ) (ν := μ) G F]
  rw [integral_fun_fst (μ := μ) (ν := μ) (fun u => F u * G u), integral_fun_snd (μ := μ) (ν := μ) (fun u => F u * G u)]
  simp only [probReal_univ, one_smul, wilsonCovariance, μ]
  ring

#print axioms replica_exchange_identity
#print axioms twice_wilsonCovariance
end
end YangMills.PeriodicWilson
