-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaExchange

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real
noncomputable section

def faceEdges {l : ℕ+} (p : Face l) : Finset (Edge l) :=
  {(corners p).1,(corners p).2.1,(corners p).2.2.1,(corners p).2.2.2}

def uniformOnFace {l : ℕ+} (m : Edge l → Bool) (p : Face l) : Prop :=
  ∃ b : Bool, ∀ e ∈ faceEdges p, m e = b

def faceScore {l : ℕ+} (p : Face l) (z : WilsonReplicas l) :=
  wilsonPlaquetteTrace p z.1 + wilsonPlaquetteTrace p z.2

theorem trace_agrees {l : ℕ+} (p : Face l) (U V : WilsonConfig l)
    (h : ∀ e ∈ faceEdges p, U e = V e) : wilsonPlaquetteTrace p U = wilsonPlaquetteTrace p V := by
  apply congrArg (fun u : gaugeGroup.image => (suMat u).trace.re / 2)
  change U (corners p).1 * (U (corners p).2.1 * ((U (corners p).2.2.1)⁻¹ * (U (corners p).2.2.2)⁻¹)) =
    V (corners p).1 * (V (corners p).2.1 * ((V (corners p).2.2.1)⁻¹ * (V (corners p).2.2.2)⁻¹))
  rw [h _ (by simp [faceEdges]),h _ (by simp [faceEdges]),h _ (by simp [faceEdges]),h _ (by simp [faceEdges])]

private theorem uniform_score {l : ℕ+} (m : Edge l → Bool) (p : Face l) (h : uniformOnFace m p) (z : WilsonReplicas l) :
    faceScore p (exchangeLinks m z) = faceScore p z := by
  obtain ⟨b,hb⟩ := h
  cases b
  · exact congrArg₂ (·+·) (trace_agrees p _ z.1 fun e he => by simp [exchangeLinks,hb e he])
      (trace_agrees p _ z.2 fun e he => by simp [exchangeLinks,hb e he])
  · exact (congrArg₂ (·+·) (trace_agrees p _ z.2 fun e he => by simp [exchangeLinks,hb e he])
      (trace_agrees p _ z.1 fun e he => by simp [exchangeLinks,hb e he])).trans (add_comm ..)

private theorem energy_sum {l : ℕ+} (U : WilsonConfig l) : wilsonEnergy U = ∑ p : Face l, (1-wilsonPlaquetteTrace p U) := rfl

/-- The complete exchange field is a signed sum of plaquette defects.
A face contributes zero whenever all four links receive the same swap. -/
theorem exchangeField_eq_sum {l : ℕ+} (β : ℝ) (m : Edge l → Bool) (z : WilsonReplicas l) :
    exchangeField β m z = (β/2) * ∑ p : Face l, (faceScore p z - faceScore p (exchangeLinks m z)) := by
  change (-β*(wilsonEnergy z.1 + wilsonEnergy z.2) -
    -β*(wilsonEnergy (exchangeLinks m z).1 + wilsonEnergy (exchangeLinks m z).2))/2 = _
  simp only [energy_sum,faceScore,Finset.sum_sub_distrib,Finset.sum_add_distrib]; ring

theorem exchangeField_stable {l : ℕ+} (β : ℝ) (m n : Edge l → Bool)
    (hd : ∀ p : Face l, uniformOnFace m p ∨ uniformOnFace n p) (z : WilsonReplicas l) :
    exchangeField β m (exchangeLinks n z) = exchangeField β m z := by
  rw [exchangeField_eq_sum, exchangeField_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rcases hd p with h | h
  · simp only [uniform_score m p h, sub_self]
  · rw [exchangeLinks_commute m n,uniform_score n p h,uniform_score n p h]

theorem shell_identity_of_exchange {l : ℕ+} (β : ℝ) (ν : Measure (WilsonReplicas l))
    (exchange : ∀ m {H : WilsonReplicas l → ℝ}, Continuous H → (∀ z, H (exchangeLinks m z) = -H z) →
      (∫ z, H z ∂ν) = ∫ z, H z * tanh (exchangeField β m z) ∂ν) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Edge l → Bool) {D : WilsonReplicas l → ℝ} (hc : Continuous D)
    (ha : ∀ i ∈ s, ∀ z, D (exchangeLinks (m i) z) = -D z)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ p : Face l, uniformOnFace (m i) p ∨ uniformOnFace (m j) p) :
    (∫ z, D z ∂ν) = ∫ z, D z * ∏ i ∈ s, tanh (exchangeField β (m i) z) ∂ν := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let H := fun z => D z * ∏ j ∈ s, tanh (exchangeField β (m j) z)
    have cH : Continuous H := hc.mul (continuous_finsetProd _ fun j _ => replica_tanh_continuous.comp (exchangeField_cont β (m j)))
    have hH (z : WilsonReplicas l) : H (exchangeLinks (m i) z) = -H z := by
      have hprod : ∀ j ∈ s, exchangeField β (m j) (exchangeLinks (m i) z) = exchangeField β (m j) z := by
        intro j hj
        exact exchangeField_stable β _ _ (hd j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self ..)
          (fun eq => hi (eq ▸ hj))) z
      simp only [H,ha i (Finset.mem_insert_self ..) z,neg_mul]
      rw [Finset.prod_congr rfl fun j hj => congrArg tanh (hprod j hj)]
    rw [ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))]
    change (∫ z, H z ∂ν) = _
    rw [exchange (m i) cH hH]
    apply integral_congr_ae
    exact .of_forall fun z => by simp [H,Finset.prod_insert hi]; ring

/-- Exact multi-shell identity for the full Wilson measure, at any coupling.
Different exchange surfaces may share links; no plaquette may be split
by both. The signed factors retain the actual neighboring configurations. -/
theorem replica_shell_identity {l : ℕ+} (β : ℝ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Edge l → Bool) {D : WilsonReplicas l → ℝ} (hc : Continuous D)
    (ha : ∀ i ∈ s, ∀ z, D (exchangeLinks (m i) z) = -D z)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ p : Face l, uniformOnFace (m i) p ∨ uniformOnFace (m j) p) :
    (∫ z, D z ∂replicaLaw l β) = ∫ z, D z * ∏ i ∈ s, tanh (exchangeField β (m i) z) ∂replicaLaw l β :=
  shell_identity_of_exchange β _ (replica_exchange_identity β) s m hc ha hd

theorem replica_covariance_bound_of_integral {l : ℕ+} (β : ℝ) (ν : Measure (WilsonReplicas l)) [IsFiniteMeasure ν] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Edge l → Bool) {F G : WilsonConfig l → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hbF : ∀ U, |F U| ≤ 1) (hbG : ∀ U, |G U| ≤ 1)
    (eq : 2*wilsonCovariance β F G = ∫ z, replicaDifference F G z *
      ∏ i ∈ s, tanh (exchangeField β (m i) z) ∂ν) :
    |wilsonCovariance β F G| ≤ 2 * ∫ z, ∏ i ∈ s, |tanh (exchangeField β (m i) z)| ∂ν := by
  let Q := fun z : WilsonReplicas l => ∏ i ∈ s, tanh (exchangeField β (m i) z)
  have cQ : Continuous Q := continuous_finsetProd _ fun i _ => replica_tanh_continuous.comp (exchangeField_cont β (m i))
  have cD : Continuous (replicaDifference F G) := ((hF.comp continuous_fst).sub (hF.comp continuous_snd)).mul
    ((hG.comp continuous_fst).sub (hG.comp continuous_snd))
  have hD (z : WilsonReplicas l) : |replicaDifference F G z| ≤ 4 := by
    have cap (f : WilsonConfig l → ℝ) (hf : ∀ U, |f U| ≤ 1) : |f z.1-f z.2| ≤ 2 := by
      apply (abs_sub _ _).trans
      linarith [hf z.1,hf z.2]
    rw [replicaDifference,abs_mul]
    exact (mul_le_mul (cap F hbF) (cap G hbG) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hi {f : WilsonReplicas l → ℝ} (hf : Continuous f) : Integrable f ν :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have H : |2*wilsonCovariance β F G| ≤ 4 * ∫ z, |Q z| ∂ν := by
    rw [eq, ← integral_const_mul]
    apply abs_integral_le_integral_abs.trans
    exact integral_mono (hi (cD.mul cQ).abs) (hi (continuous_const.mul cQ.abs)) fun z =>
      (abs_mul ..).le.trans (mul_le_mul_of_nonneg_right (hD z) (abs_nonneg _))
  simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),Q,Finset.abs_prod] at H
  linarith

/-- An operational correlation bound. The right side is a single equilibrium
expectation of measured exchange fields, with all correlations between shells retained. -/
theorem replica_covariance_bound {l : ℕ+} (β : ℝ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Edge l → Bool) {F G : WilsonConfig l → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hbF : ∀ U, |F U| ≤ 1) (hbG : ∀ U, |G U| ≤ 1)
    (ha : ∀ i ∈ s, ∀ z, replicaDifference F G (exchangeLinks (m i) z) = -replicaDifference F G z)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ p : Face l, uniformOnFace (m i) p ∨ uniformOnFace (m j) p) :
    |wilsonCovariance β F G| ≤ 2 * ∫ z, ∏ i ∈ s, |tanh (exchangeField β (m i) z)| ∂replicaLaw l β := by
  have cD : Continuous (replicaDifference F G) := ((hF.comp continuous_fst).sub (hF.comp continuous_snd)).mul
    ((hG.comp continuous_fst).sub (hG.comp continuous_snd))
  have eq := (twice_wilsonCovariance β hF hG).trans (replica_shell_identity β s m cD ha hd)
  exact replica_covariance_bound_of_integral β _ s m hF hG hbF hbG eq

#print axioms exchangeField_stable
#print axioms replica_shell_identity
#print axioms replica_covariance_bound
end
end YangMills.PeriodicWilson
