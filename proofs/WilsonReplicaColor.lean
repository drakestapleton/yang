-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaEndpoint

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real
noncomputable section

/-- Relative color orientation of the second Wilson replica. -/
def rotateReplica {l : ℕ+} (h : gaugeGroup.image) (z : WilsonReplicas l) : WilsonReplicas l :=
  (z.1,gaugeAct (fun _ => h) z.2)

private theorem rotate_cont {l : ℕ+} (h : gaugeGroup.image) : Continuous (rotateReplica (l := l) h) := by
  apply continuous_fst.prodMk
  apply continuous_pi; intro e
  change Continuous (fun z : WilsonReplicas l => h * z.2 e * h⁻¹)
  fun_prop

private theorem rotate_preserving {l : ℕ+} (β : ℝ) (h : gaugeGroup.image) :
    MeasurePreserving (rotateReplica h) (replicaLaw l β) (replicaLaw l β) := by
  let μ := wilsonLaw gaugeGroup l β su2Haar
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  have cm : Continuous (gaugeAct (l := l) (fun _ => h)) := by
    apply continuous_pi; intro e
    change Continuous (fun U : WilsonConfig l => h*U e*h⁻¹); fun_prop
  have hg : MeasurePreserving (gaugeAct (fun _ => h)) μ μ := ⟨cm.measurable,PhaseFour.wilsonLaw_map_gaugeAct β su2Haar _⟩
  exact (MeasurePreserving.id μ).prod hg

/-- In an Abelian configuration all internal conjugations fix the observable
pair pointwise. Equivalently, it suffices that the second replica commutes with h. -/
theorem rotateReplica_eq_of_commute {l : ℕ+} (h : gaugeGroup.image) (z : WilsonReplicas l)
    (hc : ∀ e, Commute h (z.2 e)) : rotateReplica h z = z := by
  refine Prod.ext ?_ ?_
  · rfl
  funext e
  change h * z.2 e * h⁻¹ = z.2 e
  rw [(hc e).eq,mul_assoc,mul_inv_cancel,mul_one]

/-- Average the signed exchange estimator before taking absolute values. Any
finite list of relative orientations works, including repeated elements. -/
def colorAverage {l : ℕ+} {ι : Type*} [Fintype ι] (colors : ι → gaugeGroup.image)
    (Q : WilsonReplicas l → ℝ) (z : WilsonReplicas l) :=
  (∑ i, Q (rotateReplica (colors i) z)) / Fintype.card ι

theorem colorAverage_abs_le {l : ℕ+} {ι : Type*} [Fintype ι] (colors : ι → gaugeGroup.image)
    (Q : WilsonReplicas l → ℝ) (z : WilsonReplicas l) :
    |colorAverage colors Q z| ≤ colorAverage colors (fun w => |Q w|) z := by
  rw [colorAverage,colorAverage,abs_div,abs_of_nonneg (show (0:ℝ) ≤ Fintype.card ι from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem colorAverage_eq_of_commute {l : ℕ+} {ι : Type*} [Fintype ι] [Nonempty ι]
    (colors : ι → gaugeGroup.image) (Q : WilsonReplicas l → ℝ) (z : WilsonReplicas l)
    (hc : ∀ i e, Commute (colors i) (z.2 e)) : colorAverage colors Q z = Q z := by
  have h (i : ι) := rotateReplica_eq_of_commute (colors i) z (hc i)
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [colorAverage,h,hn]

theorem colorAverage_integral {l : ℕ+} {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (colors : ι → gaugeGroup.image) {D Q : WilsonReplicas l → ℝ}
    (cD : Continuous D) (cQ : Continuous Q) (fixed : ∀ i z, D (rotateReplica (colors i) z) = D z) :
    (∫ z, D z * colorAverage colors Q z ∂replicaLaw l β) = ∫ z, D z * Q z ∂replicaLaw l β := by
  let A := fun i z => D z * Q (rotateReplica (colors i) z)
  let I := ∫ z, D z * Q z ∂replicaLaw l β
  have ca (i : ι) : Continuous (A i) := cD.mul (cQ.comp (rotate_cont _))
  have eq (i : ι) : (∫ z, A i z ∂replicaLaw l β) = I := by
    have hp := rotate_preserving (l := l) β (colors i)
    have c : Continuous (fun z => D z * Q z) := cD.mul cQ
    have h := integral_map hp.measurable.aemeasurable (c.aestronglyMeasurable (μ := (replicaLaw l β).map (rotateReplica (colors i))))
    rw [hp.map_eq] at h
    simpa only [A,I,fixed] using h.symm
  have factor (z : WilsonReplicas l) : D z * colorAverage colors Q z = (∑ i, A i z)/(Fintype.card ι : ℝ) := by
    rw [colorAverage,mul_div_assoc',Finset.mul_sum]
  have hi (i : ι) : Integrable (A i) (replicaLaw l β) := (ca i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [factor]; rw [integral_div,integral_finsetSum _ fun i _ => hi i]
  simp_rw [eq]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hn,I]

/-- A signed relative-color average has a rigorous absolute-value bound. -/
theorem colorAverage_bound {l : ℕ+} {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (colors : ι → gaugeGroup.image) {D Q : WilsonReplicas l → ℝ}
    (cD : Continuous D) (cQ : Continuous Q) (fixed : ∀ i z, D (rotateReplica (colors i) z) = D z) :
    |∫ z, D z * Q z ∂replicaLaw l β| ≤ ∫ z, |D z| * |colorAverage colors Q z| ∂replicaLaw l β := by
  rw [← colorAverage_integral β colors cD cQ fixed]
  simpa only [abs_mul] using (abs_integral_le_integral_abs (μ := replicaLaw l β) (f := fun z => D z * colorAverage colors Q z))

theorem endpoint_color_bound {l : ℕ+} {ι : Type*} [Fintype ι] [Nonempty ι]
    (colors : ι → gaugeGroup.image) (P : PinnedFrame l) (hl : 1 < l.val) (β : ℝ)
    (p q : Face l) (e f : Edge l) (he : e ∈ faceEdges p) (hf : f ∈ faceEdges q)
    (pe : ∀ a ∈ faceEdges p, a ≠ e → a ∈ P.edges) (qf : ∀ a ∈ faceEdges q, a ≠ f → a ∈ P.edges)
    (pq : Disjoint (faceEdges p) (faceEdges q))
    (cut : ∀ a : Face l, uniformOnFace (faceMask p) a ∨ uniformOnFace (faceMask q) a) :
    |wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)| ≤
      (∫ z, |replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) z| *
        |colorAverage colors (fun w => tanh (stapleExchange β e (P.pair w)) *
          tanh (stapleExchange β f (P.pair w))) z| ∂replicaLaw l β)/2 := by
  let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
  let Q := fun w => tanh (stapleExchange β e (P.pair w)) * tanh (stapleExchange β f (P.pair w))
  have cF := (wilsonPlaquetteTrace_variation p).continuous
  have cG := (wilsonPlaquetteTrace_variation q).continuous
  have cD : Continuous D := ((cF.comp continuous_fst).sub (cF.comp continuous_snd)).mul
    ((cG.comp continuous_fst).sub (cG.comp continuous_snd))
  have one (a : Edge l) : Continuous (fun w => tanh (stapleExchange β a (P.pair w))) := by
    simp_rw [← singleLink_exchange hl]
    exact replica_tanh_continuous.comp ((exchangeField_cont β _).comp P.pair_cont)
  have fixed (i : ι) (z : WilsonReplicas l) : D (rotateReplica (colors i) z) = D z := by
    simp [D,rotateReplica,replicaDifference,wilsonPlaquetteTrace_gauge_invariant]
  have H := colorAverage_bound β colors cD (show Continuous Q from (one e).mul (one f)) fixed
  have eq := endpoint_covariance_identity P hl β p q e f he hf pe qf pq cut
  change 2*_ = ∫ z, D z * Q z ∂replicaLaw l β at eq
  rw [← eq,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at H
  change _ ≤ (∫ z, |D z| * |colorAverage colors Q z| ∂replicaLaw l β)/2
  linarith only [H]

#print axioms colorAverage_abs_le
#print axioms colorAverage_eq_of_commute
#print axioms endpoint_color_bound
#print axioms rotateReplica_eq_of_commute
#print axioms colorAverage_integral
#print axioms colorAverage_bound
end
end YangMills.PeriodicWilson
