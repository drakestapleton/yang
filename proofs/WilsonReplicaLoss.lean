-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaSlabs

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real
noncomputable section

def shellWeight {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ) (z : WilsonReplicas l) : ℝ :=
  ∏ r ∈ Finset.range k, |tanh (exchangeField β (slabMask t s r) z)|

private theorem shellWeight_cont {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ) :
    Continuous (shellWeight β t s k) :=
  continuous_finsetProd _ fun r _ => (replica_tanh_continuous.comp (exchangeField_cont β (slabMask t s r))).abs

/-- Loss of the next shell, weighted by the survival of every preceding shell. -/
def slabLoss {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ)
    (ν : Measure (WilsonReplicas l) := replicaLaw l β) :=
  ∫ z, shellWeight β t s k z * (1 - |tanh (exchangeField β (slabMask t s k) z)|) ∂ν

theorem slabMoment_succ {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ)
    (ν : Measure (WilsonReplicas l) := replicaLaw l β) [IsFiniteMeasure ν] :
    slabMoment β t s (k+1) ν = slabMoment β t s k ν - slabLoss β t s k ν := by
  let W := shellWeight β t s k
  let A := fun z => |tanh (exchangeField β (slabMask t s k) z)|
  have cW := shellWeight_cont β t s k
  have cA : Continuous A := (replica_tanh_continuous.comp (exchangeField_cont β _)).abs
  change (∫ z, _ ∂ν) = (∫ z, W z ∂_) - ∫ z, W z * (1 - A z) ∂_
  have cL : Continuous (fun z => W z * (1 - A z)) := cW.mul (continuous_const.sub cA)
  rw [← integral_sub (μ := ν) (cW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (cL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  exact .of_forall fun z => by simp only [Finset.prod_range_succ,W,shellWeight,A]; ring

/-- A finite test event. Its mass includes the preceding shell weights. -/
def moderateShellMass {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ) (q : ℝ)
    (ν : Measure (WilsonReplicas l) := replicaLaw l β) :=
  ∫ z in {z : WilsonReplicas l | |tanh (exchangeField β (slabMask t s k) z)| ≤ q},
    shellWeight β t s k z ∂ν

theorem moderateShellMass_le_loss {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ) (q : ℝ)
    (ν : Measure (WilsonReplicas l) := replicaLaw l β) [IsFiniteMeasure ν] :
    (1-q) * moderateShellMass β t s k q ν ≤ slabLoss β t s k ν := by
  let W := shellWeight β t s k
  let A := fun z => |tanh (exchangeField β (slabMask t s k) z)|
  let E := {z : WilsonReplicas l | A z ≤ q}
  have cW := shellWeight_cont β t s k
  have cA : Continuous A := (replica_tanh_continuous.comp (exchangeField_cont β _)).abs
  have mE : MeasurableSet E := isClosed_le cA continuous_const |>.measurableSet
  have hi {f : WilsonReplicas l → ℝ} (hf : Continuous f) : Integrable f ν :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (1-q) * (∫ z in E, W z ∂_) ≤ ∫ z, W z * (1-A z) ∂_
  rw [← integral_const_mul, ← integral_indicator mE]
  apply integral_mono ((hi (continuous_const.mul cW)).indicator mE) (hi (cW.mul (continuous_const.sub cA)))
  intro z
  have hw : 0 ≤ W z := Finset.prod_nonneg fun _ _ => abs_nonneg _
  by_cases hz : z ∈ E
  · rw [Set.indicator_of_mem hz, mul_comm]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hz _) hw
  · rw [Set.indicator_of_notMem hz]
    exact mul_nonneg hw (sub_nonneg.mpr (abs_tanh_lt_one _).le)

/-- Each shell can have a different certified loss budget. The budgets add in
the exponent even when the measured shell fields are dependent. -/
theorem slabMoment_le_exp_of_loss {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val)
    (a : ℕ → ℝ) (k : ℕ)
    (ν : Measure (WilsonReplicas l)) [IsProbabilityMeasure ν]
    (h : ∀ j < k, (1-exp (-a j))*slabMoment β t s j ν ≤ slabLoss β t s j ν) :
    slabMoment β t s k ν ≤ exp (-(∑ j ∈ Finset.range k, a j)) := by
  induction k with
  | zero => simp [slabMoment]
  | succ k ih =>
    have h0 := ih (fun j hj => h j (by omega))
    have h1 := h k (by omega)
    rw [slabMoment_succ β t s k ν,Finset.sum_range_succ,neg_add,exp_add]
    exact (show slabMoment β t s k ν - slabLoss β t s k ν ≤ slabMoment β t s k ν * exp (-a k) by nlinarith).trans
      (mul_le_mul_of_nonneg_right h0 (exp_pos _).le)

/-- R is the fine spacing. A weighted moderate-field estimate paying m R per
fine shell supplies physical rate m for blocked products at the actual beta. -/
theorem blockedProduct_physical_bound_of_overlap {l : ℕ+} (hl : 1 < l.val) (b : ℕ+) (β m R : ℝ)
    (t : Axis) (s u : ZMod l.val) (ps qs : List (Face l))
    (hp : spatialSlice t s ps) (hq : spatialSlice t u qs) (q : ℕ → ℝ)
    (h : ∀ j < b.val*cyclicDistance (l := l) s u,
      (1-exp (-(m*R))) * slabMoment β t (blockCoordinate b l s) j ≤
        (1-q j) * moderateShellMass β t (blockCoordinate b l s) j (q j)) :
    |blockedCovariance b β (plaquetteProduct ps) (plaquetteProduct qs)| ≤
      2*exp (-((b.val*cyclicDistance (l := l) s u : ℕ) : ℝ)*(m*R)) := by
  apply (blockedProduct_replica_bound hl b β t s u ps qs hp hq).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have H := slabMoment_le_exp_of_loss β t (blockCoordinate b l s) (fun _ => m*R) _ _
    (fun j hj => (h j hj).trans (moderateShellMass_le_loss β t _ j _))
  simpa [neg_mul] using H

/-- Physical overlap criterion after pinning a forest in each fine replica. -/
theorem framed_blockedProduct_physical_bound_of_overlap {l : ℕ+} (hl : 1 < l.val) (b : ℕ+) (β m R : ℝ) (P : PinnedFrame (b*l))
    (t : Axis) (s u : ZMod l.val) (ps qs : List (Face l))
    (hp : spatialSlice t s ps) (hq : spatialSlice t u qs) (q : ℕ → ℝ)
    (h : ∀ j < b.val*cyclicDistance (l := l) s u,
      (1-exp (-(m*R))) * slabMoment β t (blockCoordinate b l s) j (P.framedLaw β) ≤
        (1-q j) * moderateShellMass β t (blockCoordinate b l s) j (q j) (P.framedLaw β)) :
    |blockedCovariance b β (plaquetteProduct ps) (plaquetteProduct qs)| ≤
      2*exp (-((b.val*cyclicDistance (l := l) s u : ℕ) : ℝ)*(m*R)) := by
  apply (framed_blockedProduct_replica_bound hl b β P t s u ps qs hp hq).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have H := slabMoment_le_exp_of_loss β t (blockCoordinate b l s) (fun _ => m*R) _ (P.framedLaw β)
    (fun j hj => (h j hj).trans (moderateShellMass_le_loss β t _ j _ (P.framedLaw β)))
  simpa [neg_mul] using H

#print axioms framed_blockedProduct_physical_bound_of_overlap
#print axioms slabMoment_succ
#print axioms moderateShellMass_le_loss
#print axioms blockedProduct_physical_bound_of_overlap
end
end YangMills.PeriodicWilson
