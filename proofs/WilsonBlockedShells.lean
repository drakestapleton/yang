-- SPDX-License-Identifier: Apache-2.0
import WilsonBlocking

namespace YangMills.PeriodicWilson
open FundamentalSU2 PhaseTwo UfbiBridge MeasureTheory Real Filter Set
open scoped Topology
noncomputable section

/-- A signed finite linear combination of retained spatial loop correlations. -/
def blockedLoopSum (b : ℕ+) {l : ℕ+} (β : ℝ) (c : Face l × Face l → ℝ) : ℝ :=
  ∑ a, c a * blockedCovariance b β (wilsonPlaquetteTrace a.1) (wilsonPlaquetteTrace a.2)

def spatialLoopShell {l : ℕ+} (t : Axis) (k : ℕ) (c : Face l × Face l → ℝ) : Prop :=
  ∀ p q, c (p,q) ≠ 0 →
    t ≠ p.2.val.1 ∧ t ≠ p.2.val.2 ∧ t ≠ q.2.val.1 ∧ t ≠ q.2.val.2 ∧
    k ≤ (q.1 t-p.1 t).valMinAbs.natAbs

/-- Translate a face through k coarse lattice spacings along the time axis. -/
def translateFace {l : ℕ+} (t : Axis) (k : ℕ) (p : Face l) : Face l :=
  (p.1 + k • Pi.single t 1, p.2)

theorem translateFace_distance {l : ℕ+} (t : Axis) (k : ℕ) (p : Face l) (hfit : 2*k ≤ l.val) :
    (((translateFace t k p).1 t-p.1 t).valMinAbs).natAbs = k := by
  have hpos : 0 < l.val := l.prop
  have hlt : k < l.val := by omega
  change (((p.1 t + k • ((Pi.single t 1 : Site l) t)) - p.1 t).valMinAbs).natAbs = k
  rw [Pi.single_eq_same, nsmul_eq_mul, mul_one, add_sub_cancel_left,
    ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast_of_lt hlt, min_eq_left]
  omega

/-- An explicit shell observable for every torus of diameter at least k.
An antipodal translation at exactly half the side is included. -/
theorem translatedPlaquette_clustering (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (t : Axis) (k : ℕ) (hfit : 2*k ≤ l.val)
    (p : Face l) (hi : t ≠ p.2.val.1) (hj : t ≠ p.2.val.2) :
    |blockedCovariance b β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace (translateFace t k p))| ≤
      (4*b.val*π^2/(1-straightRow β))*(straightRow β ^ b.val)^k := by
  have H := blockedWilson_plaquette_clustering b hl hβ hwindow t p (translateFace t k p) hi hj hi hj
  rwa [translateFace_distance t k p hfit] at H

theorem blockedLoopSum_bound (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) {β βmax A : ℝ}
    (hβ : β ∈ Icc 0 βmax) (hwindow : βmax < sqrt 3/18)
    (t : Axis) (k : ℕ) (c : Face l × Face l → ℝ)
    (hs : spatialLoopShell t k c) (hA : ∑ a, |c a| ≤ A) :
    |blockedLoopSum b β c| ≤ (A*(4*b.val*π^2/(1-straightRow βmax)))*(straightRow βmax ^ b.val)^k := by
  have hnn : 0 ≤ straightRow β := div_nonneg (mul_nonneg (by norm_num) hβ.1) (sqrt_nonneg _)
  have hr : straightRow β ≤ straightRow βmax := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hβ.2 (by norm_num)) (sqrt_nonneg _)
  have hmax := straightRow_subunit.2 hwindow
  let P := 4*(b.val : ℝ)*π^2/(1-straightRow βmax)
  let α := straightRow βmax ^ b.val
  have hP : 0 ≤ P := div_nonneg (by positivity) (sub_nonneg.mpr hmax.le)
  have hα : 0 ≤ α := pow_nonneg (hnn.trans hr) _
  have hα1 : α ≤ 1 := pow_le_one₀ (hnn.trans hr) hmax.le
  have hb (p q : Face l) (H : c (p,q) ≠ 0) :
      |blockedCovariance b β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)| ≤ P * α^k := by
    obtain ⟨hi,hj,hi',hj',hk⟩ := hs p q H
    apply (blockedWilson_plaquette_clustering b hl hβ.1 (hβ.2.trans_lt hwindow) t p q hi hj hi' hj').trans
    apply mul_le_mul _ _ (pow_nonneg (pow_nonneg hnn _) _) hP
    · exact div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hmax) (sub_le_sub_left hr _)
    · exact (pow_le_pow_left₀ (pow_nonneg hnn _) (pow_le_pow_left₀ hnn hr _) _).trans
        (pow_le_pow_of_le_one hα hα1 hk)
  calc
    |blockedLoopSum b β c| ≤ ∑ a, |c a * blockedCovariance b β (wilsonPlaquetteTrace a.1) (wilsonPlaquetteTrace a.2)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ a, |c a| * (P*α^k) := by
      apply Finset.sum_le_sum
      rintro ⟨p,q⟩ _
      by_cases H : c (p,q) = 0
      · simp [H]
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb p q H) (abs_nonneg _)
    _ ≤ A*(P*α^k) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hA (mul_nonneg hP (pow_nonneg hα _))
    _ = _ := (mul_assoc ..).symm

/-- The continuum input is a statewise spectral identification. For each
fixed shell k, the separation and coefficient bound are required only on
sufficiently large tori. The coarse clock is bR. -/
theorem blockedWilson_gap_of_loop_limits {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    (b : ℕ+) (t : Axis) {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax) (hwindow : βmax < sqrt 3/18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val) (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Icc 0 βmax)
    (hlimit : ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
      ∃ (A : ℝ) (c : (n k : ℕ) → Face (l n) × Face (l n) → ℝ), 0 ≤ A ∧
        (∀ k, ∀ᶠ n in atTop, spatialLoopShell t k (c n k) ∧ ∑ a, |c n k a| ≤ A) ∧
        ∀ k : ℕ, Tendsto (fun n => blockedLoopSum b (β n) (c n k)) atTop
          (𝓝 (∫ p, exp (-((k:ℝ)*(b.val*R))*YangMills.time p) ∂(T.energyMomentum.diagonal ψ)))) :
    HasRelativisticMassGap T ((1/R)*log (1/straightRow βmax)) := by
  let α := straightRow βmax
  have hα : 0 < α := div_pos (mul_pos (by norm_num) hpos) (by positivity)
  have hα1 : α < 1 := straightRow_subunit.2 hwindow
  have hb : (0:ℝ) < b.val := by exact_mod_cast b.prop
  have rate : (1/(b.val*R))*log (1/α^b.val) = (1/R)*log (1/α) := by
    simp only [one_div, log_inv]
    simpa only [div_eq_inv_mul] using block_physical_rate b α R hR
  rw [← rate]
  apply eventual_shell_envelopes_imply_relativistic_mass_gap T hW0 hW1 hW2
    (mul_pos hb hR) (pow_pos hα b.val) (pow_lt_one₀ hα.le hα1 (Nat.ne_of_gt b.prop))
  intro ψ hψ
  obtain ⟨A,c,hA,hs,hspec⟩ := hlimit ψ hψ
  refine ⟨A*(4*b.val*π^2/(1-α)),fun n k => blockedLoopSum b (β n) (c n k),?_,hspec,?_⟩
  · exact mul_nonneg hA (div_nonneg (by positivity) (sub_nonneg.mpr hα1.le))
  · intro k
    filter_upwards [hs k] with n h
    exact (le_abs_self _).trans (blockedLoopSum_bound b (hl n) (hβ n) hwindow t k (c n k) h.1 h.2)

#print axioms translatedPlaquette_clustering
#print axioms blockedLoopSum_bound
#print axioms blockedWilson_gap_of_loop_limits
end
end YangMills.PeriodicWilson
