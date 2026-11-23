-- SPDX-License-Identifier: Apache-2.0
import WilsonCartesianTransport

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Filter Real PhaseTwo UfbiBridge
open scoped ENNReal Topology Matrix.Norms.Frobenius
noncomputable section

/-- Uniform row bound in the round metric, independent of the periodic volume. -/
def periodicRow (β : ℝ) := 18 * β * sqrt (1/12 + π^2/16)

private theorem incidence_profile {l : ℕ+} (e : Edge l) (d : Edge l → ℝ) :
    (∑ a : Edge l, (neighborIncidenceCount e a : ℝ) * d a) =
      ∑ i ∈ incidences e, d (neighbor e i.1 i.2).1 := by
  simp only [neighborIncidenceCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

/-- The same matrix used for propagation bounds the full conditional law even
when several neighbors change at once. -/
private theorem heatBath_influence_of_field_bound {C : ℝ} (hC₀ : 0 ≤ C)
    (hField : ∀ {r s : ℝ}, 0 ≤ r → 0 ≤ s → ∀ k j : gaugeGroup.image,
      linkWassersteinSq (poleLaw r k) (poleLaw s j) ≤ ENNReal.ofReal (C * ‖r • linkCoordinates k-s • linkCoordinates j‖^2)) {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal
      ((∑ a : Edge l, (sqrt C * β * (neighborIncidenceCount e a : ℝ)) * linkGeodesic (U a) (V a))^2) := by
  apply (periodic_neighbors_of_field_bound hC₀ hField hl hβ U V e).trans (ENNReal.ofReal_le_ofReal ?_)
  let d := fun a => linkGeodesic (U a) (V a)
  let L := sqrt C * β
  have he : (∑ a : Edge l, (sqrt C * β * (neighborIncidenceCount e a : ℝ)) * d a) =
      L * ∑ i ∈ incidences e, d (neighbor e i.1 i.2).1 := by
    simp only [mul_assoc,← Finset.mul_sum,incidence_profile,L]
  change _ ≤ (∑ a : Edge l, (sqrt C * β * (neighborIncidenceCount e a : ℝ)) * d a)^2
  rw [he]
  have hL : 0 ≤ L := mul_nonneg (sqrt_nonneg _) hβ
  let chord := fun a : Edge l => linkChord (U a) (V a) / sqrt 2
  let S := ∑ i ∈ incidences e, chord (neighbor e i.1 i.2).1
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (sqrt_nonneg _)
  have hdist : S ≤ ∑ i ∈ incidences e, d (neighbor e i.1 i.2).1 :=
    Finset.sum_le_sum fun i _ => normalized_chord_le_geodesic (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1)
  calc C*(β*S)^2 = (L*S)^2 := by
          simp only [L,mul_pow,Real.sq_sqrt hC₀]; ring
       _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hL hS) (mul_le_mul_of_nonneg_left hdist hL) 2

/-- The same matrix used for propagation bounds the full conditional law even
when several neighbors change at once. -/
theorem heatBath_influence_sum {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal
      ((∑ a : Edge l, meanSquareInfluence β e a * linkGeodesic (U a) (V a))^2) :=
  heatBath_influence_of_field_bound (by positivity) cartesian_field_mean_square hl hβ U V e

/-- Uniform control of the weight of all length-k paths of periodic heat-bath
influence. The initial profile may depend on the volume and on the link. -/
theorem periodic_influence_paths {l : ℕ+} (hl : 1 < l.val) {β βmax B : ℝ}
    (hβ : 0 ≤ β) (hmax : β ≤ βmax) (hB : 0 ≤ B) {b : Edge l → ℝ}
    (hb : ∀ a, b a ≤ B) (k : ℕ) (e : Edge l) :
    influenceIterate (meanSquareInfluence β) b k e ≤ B * periodicRow βmax ^ k := by
  have hrow : periodicRow β ≤ periodicRow βmax := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmax (by norm_num)) (sqrt_nonneg _)
  apply influenceIterate_le (fun e a => mul_nonneg (mul_nonneg (sqrt_nonneg _) hβ) (Nat.cast_nonneg _))
    (fun e => (meanSquareInfluence_row hl β e).le.trans hrow) _ hB hb
  exact mul_nonneg (mul_nonneg (by norm_num) (hβ.trans hmax)) (sqrt_nonneg _)

/-- A uniform nonnegative comparison matrix bounds every path envelope in the
spectral shell theorem. The dimension and the matrix may vary by volume. -/
private theorem shell_gap_of_rows {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (h1 : α < 1) (l : ℕ → ℕ+)
    (A : (n : ℕ) → Edge (l n) → Edge (l n) → ℝ) (hA : ∀ n e a, 0 ≤ A n e a)
    (hrow : ∀ n e, ∑ a, A n e a ≤ α)
    (hShell : ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
      ∃ (B : ℝ) (b : (n : ℕ) → Edge (l n) → ℝ) (f : ℕ → ℕ → ℝ),
        0 ≤ B ∧ (∀ n a, b n a ≤ B) ∧
        (∀ k : ℕ, Tendsto (fun n => f n k) atTop
          (𝓝 (∫ p, exp (-((k : ℝ)*R)*YangMills.time p) ∂(T.energyMomentum.diagonal ψ)))) ∧
        ∀ n k, ∃ e : Edge (l n), f n k ≤ influenceIterate (A n) (b n) k e) :
    HasRelativisticMassGap T ((1/R)*log (1/α)) := by
  apply shell_envelopes_imply_relativistic_mass_gap T hW0 hW1 hW2 hR hα h1
  intro ψ hψ
  obtain ⟨B,b,f,hB,hb,hlap,hs⟩ := hShell ψ hψ
  refine ⟨B,f,hB,hlap,fun n k => ?_⟩
  obtain ⟨e,he⟩ := hs n k
  exact he.trans (influenceIterate_le (hA n) (hrow n) hα.le hB (hb n) k e)

/-- If finite-volume physical shell observables are dominated by Wilson influence
paths and converge to the diagonal Laplace transforms, the periodic rate yields a
relativistic gap. Shell comparison and spectral convergence are physical inputs. -/
theorem periodic_shell_limits_mass_gap {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax)
    (hwindow : βmax < 1 / (18*sqrt (1/12+π^2/16)))
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Icc 0 βmax)
    (hShell : ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
      ∃ (B : ℝ) (b : (n : ℕ) → Edge (l n) → ℝ) (f : ℕ → ℕ → ℝ),
        0 ≤ B ∧ (∀ n a, b n a ≤ B) ∧
        (∀ k : ℕ, Tendsto (fun n => f n k) atTop
          (𝓝 (∫ p, exp (-((k : ℝ)*R)*YangMills.time p) ∂(T.energyMomentum.diagonal ψ)))) ∧
        ∀ n k, ∃ e : Edge (l n), f n k ≤ influenceIterate (meanSquareInfluence (β n)) (b n) k e) :
    HasRelativisticMassGap T ((1/R)*log (1/periodicRow βmax)) := by
  have hα : 0 < periodicRow βmax := mul_pos (mul_pos (by norm_num) hpos) (sqrt_pos_of_pos (by positivity))
  have h1 : periodicRow βmax < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hwindow
    unfold periodicRow; linarith only [hwindow]
  apply shell_gap_of_rows T hW0 hW1 hW2 hR hα h1 l (fun n => meanSquareInfluence (β n))
    (fun n e a => mul_nonneg (mul_nonneg (sqrt_nonneg _) (hβ n).1) (Nat.cast_nonneg _)) _ hShell
  intro n e
  rw [meanSquareInfluence_row (hl n)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hβ n).2 (by norm_num)) (sqrt_nonneg _)

/-- Each periodic neighbor incidence contributes β/√3 in the geodesic metric. -/
def straightInfluence {l : ℕ+} (β : ℝ) (e a : Edge l) :=
  sqrt (1/3 : ℝ) * β * (neighborIncidenceCount e a : ℝ)

def straightRow (β : ℝ) := 18 * β / sqrt 3

private theorem sqrt_third : sqrt (1/3 : ℝ) = 1/sqrt 3 := by rw [sqrt_div (by norm_num),sqrt_one]

theorem heatBath_straight_influence {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal
      ((∑ a : Edge l, straightInfluence β e a * linkGeodesic (U a) (V a))^2) := by
  apply heatBath_influence_of_field_bound (C := 1/3) (by norm_num) _ hl hβ U V e
  intro r s hr hs k j
  simpa only [one_div,inv_mul_eq_div] using straight_field_wasserstein hr hs k j

theorem straightInfluence_row {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    ∑ a : Edge l, straightInfluence β e a = straightRow β := by
  simp only [straightInfluence,←Finset.mul_sum,incidence_row hl,straightRow,sqrt_third]; ring

theorem straightInfluence_self {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) :
    straightInfluence β e e = 0 := by simp [straightInfluence,incidence_self hl]

theorem straightRow_subunit {β : ℝ} : straightRow β < 1 ↔ β < sqrt 3 / 18 := by
  rw [straightRow,div_lt_iff₀ (by positivity),lt_div_iff₀ (by norm_num : (0:ℝ) < 18)]
  simp only [one_mul,mul_comm]

theorem straightRow_at_0096 : straightRow (12/125) < 1 := by
  rw [straightRow_subunit,lt_div_iff₀ (by norm_num : (0:ℝ) < 18)]
  nlinarith only [sq_sqrt (by norm_num : (0:ℝ) ≤ 3),sqrt_nonneg 3,
    sq_nonneg (sqrt 3 - 216/125)]

/-- Conditional physical shell limit for the improved, volume-uniform matrix. -/
theorem straight_shell_limits_mass_gap {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax)
    (hwindow : βmax < sqrt 3 / 18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Icc 0 βmax)
    (hShell : ∀ ψ : H.carrier, inner ℂ T.fields.vacuum.1 ψ = 0 →
      ∃ (B : ℝ) (b : (n : ℕ) → Edge (l n) → ℝ) (f : ℕ → ℕ → ℝ),
        0 ≤ B ∧ (∀ n a, b n a ≤ B) ∧
        (∀ k : ℕ, Tendsto (fun n => f n k) atTop
          (𝓝 (∫ p, exp (-((k : ℝ)*R)*YangMills.time p) ∂(T.energyMomentum.diagonal ψ)))) ∧
        ∀ n k, ∃ e : Edge (l n), f n k ≤ influenceIterate (straightInfluence (β n)) (b n) k e) :
    HasRelativisticMassGap T ((1/R)*log (1/straightRow βmax)) := by
  have hα : 0 < straightRow βmax := div_pos (mul_pos (by norm_num) hpos) (by positivity)
  apply shell_gap_of_rows T hW0 hW1 hW2 hR hα (straightRow_subunit.2 hwindow) l
    (fun n => straightInfluence (β n))
    (fun n e a => mul_nonneg (mul_nonneg (sqrt_nonneg _) (hβ n).1) (Nat.cast_nonneg _)) _ hShell
  intro n e
  rw [straightInfluence_row (hl n)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hβ n).2 (by norm_num)) (sqrt_nonneg _)

#print axioms heatBath_straight_influence
#print axioms straightInfluence_row
#print axioms straightInfluence_self
#print axioms straightRow_subunit
#print axioms straightRow_at_0096
#print axioms straight_shell_limits_mass_gap
#print axioms heatBath_influence_sum
#print axioms periodic_influence_paths
#print axioms periodic_shell_limits_mass_gap
end
end YangMills.PeriodicWilson
