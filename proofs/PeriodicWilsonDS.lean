-- SPDX-License-Identifier: Apache-2.0
import WilsonFieldResponse

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
theorem heatBath_influence_sum {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hβ : 0 ≤ β)
    (U V : Configuration gaugeGroup l) (e : Edge l) :
    linkWassersteinSq (heatBath β U e) (heatBath β V e) ≤ ENNReal.ofReal
      ((∑ a : Edge l, meanSquareInfluence β e a * linkGeodesic (U a) (V a))^2) := by
  apply (periodic_neighbor_mean_square hl hβ U V e).trans (ENNReal.ofReal_le_ofReal ?_)
  let d := fun a => linkGeodesic (U a) (V a)
  let C := sqrt (1/12 + π^2/16) * β
  have he : (∑ a : Edge l, meanSquareInfluence β e a * d a) =
      C * ∑ i ∈ incidences e, d (neighbor e i.1 i.2).1 := by
    simp only [meanSquareInfluence,mul_assoc,← Finset.mul_sum,incidence_profile,C]
  change _ ≤ (∑ a : Edge l, meanSquareInfluence β e a * d a)^2
  rw [he]
  have hC : 0 ≤ C := mul_nonneg (sqrt_nonneg _) hβ
  let chord := fun a : Edge l => linkChord (U a) (V a) / sqrt 2
  let S := ∑ i ∈ incidences e, chord (neighbor e i.1 i.2).1
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (sqrt_nonneg _)
  have hdist : S ≤ ∑ i ∈ incidences e, d (neighbor e i.1 i.2).1 :=
    Finset.sum_le_sum fun i _ => normalized_chord_le_geodesic (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1)
  calc (1/12+π^2/16)*(β*S)^2 = (C*S)^2 := by
          simp only [C,mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1/12+π^2/16)]; ring
       _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hC hS) (mul_le_mul_of_nonneg_left hdist hC) 2

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
  apply shell_envelopes_imply_relativistic_mass_gap T hW0 hW1 hW2 hR hα h1
  intro ψ hψ
  obtain ⟨B,b,f,hB,hb,hlap,hs⟩ := hShell ψ hψ
  refine ⟨B,f,hB,hlap,fun n k => ?_⟩
  obtain ⟨e,he⟩ := hs n k
  exact he.trans (periodic_influence_paths (hl n) (hβ n).1 (hβ n).2 hB (hb n) k e)

#print axioms heatBath_influence_sum
#print axioms periodic_influence_paths
#print axioms periodic_shell_limits_mass_gap
end
end YangMills.PeriodicWilson
