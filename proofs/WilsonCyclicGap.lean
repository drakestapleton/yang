-- SPDX-License-Identifier: Apache-2.0
import WilsonWordClustering

namespace YangMills.PeriodicWilson
open FundamentalSU2 PhaseTwo UfbiBridge Real Filter MeasureTheory Set
open scoped Topology
noncomputable section

private theorem productExpansion_uniform {l : ℕ+} (b : ℕ+) (hl : 1 < l.val) {β βmax A : ℝ}
    (hβ : β ∈ Icc 0 βmax) (hwindow : βmax < sqrt 3/18) (t : Axis) (k : ℕ)
    (terms : List (WilsonProductTerm l)) (hA : productExpansionWeight terms ≤ A) (hA0 : 0 ≤ A)
    (hs : ∀ a ∈ terms, a.coefficient ≠ 0 → separatedPlaquetteProducts t k a.left a.right) :
    productExpansion b β terms ≤ (A*(4*b.val*π^2/(1-straightRow βmax)))*(straightRow βmax)^(b.val*k) := by
  have hr : straightRow β ≤ straightRow βmax := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hβ.2 (by norm_num)) (sqrt_nonneg _)
  have hnn : 0 ≤ straightRow β := div_nonneg (mul_nonneg (by norm_num) hβ.1) (sqrt_nonneg _)
  have hden : 0 < 1-straightRow βmax := sub_pos.mpr (straightRow_subunit.2 hwindow)
  have hP : 0 ≤ 4*(b.val:ℝ)*π^2/(1-straightRow βmax) := div_nonneg (by positivity) hden.le
  apply (le_abs_self _).trans ((productExpansion_bound b hl hβ.1 (hβ.2.trans_lt hwindow) t k terms hs).trans ?_)
  rw [← pow_mul, mul_assoc A]
  apply mul_le_mul hA _ (mul_nonneg (div_nonneg (by positivity) (hden.le.trans (sub_le_sub_left hr _))) (pow_nonneg hnn _)) hA0
  exact mul_le_mul (div_le_div_of_nonneg_left (by positivity) hden (sub_le_sub_left hr _))
    (pow_le_pow_left₀ hnn hr _) (pow_nonneg hnn _) hP

/-- To exclude a low-energy band, one-sided approximation on an unbounded
set of shells for each centered field word is sufficient. The side, loop
products, and coefficients of a witness may depend on the requested accuracy. -/
theorem blockedWilson_gap_of_word_comparison {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    (b : ℕ+) (axis : Axis) {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax) (hwindow : βmax < sqrt 3/18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val) (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Icc 0 βmax)
    (hwords : ∀ w, ∃ (A : ℝ) (k : ℕ → ℕ), 0 ≤ A ∧ Tendsto k atTop atTop ∧
      ∀ j, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (terms : List (WilsonProductTerm (l n))),
        productExpansionWeight terms ≤ A ∧
        (∀ a ∈ terms, a.coefficient ≠ 0 → separatedPlaquetteProducts axis (k j) a.left a.right) ∧
        (∫ p, exp (-((b.val*k j:ℕ):ℝ)*R*YangMills.time p) ∂(T.energyMomentum.diagonal (centeredFieldWord T w)))
          ≤ productExpansion b (β n) terms + ε) :
    HasRelativisticMassGap T ((1/R)*log (1/straightRow βmax)) := by
  let α := straightRow βmax
  have hα : 0 < α := div_pos (mul_pos (by norm_num) hpos) (by positivity)
  have hα1 : α < 1 := straightRow_subunit.2 hwindow
  have hΔ := (dobrushin_shlosman_exponential_decay (C := 1) hR hα hα1 0).2
  apply cyclic_word_decay_implies_relativistic_mass_gap T hW0 hW1 hW2 hΔ
  intro w
  obtain ⟨A,k,hA,hk,hobs⟩ := hwords w
  let C := A*(4*b.val*π^2/(1-α))
  let clock := fun j => ((b.val * k j : ℕ) : ℝ) * R
  have hclock : Tendsto clock atTop atTop := by
    have hb : Tendsto (fun j => b.val * k j) atTop atTop :=
      tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left _ b.prop) hk
    exact (tendsto_natCast_atTop_atTop.comp hb).atTop_mul_const hR
  refine ⟨C,clock,hclock,.of_forall fun j => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n,terms,hweight,hsep,hcomp⟩ := hobs j ε hε
  have hub := productExpansion_uniform b (hl n) (hβ n) hwindow axis (k j) terms hweight hA hsep
  have hrate := (dobrushin_shlosman_exponential_decay (C := C) hR hα hα1 (b.val*k j)).1
  have hsum := hcomp.trans (add_le_add (hub.trans_eq hrate) (le_refl ε))
  simpa only [clock, neg_mul] using hsum

/-- Ordinary finite-volume convergence supplies the comparison without a
volume convergence rate. Only individual finite field words occur in this
hypothesis. Neither their linear combinations nor arbitrary Hilbert vectors
need separate lattice realizations. -/
theorem blockedWilson_gap_of_word_limits {H : HilbertSpace} {Labels : FieldLabels}
    (T : WightmanTheory H Labels) (hW0 : T.W0) (hW1 : T.W1) (hW2 : T.W2)
    (b : ℕ+) (axis : Axis) {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax) (hwindow : βmax < sqrt 3/18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val) (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Icc 0 βmax)
    (hwords : ∀ w, ∃ (A : ℝ) (k : ℕ → ℕ) (terms : (n j : ℕ) → List (WilsonProductTerm (l n))),
      0 ≤ A ∧ Tendsto k atTop atTop ∧
      (∀ j, ∀ᶠ n in atTop, productExpansionWeight (terms n j) ≤ A ∧
        ∀ a ∈ terms n j, a.coefficient ≠ 0 → separatedPlaquetteProducts axis (k j) a.left a.right) ∧
      ∀ j, Tendsto (fun n => productExpansion b (β n) (terms n j)) atTop
        (𝓝 (∫ p, exp (-((b.val*k j:ℕ):ℝ)*R*YangMills.time p) ∂(T.energyMomentum.diagonal (centeredFieldWord T w))))) :
    HasRelativisticMassGap T ((1/R)*log (1/straightRow βmax)) := by
  apply blockedWilson_gap_of_word_comparison T hW0 hW1 hW2 b axis hR hpos hwindow l hl β hβ
  intro w
  obtain ⟨A,k,terms,hA,hk,hs,hm⟩ := hwords w
  refine ⟨A,k,hA,hk,fun j ε hε => ?_⟩
  have hnear := (Metric.tendsto_nhds.mp (hm j)) ε hε
  obtain ⟨n,hn,hclose⟩ := ((hs j).and hnear).exists
  refine ⟨n,terms n j,hn.1,hn.2,?_⟩
  rw [Real.dist_eq, abs_lt] at hclose
  linarith only [hclose.1]

/-- Read a word of actual Wilson insertion tokens as a word of smeared
continuum field labels in the public reconstruction. -/
def insertionWord {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (word : List (C.Token × TestFunction)) : List (T.labels.carrier × TestFunction) :=
  word.map fun a => (T.toLabel (T.project a.1).1 (T.project a.1).2, a.2)

theorem insertionWord_surjective {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (hT : T.Reconstructed) :
    Function.Surjective (insertionWord T) := by
  intro w
  induction w with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨tag,htag⟩ := hT.covers x.1
    obtain ⟨token,htoken⟩ := hT.represents tag
    obtain ⟨tail,htail⟩ := ih
    refine ⟨(token,x.2)::tail,?_⟩
    change (T.toLabel (T.project token).1 (T.project token).2,x.2)::insertionWord T tail = x::xs
    change T.toLabel tag.1 tag.2 = x.1 at htag
    rw [htoken,htag,htail]

/-- The public reconstruction covers the dense W1 domain using its own
insertion tokens. The remaining matching condition is indexed by those
tokens and their Schwartz smearings. -/
theorem reconstructed_gap_of_token_limits {C : WilsonFamily gaugeGroup} (T : Hierarchy C) (hT : T.Reconstructed)
    (b : ℕ+) (axis : Axis) {R βmax : ℝ} (hR : 0 < R) (hpos : 0 < βmax) (hwindow : βmax < sqrt 3/18)
    (l : ℕ → ℕ+) (hl : ∀ n, 1 < (l n).val) (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Icc 0 βmax)
    (hmatch : ∀ w : List (C.Token × TestFunction),
      ∃ (A : ℝ) (k : ℕ → ℕ) (terms : (n j : ℕ) → List (WilsonProductTerm (l n))),
        0 ≤ A ∧ Tendsto k atTop atTop ∧
        (∀ j, ∀ᶠ n in atTop, productExpansionWeight (terms n j) ≤ A ∧
          ∀ a ∈ terms n j, a.coefficient ≠ 0 → separatedPlaquetteProducts axis (k j) a.left a.right) ∧
        ∀ j, Tendsto (fun n => productExpansion b (β n) (terms n j)) atTop
          (𝓝 (∫ p, exp (-((b.val*k j:ℕ):ℝ)*R*YangMills.time p)
            ∂(T.theory.energyMomentum.diagonal (centeredFieldWord T.theory (insertionWord T w)))))) :
    HasRelativisticMassGap T.theory ((1/R)*log (1/straightRow βmax)) := by
  apply blockedWilson_gap_of_word_limits T.theory hT.axioms.w0 hT.axioms.w1 hT.axioms.w2
    b axis hR hpos hwindow l hl β hβ
  intro v
  obtain ⟨w,rfl⟩ := insertionWord_surjective T hT v
  exact hmatch w

/-- Along a weak bare-coupling trajectory, powering the *bare row estimate*
by any positive block size eventually gives a nonpositive inferred rate. -/
theorem bare_block_rate_eventually_nonpos (β : ℕ → ℝ) (hβ : Tendsto β atTop atTop)
    (b : ℕ → ℕ+) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) :
    ∀ᶠ n in atTop, -log (straightRow (β n) ^ (b n).val) / ((b n).val*R n) ≤ 0 := by
  filter_upwards [hβ.eventually_ge_atTop (sqrt 3/18)] with n hn
  have hrow : 1 ≤ straightRow (β n) := le_of_not_gt fun h => hn.not_gt (straightRow_subunit.1 h)
  rw [block_physical_rate (b n) _ _ (hR n)]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (log_nonneg hrow)) (hR n).le

/-- The positive running slope in the public Wilson interface forces the
bare beta to infinity even when the box index changes with the mesh. -/
theorem regular_bare_beta_tendsto {g : GaugeGroup} {C : WilsonFamily g} (hC : WilsonRegularity C) (box : ℕ → ℕ) :
    Tendsto (fun n => C.beta n (box n)) atTop atTop := by
  obtain ⟨s,hs,hrun⟩ := hC.running
  have hlog : Tendsto (fun n => log ((C.denominator n).val : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp C.denominatorStrict.tendsto_atTop)
  have hhalf : 0 < s/2 := half_pos hs
  have hlower : Tendsto (fun n => s/2 * log ((C.denominator n).val : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hhalf
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [hrun (s/2) hhalf, hlog.eventually_gt_atTop 0] with n hn hln
  have h := (abs_lt.mp (hn (box n))).1
  simp only [WilsonFamily.mesh, inv_inv] at h
  apply (le_div_iff₀ hln).mp
  linarith

theorem regular_bare_block_rate_eventually_nonpos {C : WilsonFamily gaugeGroup} (hC : WilsonRegularity C)
    (box : ℕ → ℕ) (b : ℕ → ℕ+) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) :
    ∀ᶠ n in atTop, -log (straightRow (C.beta n (box n)) ^ (b n).val) / ((b n).val*R n) ≤ 0 :=
  bare_block_rate_eventually_nonpos _ (regular_bare_beta_tendsto hC box) b R hR

#print axioms insertionWord_surjective
#print axioms reconstructed_gap_of_token_limits
#print axioms regular_bare_beta_tendsto
#print axioms regular_bare_block_rate_eventually_nonpos
#print axioms blockedWilson_gap_of_word_comparison
#print axioms blockedWilson_gap_of_word_limits
#print axioms bare_block_rate_eventually_nonpos
end
end YangMills.PeriodicWilson
