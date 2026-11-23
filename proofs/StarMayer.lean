import WilsonPolymerBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

namespace YangMills.StarMayer
noncomputable section

/-- Interaction plaquettes in the shifted Wilson convention contribute β(1-P). -/
def bridgeAction (β : ℝ) {k : ℕ} (p : Fin k → ℝ) := ∑ j, β*(1-p j)

def bond (v : ℝ) := Real.exp (-v) - 1

theorem bridge_range {k : ℕ} {β : ℝ} (hb : 0 ≤ β)
    {p : Fin k → ℝ} (h : ∀ j, |p j| ≤ 1) :
    0 ≤ bridgeAction β p ∧ bridgeAction β p ≤ 2*β*k := by
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg hb (sub_nonneg.mpr (abs_le.mp (h j)).2)
  · calc
      bridgeAction β p ≤ ∑ _ : Fin k, β*2 := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (h j)).1]) hb
      _ = _ := by simp; ring

/-- The single-bond activity is the exact correction to two normalized product cells. -/
theorem two_cell {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (V : X × Y → ℝ) (hv : Integrable (fun z => Real.exp (-V z)) (μ.prod ν)) :
    (∫ z, Real.exp (-V z) ∂μ.prod ν) = 1 + ∫ z, bond (V z) ∂μ.prod ν := by
  unfold bond
  rw [integral_sub hv (integrable_const _)]
  simp

/-- Without inter-cell concentration the worst-case bound approaches one at large β. -/
theorem two_cell_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {V : X → ℝ} {B : ℝ} (bound : ∀ x, 0 ≤ V x ∧ V x ≤ B)
    (h : Integrable (fun x => bond (V x)) μ) :
    |∫ x, bond (V x) ∂μ| ≤ 1 - Real.exp (-B) := by
  have pos (x : X) : Real.exp (-B) - 1 ≤ bond (V x) :=
    sub_le_sub_right (Real.exp_le_exp.mpr (neg_le_neg (bound x).2)) _
  have neg (x : X) : bond (V x) ≤ 0 := by
    unfold bond; linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr (bound x).1)]
  have lower := integral_mono (μ := μ) (integrable_const (Real.exp (-B)-1)) h pos
  have upper := integral_mono (μ := μ) h (integrable_const (0:ℝ)) neg
  simp at lower upper
  rw [abs_of_nonpos upper]; linarith

/-- Exact finite Mayer expansion. Factorizing the terms by connected support and
bounding their activities is a subsequent step in using Kotecký–Preiss. -/
theorem finite_expansion {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (s : Finset ι) (V : ι → X → ℝ)
    (h : ∀ a ∈ s.powerset, Integrable (fun x => ∏ e ∈ a, bond (V e x)) μ) :
    (∫ x, ∏ e ∈ s, Real.exp (-V e x) ∂μ) =
      ∑ a ∈ s.powerset, ∫ x, ∏ e ∈ a, bond (V e x) ∂μ := by
  rw [← integral_finsetSum _ h]
  apply integral_congr_ae
  filter_upwards with x
  rw [← Finset.prod_one_add]
  simp [bond]

open YangMills.WilsonPolymer

/-- The two-cell problem has one hard-core polymer, its crossing bond. -/
def oneBond (z : ℝ) : PolymerModel Unit where
  incompat := fun _ _ => True
  decIncompat := fun _ _ => isTrue trivial
  refl := fun _ => trivial
  symm := fun _ _ _ => trivial
  w := fun _ => z
  a := fun _ => 1
  a_nonneg := fun _ => zero_le_one

theorem oneBond_partition (z : ℝ) : (oneBond z).Z {()} = 1+(z:ℂ) := by
  rw [(oneBond z).Z_recursion {()} (γ:=()) (by simp)]
  simp [PolymerModel.nbhd,oneBond,PolymerModel.Z_empty]

/-- The same integrated bridge activity feeds the repository's KP ratio theorem. -/
theorem two_cell_KP {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (V : X × Y → ℝ) (hv : Integrable (fun x => Real.exp (-V x)) (μ.prod ν))
    (h : |∫ x, bond (V x) ∂μ.prod ν| * Real.exp 1 ≤ 1) :
    let z := ∫ x, bond (V x) ∂μ.prod ν
    let Z := ∫ x, Real.exp (-V x) ∂μ.prod ν
    (oneBond z).Z {()} = (Z:ℂ) ∧ Z ≠ 0 ∧
      ‖1 / (Z:ℂ)‖ ≤ Real.exp (|z| *Real.exp 1) := by
  let z := ∫ x, bond (V x) ∂μ.prod ν
  let Z := ∫ x, Real.exp (-V x) ∂μ.prod ν
  have eq : (oneBond z).Z {()} = (Z:ℂ) := by
    rw [oneBond_partition]; simp [Z,two_cell μ ν V hv,z]
  have kp : (oneBond z).KoteckyPreissCond {()} := by
    intro γ _
    simpa [PolymerModel.nbhd,oneBond,Complex.norm_real,Real.norm_eq_abs,z] using h
  have result := (oneBond z).kotecky_preiss_partition_nonvanishing_and_ratio kp {()} (by rfl)
  have ratio := result.2 () (by simp)
  rw [eq] at result ratio
  refine ⟨eq,fun hz => result.1 (by simp [Z,hz]),?_⟩
  simpa [PolymerModel.Z_empty,oneBond,Complex.norm_real,Real.norm_eq_abs] using ratio

#print axioms two_cell_KP
#print axioms two_cell
#print axioms two_cell_bound
#print axioms finite_expansion
end
end YangMills.StarMayer
