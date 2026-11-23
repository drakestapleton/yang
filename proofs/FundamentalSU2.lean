-- SPDX-License-Identifier: Apache-2.0
import PublicWilson
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Star

namespace YangMills.FundamentalSU2
open Matrix Filter
open scoped Matrix.Norms.Frobenius Topology ComplexConjugate
noncomputable section

abbrev M := Matrix (Fin 2) (Fin 2) ℂ

/-- The real quaternion algebra inside two-by-two complex matrices. -/
def quaternionAlgebra : Subalgebra ℝ M where
  carrier := {A | A 1 1 = conj (A 0 0) ∧ A 1 0 = -conj (A 0 1)}
  algebraMap_mem' r := by
    change (algebraMap ℝ M r) 1 1 = _ ∧ (algebraMap ℝ M r) 1 0 = _
    simp [Matrix.algebraMap_eq_diagonal]
  add_mem' := by
    rintro A B ⟨ha, hb⟩ ⟨hc, hd⟩
    simp_all [Matrix.add_apply]
    ring
  mul_mem' := by
    rintro A B ⟨ha, hb⟩ ⟨hc, hd⟩
    change (A*B) 1 1 = _ ∧ (A*B) 1 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd]
    ring

private theorem quaternion_star {A : M} (h : A ∈ quaternionAlgebra) : star A ∈ quaternionAlgebra := by
  obtain ⟨ha,hb⟩ := h
  change (star A) 1 1 = _ ∧ (star A) 1 0 = _
  simp [Matrix.star_apply, ha, hb]

def quaternionUnitary : Subgroup (UnitaryRepresentation 1) where
  carrier := {u | u.val ∈ quaternionAlgebra}
  one_mem' := quaternionAlgebra.one_mem
  mul_mem' := fun h k => quaternionAlgebra.mul_mem h k
  inv_mem' := fun h => quaternion_star h

/-- This group consists of exactly the determinant-one two-by-two unitary matrices. -/
theorem mem_iff_det_one (u : UnitaryRepresentation 1) :
    u ∈ quaternionUnitary ↔ u.val.det = 1 := by
  let A : M := u.val
  have hl : star A * A = 1 := u.prop.1
  have hr : A * star A = 1 := u.prop.2
  change (A 1 1 = conj (A 0 0) ∧ A 1 0 = -conj (A 0 1)) ↔ A.det=1
  constructor
  · rintro ⟨ha,hb⟩
    have h := congrArg (fun X : M => X 0 0) hr
    simpa [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, ha,hb] using h
  · intro hd
    have hinv : star A = A.adjugate := calc
      _ = star A * (A * A.adjugate) := by rw [Matrix.mul_adjugate, hd, one_smul, mul_one]
      _ = _ := by rw [← mul_assoc, hl, one_mul]
    have h0 := congrArg (fun X : M => X 0 0) hinv
    have h1 := congrArg (fun X : M => X 1 0) hinv
    simp [Matrix.star_apply, Matrix.adjugate_fin_two] at h0 h1
    exact ⟨h0.symm, by simpa using congrArg Neg.neg h1.symm⟩

private def tangent : Submodule ℝ M where
  carrier := {X | X ∈ quaternionAlgebra ∧ star X = -X}
  zero_mem' := ⟨quaternionAlgebra.zero_mem, by simp⟩
  add_mem' := fun ⟨hx,hs⟩ ⟨hy,ht⟩ => ⟨quaternionAlgebra.add_mem hx hy, by simp [hs,ht,add_comm]⟩
  smul_mem' := fun c X ⟨h,hs⟩ => ⟨quaternionAlgebra.smul_mem h c, by simp [hs]⟩

private theorem exp_mem_quaternion {X : M} (hx : X ∈ quaternionAlgebra) :
    NormedSpace.exp X ∈ quaternionAlgebra := by
  apply quaternionAlgebra.toSubmodule.closed_of_finiteDimensional.mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X)
  exact .of_forall fun S => quaternionAlgebra.sum_mem fun n _ =>
    quaternionAlgebra.smul_mem (quaternionAlgebra.pow_mem hx n) _

set_option backward.isDefEq.respectTransparency false in
private theorem generates (X : M) :
    X ∈ tangent ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈
      Set.range (fun u : quaternionUnitary => (u.val.val : M)) := by
  constructor
  · rintro ⟨hq,hs⟩ t
    have hx : t • X ∈ skewAdjoint M := by simp [skewAdjoint.mem_iff, hs]
    exact ⟨⟨⟨_, NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hx⟩,
      exp_mem_quaternion (quaternionAlgebra.smul_mem hq t)⟩, rfl⟩
  · intro h
    let f := fun t : ℝ => NormedSpace.exp (t • X)
    have hf (t : ℝ) : f t ∈ quaternionAlgebra ∧ star (f t) * f t = 1 := by
      obtain ⟨u,hu⟩ := h t
      change NormedSpace.exp (t • X) ∈ _ ∧ star (NormedSpace.exp (t • X)) * NormedSpace.exp (t • X) = 1
      rw [← hu]
      exact ⟨u.prop, u.val.prop.1⟩
    have hd : HasDerivAt f X 0 := by
      simpa [f] using! hasDerivAt_exp_smul_const X (0:ℝ)
    have hq : X ∈ quaternionAlgebra := by
      apply quaternionAlgebra.toSubmodule.closed_of_finiteDimensional.mem_of_tendsto
        (hasDerivAt_iff_tendsto_slope.mp hd)
      exact .of_forall fun t => quaternionAlgebra.smul_mem
        (quaternionAlgebra.sub_mem (hf t).1 (hf 0).1) _
    have hc : (fun t => star (f t) * f t) = (fun _ => (1:M)) := funext fun t => (hf t).2
    have hh := hd.star.mul hd
    change HasDerivAt (fun t => star (f t) * f t) _ 0 at hh
    rw [hc] at hh
    have hz := hh.unique (hasDerivAt_const (0:ℝ) (1:M))
    simp [f] at hz
    exact ⟨hq, eq_neg_of_add_eq_zero_left hz⟩

/-- The fundamental SU(2) gauge group in the public Wilson API. -/
def gaugeGroup : GaugeGroup where
  n := 1
  image := quaternionUnitary
  imageClosed := quaternionAlgebra.toSubmodule.closed_of_finiteDimensional.preimage continuous_subtype_val
  lieAlgebra := tangent
  generates := generates

/-- Quaternion length in the fundamental matrix representation. -/
def length (A : M) := Real.sqrt (‖A 0 0‖^2 + ‖A 0 1‖^2)

theorem frobenius_eq {A : M} (ha : A ∈ quaternionAlgebra) :
    ‖A‖ = Real.sqrt 2 * length A := by
  obtain ⟨h1,h2⟩ := ha
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Fin.sum_univ_two, h1,h2, norm_neg, Complex.norm_conj, length]
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring_nf
  norm_num

theorem unitary_of_length_one {A : M} (ha : A ∈ quaternionAlgebra) (h : length A = 1) :
    A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  obtain ⟨hd,hc⟩ := ha
  have sq := Real.sq_sqrt (show 0 ≤ ‖A 0 0‖^2+‖A 0 1‖^2 by positivity)
  change length A^2 = _ at sq
  rw [h,one_pow] at sq
  have eqC : conj (A 0 0) * A 0 0 + conj (A 0 1) * A 0 1 = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_add, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← sq]
    simp
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, hd,hc, mul_comm] at * <;>
    first | exact eqC | linear_combination eqC

/-- Every staple matrix in the quaternion subalgebra is its nonnegative length times
an actual SU(2) matrix. At zero any unit quaternion works. -/
theorem polar {A : M} (ha : A ∈ quaternionAlgebra) :
    ∃ u : gaugeGroup.image, A = length A • u.val.val := by
  have hnn : 0 ≤ length A := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hnn with hz | hp
  · have hA : A = 0 := norm_eq_zero.mp (by rw [frobenius_eq ha, ← hz, mul_zero])
    exact ⟨1, by simp [hA,length]; rfl⟩
  · let B := (length A)⁻¹ • A
    have hB := quaternionAlgebra.smul_mem ha (length A)⁻¹
    have hlen : length B = 1 := by
      have hh := frobenius_eq hB
      change ‖(length A)⁻¹ • A‖ = Real.sqrt 2 * length B at hh
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), frobenius_eq ha] at hh
      field_simp at hh
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)]
    refine ⟨⟨⟨B, unitary_of_length_one hB hlen⟩, hB⟩, ?_⟩
    change A = length A • ((length A)⁻¹ • A)
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

#print axioms polar
#print axioms mem_iff_det_one
#print axioms gaugeGroup
end
end YangMills.FundamentalSU2
