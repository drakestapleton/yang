-- SPDX-License-Identifier: Apache-2.0
import Mathlib

/-! Cut one bond of a periodic path and evaluate its marked integral trace. -/
namespace YangMills.PlaquetteTransfer
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
abbrev V (X : Type*) [TopologicalSpace X] := C(X, ℝ)
abbrev Op (X : Type*) [TopologicalSpace X] [CompactSpace X] := V X →L[ℝ] V X
abbrev Columns (X : Type*) [TopologicalSpace X] [CompactSpace X] := C(X, V X)

def pairing (μ : Measure X) (a b : V X) := ∫ x, a x * b x ∂μ

omit [MeasurableSpace X] [BorelSpace X] in
private theorem diagCont (F : Op X) (k : Columns X) : Continuous (fun x => F (k x) x) :=
  continuous_eval.comp ((F.continuous.comp k.continuous).prodMk continuous_id)

/-- The diagonal integral of F followed by a single integral kernel. -/
def cutTrace (μ : Measure X) [IsProbabilityMeasure μ] (F : Op X) : Columns X →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun (k : Columns X) => ∫ x, F (k x) x ∂μ
      map_add' := by
        intro a b
        simp only [ContinuousMap.add_apply, map_add]
        apply integral_add
        all_goals exact (diagCont _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      map_smul' := by
        intro r k
        simp only [ContinuousMap.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul]
        apply integral_const_mul }
    ‖F‖ (by
      intro k
      simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => F (k x) x)
        (.of_forall fun x => ((F (k x)).norm_coe_le_norm x).trans <|
          (F.le_opNorm (k x)).trans (mul_le_mul_of_nonneg_left (k.norm_coe_le_norm x) (norm_nonneg _))))

def thermal (μ : Measure X) [IsProbabilityMeasure μ] (T : Op X) (k : Columns X)
    (a : V X) (d r : ℕ) : ℝ :=
  let M := ContinuousLinearMap.mul ℝ (V X) a
  let tr := fun F : Op X => cutTrace μ (F.comp (T^r)) k
  let Z := tr (T^d)
  tr ((M.comp (T^d)).comp M) / Z - (tr (M.comp (T^d)) / Z)^2

end
end YangMills.PlaquetteTransfer
