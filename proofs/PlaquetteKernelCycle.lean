-- SPDX-License-Identifier: Apache-2.0
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact

/-! Cut a product-measure time circle at its source and integrate its two arcs. -/
namespace YangMills.KernelCycle
open MeasureTheory
noncomputable section

private theorem integrate_head {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (f : (Fin (n+1) → X) → ℝ)
    (hf : Continuous f) :
    (∫ u, f u ∂Measure.pi (fun _ => μ)) =
    ∫ x, (∫ v, f (Fin.cons x v) ∂Measure.pi (fun _ => μ)) ∂μ := by
  have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  have hi := hf.integrable_of_hasCompactSupport (μ := Measure.pi (fun _ => μ)) (HasCompactSupport.of_compactSpace _)
  rw [← mp.integral_comp']
  have hprod := integral_prod _ (mp.integrable_comp_of_integrable hi)
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Function.comp_apply, Fin.zero_succAbove, cast_eq] using hprod

private abbrev front {X : Type*} {n : ℕ} (x : X) (u : Fin n → X) : Fin (n+1) → X :=
  Fin.cons (α := fun _ => X) x u

private def pathWeight {X : Type*} (K : X → X → ℝ) (f : X → ℝ) :
    (n : ℕ) → X → (Fin n → X) → ℝ
  | 0, x, _ => f x
  | n+1, x, u => K x (u 0) * pathWeight K f n (u 0) (Fin.tail u)

private theorem pathWeight_prod {X : Type*} (K : X → X → ℝ) (f : X → ℝ)
    (n : ℕ) (x : X) (u : Fin n → X) :
    pathWeight K f n x u =
      (∏ j, K ((front x u) j.castSucc) (u j)) * f ((front x u) (Fin.last n)) := by
  induction n generalizing x with
  | zero => simp [pathWeight, front]
  | succ n ih =>
    rw [pathWeight, ih, Fin.prod_univ_succ]
    simp [front, Fin.tail, Fin.cons_last, Fin.castSucc_succ, mul_assoc]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (K : C(X × X, ℝ))

def steps : ℕ → (X → ℝ) → X → ℝ
  | 0, f => f
  | n+1, f => fun x => ∫ y, K (x,y) * steps n f y ∂μ

private abbrev edge (x y : X) := K (x,y)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
private theorem path_cont (f : X → ℝ) (hf : Continuous f) (n : ℕ) (x : X) :
    Continuous (pathWeight (edge K) f n x) := by
  simp_rw [funext (pathWeight_prod (edge K) f n x)]
  have hc (j : Fin (n+1)) : Continuous (fun u : Fin n → X => front x u j) := by
    cases j using Fin.cases <;> simp [front, continuous_apply, continuous_const]
  apply Continuous.mul _ (hf.comp (hc _))
  apply continuous_finsetProd
  intro i _
  exact K.continuous.comp ((hc _).prodMk (continuous_apply _))

private theorem path_integral (f : C(X,ℝ)) (n : ℕ) (x : X) :
    (∫ u, pathWeight (edge K) f n x u ∂Measure.pi (fun _ => μ)) = steps μ K n f x := by
  induction n generalizing x with
  | zero => simp [pathWeight, steps, measureReal_def]
  | succ n ih =>
    rw [integrate_head _ _ (path_cont K _ f.continuous _ x)]
    simp only [pathWeight, Fin.cons_zero, Fin.tail_cons, integral_const_mul, ih,
      steps]


def mark (r d : ℕ) : Fin (r+d+1) := ⟨d, by omega⟩

private theorem path_marked_integral (b f : C(X,ℝ)) (d r : ℕ) (x : X) :
    (∫ u, b ((front x u) (mark r d)) * pathWeight (edge K) f (r+d) x u
      ∂Measure.pi (fun _ => μ)) =
    steps μ K d (fun y => b y * steps μ K r f y) x := by
  induction d generalizing x with
  | zero =>
    change (∫ u, b x * pathWeight (edge K) f r x u ∂_) = _
    rw [integral_const_mul]
    exact congrArg (b x * ·) (path_integral μ K f r x)
  | succ d ih =>
    have hm : mark r (d+1) = (mark r d).succ := rfl
    rw [hm]
    change (∫ u : Fin ((r+d)+1) → X, b (u (mark r d)) * pathWeight _ f ((r+d)+1) x u ∂_) = _
    let g := fun u : Fin ((r+d)+1) → X => b (u (mark r d)) * pathWeight (edge K) f ((r+d)+1) x u
    have hg : Continuous g := (b.continuous.comp (continuous_apply _)).mul (path_cont K _ f.continuous _ x)
    refine (integrate_head μ g hg).trans ?_
    apply integral_congr_ae
    filter_upwards with y
    change (∫ u, b (front y u (mark r d)) * (edge K x y * pathWeight _ f (r+d) y u) ∂_) =
      edge K x y * steps μ K d (fun z => b z * steps μ K r f z) y
    simp_rw [mul_left_comm (b _) (edge K x y), integral_const_mul]
    exact congrArg (edge K x y * ·) (ih y)


omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
private theorem closed_product (n : ℕ) (x : X) (u : Fin n → X) :
    (∏ t : Fin (n+1), edge K ((front x u) t) ((front x u) (t+1))) =
      pathWeight (edge K) (fun z => edge K z x) n x u := by
  rw [pathWeight_prod, Fin.prod_univ_castSucc, Fin.last_add_one]
  simp only [front, Fin.cons_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have h : i.castSucc + 1 = i.succ := by simp
  simp [h]

/-- The source is at 0 and the sink at d on the closed r+d+1 slice circle. -/
theorem cycle_integral (a b : C(X,ℝ)) (d r : ℕ) :
    (∫ U : Fin (r+d+1) → X, (a (U 0) * b (U (mark r d))) *
      ∏ t, K (U t,U (t+1)) ∂Measure.pi (fun _ => μ)) =
    (∫ x, a x * steps μ K d (fun y => b y * steps μ K r (fun z => K (z,x)) y) x ∂μ) := by
  rw [integrate_head μ]
  · change (∫ x, (∫ u, a x * b (front x u (mark r d)) *
          ∏ t, edge K (front x u t) (front x u (t+1)) ∂_) ∂_) = _
    simp_rw [closed_product K (r+d), mul_assoc, integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    let f : C(X,ℝ) := ⟨fun z => K (z,x), K.continuous.comp (continuous_id.prodMk continuous_const)⟩
    exact path_marked_integral μ K b f d r x
  · apply Continuous.mul
    · exact (a.continuous.comp (continuous_apply _)).mul (b.continuous.comp (continuous_apply _))
    · apply continuous_finsetProd
      intro i _
      exact K.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))

#print axioms cycle_integral
end
end YangMills.KernelCycle
