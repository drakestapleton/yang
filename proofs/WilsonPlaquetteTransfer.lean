-- SPDX-License-Identifier: Apache-2.0
import PeriodicWilson
import PlaquetteKernelTrace
import PlaquetteKernelCycle
import Mathlib.MeasureTheory.Integral.Pi

/-! Finite spatial volume, periodic time. Axes 0,1,2 are spatial, axis 3 is time.
All energies and separations are in lattice units. -/
namespace YangMills.PlaquetteTransfer
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ENNReal
noncomputable section

abbrev G := FundamentalSU2.gaugeGroup.image
abbrev Space (L : ℕ+) := Fin 3 → ZMod L.val
abbrev Slice (L : ℕ+) := Space L × Fin 3 → G
abbrev Vertical (L : ℕ+) := Space L → G

def shift {L : ℕ+} (x : Space L) (i : Fin 3) : Space L := x + Pi.single i 1

def normalizedTrace (u : G) : ℝ := u.val.val.trace.re / 2

def face {L : ℕ+} (U : Slice L) (x : Space L) (i j : Fin 3) : ℝ :=
  normalizedTrace (U (x,i) * U (shift x i,j) * (U (shift x j,i))⁻¹ * (U (x,j))⁻¹)

/-- The translation average of one oriented spatial plaquette, as in Omega's sliceP. -/
def plaquette01 {L : ℕ+} (U : Slice L) : ℝ :=
  (∑ x, face U x 0 1) / Fintype.card (Space L)

theorem plaquette_space_shift (k : Space L) (U : Slice L) :
    plaquette01 (fun (e : Space L × Fin 3) => U (e.1+k,e.2)) = plaquette01 U := by
  let W : Slice L := fun e => U (e.1+k,e.2)
  have he (x : Space L) : face W x 0 1 = face U (x+k) 0 1 := by
    have hs (i : Fin 3) : shift x i + k = shift (x+k) i := by unfold shift; abel
    simp only [W, face, hs]
  exact congrArg (· / (Fintype.card (Space L) : ℝ))
    (Fintype.sum_equiv (Equiv.addRight k) (fun x => face W x 0 1) (fun x => face U x 0 1) he)

def spatial {L : ℕ+} (U : Slice L) : ℝ :=
  ∑ x, ((1 - face U x 0 1) + (1 - face U x 0 2) + (1 - face U x 1 2))

def temporal {L : ℕ+} (U V : Slice L) (h : Vertical L) : ℝ :=
  ∑ x, ∑ i, (1 - normalizedTrace (U (x,i) * h (shift x i) * (V (x,i))⁻¹ * (h x)⁻¹))

def bond {L : ℕ+} (β : ℝ) (U V : Slice L) (h : Vertical L) : ℝ :=
  Real.exp (-β * ((spatial U + spatial V)/2 + temporal U V h))

def kernel {L : ℕ+} (β : ℝ) (haar : Measure G) (U V : Slice L) : ℝ :=
  ∫ h, bond β U V h ∂Measure.pi (fun _ => haar)

variable {L N : ℕ+}
abbrev Time (N : ℕ+) := Fin N.val

def action (U : Time N → Slice L) (h : Time N → Vertical L) : ℝ :=
  ∑ t, (spatial (U t) + temporal (U t) (U (t+1)) (h t))

/-- Half of each spatial action belongs to each adjacent bond, including the wrap. -/
theorem periodic_weight (β : ℝ) (U : Time N → Slice L) (h : Time N → Vertical L) :
    Real.exp (-β * action U h) = ∏ t, bond β (U t) (U (t+1)) (h t) := by
  unfold bond action
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 2
  have hs : ∑ t : Time N, spatial (U (t+1)) = ∑ t : Time N, spatial (U t) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div, hs]
  ring

/-- Integrating all temporal links of the rectangular Wilson lattice yields the
closed product of Wilson kernels. The insertion may depend on all spatial slices. -/
theorem integrate_temporal (β : ℝ) (haar : Measure G) [IsProbabilityMeasure haar]
    (U : Time N → Slice L) (a : ℝ) :
    (∫ h, a * Real.exp (-β * action U h)
      ∂Measure.pi (fun _ => Measure.pi (fun _ : Space L => haar))) =
      a * ∏ t, kernel β haar (U t) (U (t+1)) := by
  simp_rw [periodic_weight]
  rw [integral_const_mul, integral_fintype_prod_eq_prod]
  rfl

/-- Closed-kernel integral trace. For insertions f, the Wilson law is the
normalized product Haar integral with precisely the six positive faces per site. -/
def wilsonMoment (β : ℝ) (haar : Measure G) (f : (Time N → Slice L) → ℝ) : ℝ :=
  ∫ U, (∫ h, f U * Real.exp (-β * action U h)
    ∂Measure.pi (fun _ => Measure.pi (fun _ : Space L => haar)))
    ∂Measure.pi (fun _ => Measure.pi (fun _ => haar))

def cycleTrace (K : Slice L → Slice L → ℝ) (haar : Measure G)
    (f : (Time N → Slice L) → ℝ) : ℝ :=
  ∫ U, f U * ∏ t, K (U t) (U (t+1))
    ∂Measure.pi (fun _ => Measure.pi (fun _ => haar))

def connected (moment : ((Time N → Slice L) → ℝ) → ℝ) (d : ℕ) : ℝ :=
  let Z := moment 1
  moment (fun U => plaquette01 (U 0) * plaquette01 (U (Fin.ofNat N.val d))) / Z -
    (moment (fun U => plaquette01 (U 0)) / Z)^2

theorem wilsonMoment_eq_cycle (β : ℝ) (haar : Measure G) [IsProbabilityMeasure haar] :
    wilsonMoment (N := N) (L := L) β haar = cycleTrace (kernel β haar) haar := by
  funext f
  unfold wilsonMoment cycleTrace
  simp_rw [integrate_temporal]

theorem finite_periodic_trace (β : ℝ) (haar : Measure G) [IsProbabilityMeasure haar] (d : ℕ) :
    connected (N := N) (L := L) (wilsonMoment β haar) d =
      connected (N := N) (L := L) (cycleTrace (kernel β haar) haar) d := by
  rw [wilsonMoment_eq_cycle]

abbrev sliceLaw (L : ℕ+) := Measure.pi (fun _ : Space L × Fin 3 => PeriodicWilson.su2Haar)

private theorem trace_continuous : Continuous normalizedTrace :=
  (Complex.continuous_re.comp ((continuous_subtype_val.comp continuous_subtype_val).matrix_trace)).div_const _

theorem face_continuous (x : Space L) (i j : Fin 3) :
    Continuous (fun U : Slice L => face U x i j) := by
  unfold face
  apply trace_continuous.comp
  fun_prop

def observable (L : ℕ+) : V (Slice L) :=
  ⟨plaquette01, (continuous_finsetSum _ (fun x _ => face_continuous x 0 1)).div_const _⟩

theorem bond_continuous (β : ℝ) :
    Continuous (fun p : (Slice L × Slice L) × Vertical L => bond β p.1.1 p.1.2 p.2) := by
  have hs : Continuous (spatial (L := L)) := by
    unfold spatial
    exact continuous_finsetSum _ fun x _ =>
      (((continuous_const.sub (face_continuous x 0 1)).add
        (continuous_const.sub (face_continuous x 0 2))).add (continuous_const.sub (face_continuous x 1 2)))
  have ht : Continuous (fun p : (Slice L × Slice L) × Vertical L => temporal p.1.1 p.1.2 p.2) := by
    unfold temporal
    apply continuous_finsetSum; intro x _
    apply continuous_finsetSum; intro i _
    apply continuous_const.sub
    apply trace_continuous.comp
    fun_prop
  exact Real.continuous_exp.comp (continuous_const.mul (((hs.comp (continuous_fst.comp continuous_fst)).add
    (hs.comp (continuous_snd.comp continuous_fst))).div_const _ |>.add ht))

/-- The kernel is divided by its Perron eigenvalue when a spectral resolution is used.
The normalization factor cancels from every finite periodic expectation. -/
def normalizedKernel (L : ℕ+) (β scale : ℝ) : C(Slice L × Slice L, ℝ) :=
  ⟨fun p => kernel β PeriodicWilson.su2Haar p.1 p.2 / scale, by
    apply Continuous.div_const
    have h := continuous_parametric_integral_of_continuous (μ := Measure.pi (fun _ : Space L => PeriodicWilson.su2Haar))
      (f := fun (p : Slice L × Slice L) h => bond β p.1 p.2 h) (bond_continuous β) isCompact_univ
    simpa [kernel] using h⟩

def closingKernel (L : ℕ+) (β scale : ℝ) : Columns (Slice L) :=
  ((normalizedKernel L β scale).comp ⟨Prod.swap, continuous_swap⟩).curry

/-- The concrete integral operator on spatial slice functions. -/
def wilsonOperator (L : ℕ+) (β scale : ℝ) : Op (Slice L) :=
  let K := normalizedKernel L β scale
  let μ := sliceLaw L
  let act (f : V (Slice L)) : V (Slice L) :=
    ⟨fun x => ∫ y, K (x,y) * f y ∂μ, by
      have h := continuous_parametric_integral_of_continuous (μ := μ)
        (f := fun x y => K (x,y) * f y) (K.continuous.mul (f.continuous.comp continuous_snd)) isCompact_univ
      simpa using h⟩
  LinearMap.mkContinuous
    { toFun := act
      map_add' := by
        intro a b
        ext x
        change (∫ y, K (x,y) * (a y + b y) ∂μ) = _
        simp_rw [mul_add]
        apply integral_add
        all_goals apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        all_goals fun_prop
      map_smul' := by
        intro c a
        ext x
        change (∫ y, K (x,y) * (c * a y) ∂μ) = c * ∫ y, K (x,y) * a y ∂μ
        simp_rw [mul_left_comm (K (_,_)) c, integral_const_mul] }
    ‖K‖ (by
      intro f
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      simpa [act] using norm_integral_le_of_norm_le_const (μ := μ)
        (.of_forall fun y => (norm_mul_le (K (x,y)) (f y)).trans
          (mul_le_mul (K.norm_coe_le_norm (x,y)) (f.norm_coe_le_norm y) (norm_nonneg _) (norm_nonneg _))))

/-- Integrate a path of n forward time steps starting at x. Each step integrates
the next spatial slice and all temporal links between the two slices. -/
def wilsonSteps (β : ℝ) : ℕ → (Slice L → ℝ) → Slice L → ℝ
  | 0, f => f
  | n+1, f => fun x => ∫ y, (∫ h, bond β x y h * wilsonSteps β n f y
      ∂Measure.pi (fun _ => PeriodicWilson.su2Haar)) ∂sliceLaw L

theorem steps_operator (β scale : ℝ) (hs : scale ≠ 0) (n : ℕ) (c : ℝ) (f : V (Slice L)) (x : Slice L) :
    wilsonSteps β n (fun y => c * f y) x = c * scale^n * ((wilsonOperator L β scale ^ n) f) x := by
  induction n generalizing x with
  | zero => simp [wilsonSteps]
  | succ n ih =>
    simp_rw [wilsonSteps, ih, integral_mul_const]
    rw [pow_succ' (wilsonOperator L β scale), mul_apply_eq_comp]
    change (∫ y, kernel β PeriodicWilson.su2Haar x y * (c * scale^n * _) ∂sliceLaw L) =
      c * scale^(n+1) * ∫ y, (kernel β PeriodicWilson.su2Haar x y / scale) * _ ∂sliceLaw L
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    field_simp
    ring

/-- Direct Wilson integral with source a at 0, sink b at d, and periodic closing
bond from the final slice back to x. Its temporal extent is d+r+1. -/
def markedRing (β : ℝ) (a b : V (Slice L)) (d r : ℕ) :=
  ∫ x, a x * wilsonSteps β d (fun y => b y * wilsonSteps β r
    (fun z => kernel β PeriodicWilson.su2Haar z x) y) x ∂sliceLaw L

set_option maxHeartbeats 900000 in
theorem markedRing_trace (β scale : ℝ) (hs : scale ≠ 0) (a b : V (Slice L)) (d r : ℕ) :
    let T := wilsonOperator L β scale
    let M := ContinuousLinearMap.mul ℝ (V (Slice L))
    markedRing β a b d r = (scale * scale^r * scale^d) *
      cutTrace (sliceLaw L) ((((M a).comp (T^d)).comp (M b)).comp (T^r)) (closingKernel L β scale) := by
  intro T M
  unfold markedRing
  change _ = _ * (∫ x, _ ∂sliceLaw L)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  let k := closingKernel L β scale x
  have hk : (fun z => kernel β PeriodicWilson.su2Haar z x) = (fun z => scale * k z) := by
    funext z
    change _ = scale * (kernel β PeriodicWilson.su2Haar z x / scale)
    field_simp
  rw [hk]
  have hr : wilsonSteps β r (fun z => scale * k z) =
      fun y => scale * scale^r * (((T^r) k) y) := funext (steps_operator β scale hs r scale k)
  rw [hr]
  have hf : (fun y => b y * (scale * scale^r * ((T^r) k) y)) =
      (fun y => (scale * scale^r) * (b * (T^r) k) y) := by
    funext y; simp only [ContinuousMap.mul_apply]; ring
  rw [hf, steps_operator β scale hs]
  change a x * (_ * (((T^d) (b * (T^r) k)) x)) = _ * (a x * (((T^d) (b * (T^r) k)) x))
  ring

def ringConnected (β : ℝ) (L : ℕ+) (d r : ℕ) :=
  let m := markedRing (L := L) β
  let a := observable L
  m a a d r / m 1 1 d r - (m a 1 d r / m 1 1 d r)^2

theorem ringConnected_thermal (β scale : ℝ) (hs : scale ≠ 0) (d r : ℕ) :
    ringConnected β L d r = thermal (sliceLaw L) (wilsonOperator L β scale)
      (closingKernel L β scale) (observable L) d r := by
  unfold ringConnected thermal
  simp only [markedRing_trace β scale hs]
  have h1 : ContinuousLinearMap.mul ℝ (V (Slice L)) 1 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro f
    exact one_mul f
  simp [h1, mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero hs (pow_ne_zero _ hs)) (pow_ne_zero _ hs))]



theorem normalizedTrace_scalar (u : G) : normalizedTrace u = (u.val.val 0 0).re := by
  obtain ⟨h, _⟩ := (show u.val.val ∈ FundamentalSU2.quaternionAlgebra from u.property)
  let A : FundamentalSU2.M := u.val.val
  change A.trace.re / 2 = (A 0 0).re
  have hd : A 1 1 = (starRingEnd ℂ) (A 0 0) := h
  simp [Matrix.trace_fin_two, hd]

open scoped Quaternion ComplexConjugate

/-- Scalar, i, j and k in the order used by the Omega link buffers. -/
private def matrixQuaternion (A : FundamentalSU2.M) : Quaternion ℝ :=
  ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩

def linkQuaternion (u : G) := matrixQuaternion u.val.val

theorem linkQuaternion_mul (u v : G) : linkQuaternion (u*v) = linkQuaternion u * linkQuaternion v := by
  let A : FundamentalSU2.M := u.val.val
  let B : FundamentalSU2.M := v.val.val
  obtain ⟨hd, hc⟩ := (show B ∈ FundamentalSU2.quaternionAlgebra from v.property)
  change B 1 1 = conj (B 0 0) at hd
  change B 1 0 = -conj (B 0 1) at hc
  change matrixQuaternion (A*B) = matrixQuaternion A * matrixQuaternion B
  ext <;> simp [matrixQuaternion, Matrix.mul_apply, Fin.sum_univ_two, hd, hc,
    Complex.mul_re, Complex.mul_im, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul] <;> ring

theorem linkQuaternion_inv (u : G) : linkQuaternion u⁻¹ = star (linkQuaternion u) := by
  let A : FundamentalSU2.M := u.val.val
  obtain ⟨_, hc⟩ := (show A ∈ FundamentalSU2.quaternionAlgebra from u.property)
  change A 1 0 = -conj (A 0 1) at hc
  change matrixQuaternion (star A) = star (matrixQuaternion A)
  ext <;> simp [matrixQuaternion, Matrix.star_apply,hc]

/-- The scalar of the ordered four Hamilton products, including both return links. -/
theorem face_quaternion (U : Slice L) (x : Space L) (i j : Fin 3) :
    face U x i j =
      (linkQuaternion (U (x,i)) * linkQuaternion (U (shift x i,j)) *
        star (linkQuaternion (U (shift x j,i))) * star (linkQuaternion (U (x,j)))).re := by
  have scalar (u : G) : normalizedTrace u = (linkQuaternion u).re := normalizedTrace_scalar u
  simp only [face, scalar, linkQuaternion_mul, linkQuaternion_inv]

def changeGauge (h : Vertical L) (U : Slice L) : Slice L :=
  fun e => h e.1 * U e * (h (shift e.1 e.2))⁻¹

def physicalSlices (L : ℕ+) : Submodule ℝ (V (Slice L)) where
  carrier := {f | ∀ h U, f (changeGauge h U) = f U}
  zero_mem' := by intro h U; rfl
  add_mem' := fun hf hg h U => by simp [ContinuousMap.add_apply, hf h U, hg h U]
  smul_mem' := fun r f hf h U => by simp [hf h U]

private theorem trace_swap (a b : G) : normalizedTrace (a*b) = normalizedTrace (b*a) := by
  change (a.val.val * b.val.val).trace.re / 2 = (b.val.val * a.val.val).trace.re / 2
  rw [Matrix.trace_mul_comm]

theorem face_gauge (h : Vertical L) (U : Slice L) (x : Space L) (i j : Fin 3) :
    face (changeGauge h U) x i j = face U x i j := by
  have hs : shift (shift x i) j = shift (shift x j) i := by unfold shift; abel
  unfold face changeGauge
  have he : (h x * U (x,i) * (h (shift x i))⁻¹) *
      (h (shift x i) * U (shift x i,j) * (h (shift (shift x i) j))⁻¹) *
      (h (shift x j) * U (shift x j,i) * (h (shift (shift x j) i))⁻¹)⁻¹ *
      (h x * U (x,j) * (h (shift x j))⁻¹)⁻¹ =
      h x * (U (x,i) * U (shift x i,j) * (U (shift x j,i))⁻¹ * (U (x,j))⁻¹) * (h x)⁻¹ := by
    rw [hs]; group
  rw [he, trace_swap _ ((h x)⁻¹)]
  simp

theorem observable_preserves_physical {f : V (Slice L)} (hf : f ∈ physicalSlices L) :
    observable L * f ∈ physicalSlices L := by
  intro h U
  change plaquette01 (changeGauge h U) * f (changeGauge h U) = plaquette01 U * f U
  simp only [plaquette01, face_gauge, hf h U]

private theorem temporal_gauge_left (g h : Vertical L) (U W : Slice L) :
    temporal (changeGauge g U) W (g*h) = temporal U W h := by
  unfold temporal
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have he : changeGauge g U (x,i) * (g*h) (shift x i) * (W (x,i))⁻¹ * ((g*h) x)⁻¹ =
      g x * (U (x,i) * h (shift x i) * (W (x,i))⁻¹ * (h x)⁻¹) * (g x)⁻¹ := by
    simp only [changeGauge, Pi.mul_apply]; group
  rw [he, trace_swap _ ((g x)⁻¹)]
  simp

theorem kernel_gauge_left (β : ℝ) (g : Vertical L) (U W : Slice L) :
    kernel β PeriodicWilson.su2Haar (changeGauge g U) W = kernel β PeriodicWilson.su2Haar U W := by
  let ν := Measure.pi (fun _ : Space L => PeriodicWilson.su2Haar)
  have he := integral_mul_left_eq_self (μ := ν) (bond β (changeGauge g U) W) g
  change (∫ h, bond β (changeGauge g U) W h ∂ν) = _
  rw [← he]
  simp only [bond, spatial, face_gauge, temporal_gauge_left]
  rfl

theorem operator_physical (β scale : ℝ) (f : V (Slice L)) :
    wilsonOperator L β scale f ∈ physicalSlices L := by
  intro g U
  change (∫ y, (kernel β _ (changeGauge g U) y / scale) * f y ∂sliceLaw L) =
    ∫ y, (kernel β _ U y / scale) * f y ∂sliceLaw L
  simp only [kernel_gauge_left]

private theorem trace_inv (u : G) : normalizedTrace u⁻¹ = normalizedTrace u := by
  rw [normalizedTrace_scalar, normalizedTrace_scalar]
  change ((star (u.val.val : FundamentalSU2.M)) 0 0).re = _
  simp [Matrix.star_apply]

private theorem temporal_reverse (U W : Slice L) (h : Vertical L) :
    temporal W U h⁻¹ = temporal U W h := by
  unfold temporal
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Pi.inv_apply, inv_inv]
  rw [trace_swap _ (h x), ← trace_inv (U (x,i) * h (shift x i) * (W (x,i))⁻¹ * (h x)⁻¹)]
  congr 1
  group

/-- Reversing a single time bond preserves its integrated Wilson weight. -/
theorem kernel_symmetric (β : ℝ) (U W : Slice L) :
    kernel β PeriodicWilson.su2Haar U W = kernel β PeriodicWilson.su2Haar W U := by
  let ν := Measure.pi (fun _ : Space L => PeriodicWilson.su2Haar)
  letI : ν.IsMulRightInvariant := ⟨fun g => by
    letI := Measure.isProbabilityMeasure_map (μ := ν) (continuous_mul_const g).measurable.aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
  letI : ν.inv.IsHaarMeasure := {}
  letI : IsProbabilityMeasure ν.inv := Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  letI : ν.IsInvInvariant := ⟨Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
  have he := integral_inv_eq_self (bond β W U) ν
  change _ = (∫ h, bond β W U h ∂ν)
  rw [← he]
  apply integral_congr_ae
  filter_upwards with h
  simp only [bond, temporal_reverse, add_comm (spatial W) (spatial U)]

set_option maxHeartbeats 900000 in
theorem kernel_pos (β : ℝ) (U W : Slice L) : 0 < kernel β PeriodicWilson.su2Haar U W := by
  let ν := Measure.pi (fun _ : Space L => PeriodicWilson.su2Haar)
  have hpair : Continuous (fun h : Vertical L => ((U,W),h)) := continuous_const.prodMk continuous_id
  have hc := (bond_continuous (L := L) β).comp hpair
  have hi := hc.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  exact integral_exp_pos (f := fun h : Vertical L => -β * ((spatial U + spatial W)/2 + temporal U W h)) hi


theorem positive_partition (β : ℝ) :
    0 < wilsonMoment (N := N) (L := L) β PeriodicWilson.su2Haar 1 := by
  unfold wilsonMoment
  simp_rw [Pi.one_apply, integrate_temporal, one_mul]
  let w := fun U : Time N → Slice L => ∏ t, kernel β PeriodicWilson.su2Haar (U t) (U (t+1))
  have hp (U) : 0 < w U := Finset.prod_pos fun t _ => kernel_pos β _ _
  have hc : Continuous w := by
    apply continuous_finsetProd
    intro t _
    have hpair : Continuous (fun U : Time N → Slice L => (U t, U (t+1))) :=
      (continuous_apply t).prodMk (continuous_apply (t+1))
    have hk := (normalizedKernel L β 1).continuous.comp hpair
    simpa [normalizedKernel, Function.comp_def] using hk
  apply (integral_pos_iff_support_of_nonneg (fun U => (hp U).le)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have full : Function.support w = Set.univ := by ext x; simp [(hp x).ne', Function.mem_support]
  simp [full]

theorem cycle_time_shift (K : Slice L → Slice L → ℝ) (haar : Measure G) [IsProbabilityMeasure haar]
    (s : Time N) (f : (Time N → Slice L) → ℝ) :
    cycleTrace K haar (fun U => f (fun t => U (t+s))) = cycleTrace K haar f := by
  let e := Equiv.addRight s
  let μ := Measure.pi (fun _ : Space L × Fin 3 => haar)
  let p := (MeasurableEquiv.piCongrLeft (fun _ : Time N => Slice L) e).symm
  have mp := (measurePreserving_piCongrLeft (fun _ : Time N => μ) e).symm
  have hp (U : Time N → Slice L) : p U = fun t => U (t+s) := by
    funext t
    exact Equiv.piCongrLeft_symm_apply (fun _ => Slice L) e U t
  have hprod (U : Time N → Slice L) : (∏ t, K ((p U) t) ((p U) (t+1))) =
      ∏ t, K (U t) (U (t+1)) := by
    rw [hp]
    apply Fintype.prod_equiv e
    intro t
    dsimp [e]
    rw [add_right_comm]
  have hh := mp.integral_comp' (fun U => f U * ∏ t, K (U t) (U (t+1)))
  change (∫ U, f (p U) * ∏ t, K ((p U) t) ((p U) (t+1)) ∂Measure.pi (fun _ => μ)) = _ at hh
  simp_rw [hprod, hp] at hh
  exact hh

theorem wilson_time_shift (β : ℝ) (s : Time N) (f : (Time N → Slice L) → ℝ) :
    wilsonMoment β PeriodicWilson.su2Haar (fun U => f (fun t => U (t+s))) =
      wilsonMoment β PeriodicWilson.su2Haar f := by
  rw [wilsonMoment_eq_cycle]
  exact cycle_time_shift _ _ _ _

private theorem steps_eq (β : ℝ) (n : ℕ) (f : Slice L → ℝ) (x : Slice L) :
    KernelCycle.steps (sliceLaw L) (normalizedKernel L β 1) n f x = wilsonSteps β n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [KernelCycle.steps, wilsonSteps, integral_mul_const, ih]
    apply integral_congr_ae
    filter_upwards with y
    change (kernel β PeriodicWilson.su2Haar x y / 1) * _ = kernel β PeriodicWilson.su2Haar x y * _
    rw [div_one]

abbrev extent (d r : ℕ) : ℕ+ := ⟨r+d+1, by omega⟩

theorem cycle_eq_ring (β : ℝ) (a b : V (Slice L)) (d r : ℕ) :
    cycleTrace (N := extent d r) (kernel β PeriodicWilson.su2Haar) PeriodicWilson.su2Haar
      (fun U => a (U 0) * b (U (KernelCycle.mark r d))) = markedRing β a b d r := by
  have h := KernelCycle.cycle_integral (sliceLaw L) (normalizedKernel L β 1) a b d r
  have hk (x y : Slice L) : normalizedKernel L β 1 (x,y) = kernel β PeriodicWilson.su2Haar x y := div_one _
  change (∫ U : Fin (r+d+1) → Slice L, _ * ∏ t, normalizedKernel L β 1 (U t,U (t+1)) ∂_) =
      (∫ x, a x * KernelCycle.steps (sliceLaw L) (normalizedKernel L β 1) d _ x ∂_) at h
  simp only [steps_eq, hk] at h
  exact h

theorem connected_eq_ring (β : ℝ) (d r : ℕ) :
    connected (N := extent d r) (wilsonMoment (L := L) β PeriodicWilson.su2Haar) d =
      ringConnected β L d r := by
  rw [finite_periodic_trace]
  let tr := cycleTrace (N := extent d r) (L := L) (kernel β PeriodicWilson.su2Haar) PeriodicWilson.su2Haar
  let a := observable L
  have hd : Fin.ofNat (extent d r).val d = KernelCycle.mark r d := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (show d < r+d+1 by omega)
  have z : tr (fun _ => (1 : ℝ)) = markedRing β (1 : V (Slice L)) 1 d r := by
    simpa only [ContinuousMap.one_apply, mul_one] using cycle_eq_ring (L := L) β (1 : V (Slice L)) 1 d r
  have one : tr (fun U => a (U 0)) = markedRing β a 1 d r := by
    simpa only [ContinuousMap.one_apply, mul_one] using cycle_eq_ring β a 1 d r
  have two := cycle_eq_ring β a a d r
  change tr (fun U => a (U 0) * a (U (Fin.ofNat (extent d r).val d))) / tr (fun _ => (1:ℝ)) -
    (tr (fun U => a (U 0)) / tr (fun _ => (1:ℝ)))^2 = _
  rw [hd, z, one]
  exact congrArg (fun v => v / markedRing β (1 : V (Slice L)) 1 d r -
    (markedRing β a 1 d r / markedRing β (1 : V (Slice L)) 1 d r)^2) two

/-- Finite rectangular Wilson expectation at N = d + r + 1, in operator form. -/
theorem wilson_plaquette_periodic_trace (β : ℝ) (d r : ℕ) :
    connected (N := extent d r) (wilsonMoment (L := L) β PeriodicWilson.su2Haar) d =
      thermal (sliceLaw L) (wilsonOperator L β 1) (closingKernel L β 1) (observable L) d r :=
  (connected_eq_ring β d r).trans (ringConnected_thermal β 1 one_ne_zero d r)

theorem operator_symmetric (β scale : ℝ) (f g : V (Slice L)) :
    pairing (sliceLaw L) f (wilsonOperator L β scale g) =
      pairing (sliceLaw L) (wilsonOperator L β scale f) g := by
  let K := normalizedKernel L β scale
  let μ := sliceLaw L
  have hc : Continuous (fun p : Slice L × Slice L => f p.1 * (K p * g p.2)) :=
    (f.continuous.comp continuous_fst).mul (K.continuous.mul (g.continuous.comp continuous_snd))
  change (∫ x, f x * (∫ y, K (x,y) * g y ∂μ) ∂μ) =
    ∫ y, (∫ x, K (y,x) * f x ∂μ) * g y ∂μ
  simp_rw [← integral_const_mul, ← integral_mul_const]
  rw [integral_integral_swap (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  change f x * (kernel β _ x y / scale * g y) = kernel β _ y x / scale * f x * g y
  rw [kernel_symmetric β x y]
  ring

theorem swap_wrap_excess {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    q^3 < (q^3+q^5)/(1+q^8) := by
  apply (lt_div_iff₀ (by positivity)).mpr
  have h := mul_pos (pow_pos h0 5) (sub_pos.mpr (pow_lt_one₀ h0.le h1 (by decide : 6 ≠ 0)))
  nlinarith

#print axioms operator_symmetric
#print axioms kernel_symmetric
#print axioms operator_physical
#print axioms plaquette_space_shift
#print axioms face_quaternion
#print axioms normalizedTrace_scalar
#print axioms observable_preserves_physical
#print axioms positive_partition
#print axioms wilson_time_shift
#print axioms wilson_plaquette_periodic_trace
#print axioms connected_eq_ring
#print axioms swap_wrap_excess
#print axioms steps_operator
#print axioms markedRing_trace
#print axioms ringConnected_thermal

def swap : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;1,0]
def twoState (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,q]

theorem swap_regression (q : ℝ) :
    ((twoState q ^ 5 * swap * twoState q ^ 3 * swap).trace / (twoState q ^ 8).trace -
      ((twoState q ^ 8 * swap).trace / (twoState q ^ 8).trace)^2) = (q^3+q^5)/(1+q^8) ∧
    (swap * twoState q ^ 3 * swap) 0 0 = q^3 := by
  norm_num [twoState, swap, pow_succ, Matrix.trace_fin_two, Matrix.mul_fin_two]

#print axioms periodic_weight
#print axioms integrate_temporal
#print axioms finite_periodic_trace
#print axioms swap_regression

end
end YangMills.PlaquetteTransfer
