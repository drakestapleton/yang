import DyadicPartition
import OneLinkTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open MeasureTheory Set Real
open YangMills.DyadicPartition YangMills.DyadicExp YangMills.DyadicTrig
open YangMills.OneLinkTransport

namespace YangMills.DyadicPolarFlux
noncomputable section

private theorem norm_pos (r : ℝ) : 0 < ∫ t in 0..π, weight r t := by
  apply intervalIntegral.integral_pos pi_pos
  · unfold weight; fun_prop
  · intro t _; unfold weight; positivity
  · refine ⟨π/2, ⟨by positivity, by linarith [pi_pos]⟩, ?_⟩
    simp [weight]

theorem mean_range (r : ℝ) : |meanCos r| ≤ 1 := by
  have w : Continuous (weight r) := by unfold weight; fun_prop
  have a : Continuous (fun t => weight r t * cos t) := w.mul continuous_cos
  have pos (t : ℝ) : 0 ≤ weight r t := by unfold weight; positivity
  have hi := intervalIntegral.integral_mono_on (μ := volume) pi_pos.le (a.intervalIntegrable _ _)
    (w.intervalIntegrable _ _) (fun t _ => mul_le_of_le_one_right (pos t) (cos_le_one t))
  have lo := intervalIntegral.integral_mono_on (μ := volume) pi_pos.le (w.neg.intervalIntegrable _ _)
    (a.intervalIntegrable _ _) (fun t _ => show -weight r t ≤ weight r t*cos t by
      linarith [mul_le_mul_of_nonneg_left (neg_one_le_cos t) (pos t)])
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at lo
  rw [abs_le, meanCos, le_div_iff₀ (norm_pos r), div_le_iff₀ (norm_pos r)]
  constructor <;> linarith

private theorem end_zero (r : ℝ) : polarFlux r π = 0 := by
  have hw : Continuous (weight r) := by unfold weight; fun_prop
  simp only [polarFlux, mul_sub]
  have ha : Continuous (fun x => weight r x * cos x) := hw.mul continuous_cos
  have hb : Continuous (fun x => weight r x * meanCos r) := hw.mul continuous_const
  rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const]
  unfold meanCos
  field_simp [(norm_pos r).ne']
  simp

private theorem cap_exp {v : ℝ} (hv : v ≤ 1/2) : exp v ≤ 2 := by
  have h : exp v ^ 2 ≤ exp 1 := by rw [← exp_nat_mul]; apply exp_le_exp.mpr; norm_num; linarith
  nlinarith [exp_one_lt_d9, exp_pos v]

private theorem density_toward_pole {r u t : ℝ} (hr : |r| ≤ 2)
    (hu : u ∈ Icc 0 t) (ht : t ≤ π/2048) : weight r u ≤ 2*weight r t := by
  have ht0 := hu.1.trans hu.2
  have h2 : t ≤ π/2 := by linarith [pi_pos]
  have su := sin_nonneg_of_nonneg_of_le_pi hu.1 (by linarith [hu.2, pi_pos] : u ≤ π)
  have sm := sin_le_sin_of_le_of_le_pi_div_two (by linarith [hu.1,pi_pos]) h2 hu.2
  have sq := pow_le_pow_left₀ su sm 2
  have hdist := abs_cos_sub_cos_le u t
  rw [abs_of_nonpos (sub_nonpos.mpr hu.2)] at hdist
  have absBound := mul_le_mul hr hdist (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  rw [← abs_mul] at absBound
  have ex := cap_exp (show r*(cos u-cos t) ≤ 1/2 by
    linarith [(le_abs_self _).trans absBound, hu.1, Real.pi_lt_four])
  have e : exp (r*cos u) ≤ 2*exp (r*cos t) := by
    rw [show r*cos u = r*(cos u-cos t)+r*cos t by ring, exp_add]
    exact mul_le_mul_of_nonneg_right ex (exp_pos _).le
  unfold weight
  calc _ ≤ sin t^2*(2*exp (r*cos t)) := mul_le_mul sq e (exp_pos _).le (sq_nonneg _)
       _ = _ := by ring

/-- The inward flux divided by the density is uniformly bounded on a pole cell,
including its zero-density endpoint in the real-division convention. -/
private theorem near_zero {r m t : ℝ} (hr : |r| ≤ 2) (hm : |m| ≤ 1)
    (ht : t ∈ Icc 0 (π/2048)) :
    (∫ u in 0..t, weight r u*(cos u-m))^2 / weight r t ≤
    16*(π/2048)^2 * weight r t := by
  let f := fun u => weight r u*(cos u-m)
  have c : Continuous f := by unfold f weight; fun_prop
  have w : 0 ≤ weight r t := by unfold weight; positivity
  have cap (u : ℝ) (h : u ∈ Icc 0 t) : |f u| ≤ 4*weight r t := by
    have wu : 0 ≤ weight r u := by unfold weight; positivity
    have delta : |cos u-m| ≤ 2 := (abs_sub _ _).trans (by linarith [abs_cos_le_one u])
    simp only [f, abs_mul, abs_of_nonneg wu]
    nlinarith [mul_le_mul (density_toward_pole hr h ht.2) delta (abs_nonneg _) (mul_nonneg (by norm_num) w)]
  have absint := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f) ht.1
  have mono := intervalIntegral.integral_mono_on (μ := volume) ht.1 (c.abs.intervalIntegrable _ _)
    (intervalIntegrable_const (c := 4*weight r t)) cap
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at mono
  have b := absint.trans (mono.trans (mul_le_mul_of_nonneg_right ht.2 (by positivity)))
  have square := pow_le_pow_left₀ (abs_nonneg _) b 2
  rw [sq_abs] at square
  rcases w.eq_or_lt with zero | positive
  · simp [← zero]
  · apply (div_le_iff₀ positive).2
    convert square using 1; ring

/-- Centering cancels the complete flux, so the last cell can be integrated from π inward. -/
private theorem reflected_flux (r t : ℝ) :
    polarFlux r (π-t) = ∫ u in 0..t, weight (-r) u*(cos u - (-meanCos r)) := by
  let f := fun u => weight r u*(cos u-meanCos r)
  have c : Continuous f := by unfold f weight; fun_prop
  have add := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (c.intervalIntegrable 0 (π-t))
    (c.intervalIntegrable (π-t) π)
  have zero : (∫ u in 0..π, f u) = 0 := end_zero r
  rw [zero] at add
  have sub := intervalIntegral.integral_comp_sub_left (f := f) (a := 0) (b := t) π
  rw [sub_zero] at sub
  have form : (fun u => f (π-u)) = fun u => -(weight (-r) u*(cos u-(-meanCos r))) := by
    funext u; simp [f,weight,Real.cos_pi_sub,Real.sin_pi_sub]; ring
  rw [form, intervalIntegral.integral_neg] at sub
  change (∫ u in 0..(π-t), f u) = _
  linarith

theorem two_pole_cells {r t : ℝ} (hr : |r| ≤ 2) (ht : t ∈ Icc 0 (π/2048)) :
    polarFlux r t ^ 2 / weight r t ≤ 16*(π/2048)^2 * weight r t ∧
    polarFlux r (π-t) ^ 2 / weight r (π-t) ≤ 16*(π/2048)^2 * weight r (π-t) := by
  refine ⟨near_zero hr (mean_range r) ht, ?_⟩
  rw [reflected_flux, show weight r (π-t) = weight (-r) t by simp [weight,Real.cos_pi_sub,Real.sin_pi_sub]]
  apply near_zero (by simpa using hr) (by simpa using mean_range r) ht

def poleCost (i : ℕ) (rl rh : ℤ) := ceilDiv (16 * weightHi (angleCell i) rl rh) 4194304

/-- The actual rounded end-cell branch of the inward energy replay bounds F²/p. -/
theorem end_cell_cost {i : ℕ} (edge : i = 0 ∨ i = 2047) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q)
    (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    polarFlux r t ^ 2 / weight r t ≤ π^2 * ((poleCost i rl rh : ℝ)/q) := by
  have hi : i < 2048 := by rcases edge with e|e <;> omega
  have hR : |r| ≤ 2 := by
    rw [abs_of_nonneg hr]
    have v : (rh:ℝ) ≤ 2*q := by exact_mod_cast h2
    norm_num [q] at hh v ⊢; linarith
  have pol : polarFlux r t^2/weight r t ≤ 16*(π/2048)^2*weight r t := by
    rcases edge with e|e
    · subst i
      exact (two_pole_cells hR (by norm_num [angle, Set.mem_Icc] at ht ⊢; exact ht)).1
    · subst i
      have z : π-t ∈ Icc 0 (π/2048) := by
        obtain ⟨a,b⟩ := ht
        norm_num [angle] at a b; constructor <;> linarith
      simpa using (two_pole_cells hR z).2
  have w : weight r t ≤ (weightHi (angleCell i) rl rh:ℝ)/q :=
    (weight_sound hi ht hr hl hh (exponent_range i h0 h1 h2).1 (exponent_range i h0 h1 h2).2).2
  have u := Int.ediv_mul_le (-(16*weightHi (angleCell i) rl rh)) (show (4194304:ℤ) ≠ 0 by decide)
  have v : (16:ℝ)*weightHi (angleCell i) rl rh ≤ (poleCost i rl rh:ℝ)*4194304 := by
    unfold poleCost ceilDiv
    exact_mod_cast (show 16*weightHi (angleCell i) rl rh ≤ -((-(16*weightHi (angleCell i) rl rh))/4194304)*4194304 by omega)
  have f : 16*((π:ℝ)/2048)^2*((weightHi (angleCell i) rl rh:ℝ)/q) ≤ π^2*((poleCost i rl rh:ℝ)/q) := by
    have t' := mul_le_mul_of_nonneg_left v (sq_nonneg π)
    norm_num [q] at *; linarith
  exact pol.trans ((mul_le_mul_of_nonneg_left w (by positivity)).trans f)

def ratioLo (x zl zh : ℤ) := min (x*q/zl) (x*q/zh)
def ratioHi (x zl zh : ℤ) := max (ceilDiv (x*q) zl) (ceilDiv (x*q) zh)

private theorem ratio_bounds (x zl zh : ℤ) {v : ℝ} (lz : 0 < zl) (lh : (zl:ℝ) ≤ v) (hh : v ≤ (zh:ℝ)) :
    (ratioLo x zl zh:ℝ)/q ≤ (x:ℝ)/v ∧ (x:ℝ)/v ≤ (ratioHi x zl zh:ℝ)/q := by
  have vl : 0 < (zl:ℝ) := by exact_mod_cast lz
  have vp := vl.trans_le lh
  have vh := vp.trans_le hh
  have hz : 0 < zh := by exact_mod_cast vh
  have qpos : (0:ℝ) < q := by norm_num [q]
  have bottom (k : ℤ) (hk : 0 < k) : ((x*q/k : ℤ):ℝ)/q ≤ (x:ℝ)/k := by
    apply (div_le_div_iff₀ qpos (by exact_mod_cast hk)).2
    exact_mod_cast Int.ediv_mul_le (x*q) hk.ne'
  have top (k : ℤ) (hk : 0 < k) : (x:ℝ)/k ≤ (ceilDiv (x*q) k:ℝ)/q := by
    apply (div_le_div_iff₀ (by exact_mod_cast hk) qpos).2
    exact_mod_cast (ceil_mul_bound (x*q) hk)
  have lo1 : (ratioLo x zl zh:ℝ)/q ≤ (x:ℝ)/zl :=
    (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) qpos.le).trans (bottom _ lz)
  have lo2 : (ratioLo x zl zh:ℝ)/q ≤ (x:ℝ)/zh :=
    (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) qpos.le).trans (bottom _ hz)
  have hi1 : (x:ℝ)/zl ≤ (ratioHi x zl zh:ℝ)/q :=
    (top _ lz).trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) qpos.le)
  have hi2 : (x:ℝ)/zh ≤ (ratioHi x zl zh:ℝ)/q :=
    (top _ hz).trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) qpos.le)
  by_cases hx : 0 ≤ (x:ℝ)
  · exact ⟨lo2.trans (div_le_div_of_nonneg_left hx vp hh), (div_le_div_of_nonneg_left hx vl lh).trans hi1⟩
  · refine ⟨lo1.trans ((div_le_div_iff₀ vl vp).2 (mul_le_mul_of_nonpos_left lh (le_of_not_ge hx))),
      ((div_le_div_iff₀ vp vh).2 (mul_le_mul_of_nonpos_left hh (le_of_not_ge hx))).trans hi2⟩

def meanLo (rl rh : ℤ) := ratioLo (averageLo momentLo rl rh) (averageLo weightLo rl rh) (averageHi weightHi rl rh)
def meanHi (rl rh : ℤ) := ratioHi (averageHi momentHi rl rh) (averageLo weightLo rl rh) (averageHi weightHi rl rh)

/-- Both signs of the rounded numerator are retained when normalizing the polar flux. -/
theorem centered_mean_sound {r : ℝ} {rl rh : ℤ} (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    (meanLo rl rh : ℝ)/q ≤ meanCos r ∧ meanCos r ≤ (meanHi rl rh : ℝ)/q := by
  obtain ⟨z,m⟩ := partition_and_moment hr hl hh h0 h1 h2
  obtain ⟨zl,zh⟩ := average_bounds z
  obtain ⟨ml,mh⟩ := average_bounds m
  let c := π/(q:ℝ)
  have cp : 0 < c := by dsimp [c,q]; positivity
  let Z := (∫ t in 0..π, polarWeight r t)/c
  let M := (∫ t in 0..π, cos t*polarWeight r t)/c
  have a : (averageLo weightLo rl rh:ℝ) ≤ Z := (le_div_iff₀ cp).2 (by simpa [c,mul_comm] using zl)
  have b : Z ≤ (averageHi weightHi rl rh:ℝ) := (div_le_iff₀ cp).2 (by simpa [c,mul_comm] using zh)
  have v := normalizer_lower_pos h0 h1 h2
  have zp : 0 < Z := lt_of_lt_of_le (by exact_mod_cast v) a
  have e : (averageLo momentLo rl rh:ℝ) ≤ M := (le_div_iff₀ cp).2 (by simpa [c,mul_comm] using ml)
  have f : M ≤ (averageHi momentHi rl rh:ℝ) := (div_le_iff₀ cp).2 (by simpa [c,mul_comm] using mh)
  have ident : meanCos r = M/Z := by
    unfold meanCos M Z; simp only [polarWeight,weight]; simp_rw [mul_comm (cos _)]
    field_simp [cp.ne']
  rw [ident]
  exact ⟨(ratio_bounds _ _ _ v a b).1.trans (div_le_div_of_nonneg_right e zp.le),
    (div_le_div_of_nonneg_right f zp.le).trans (ratio_bounds _ _ _ v a b).2⟩

/-- Both halves are integrated in the inward coordinate s, beginning at a pole. -/
def physical (back : Bool) (s : ℝ) := if back then π-s else s
def index (back : Bool) (j : ℕ) := if back then 2047-j else j
def source (back : Bool) (r s : ℝ) :=
  let t := physical back s
  (if back then meanCos r - cos t else cos t - meanCos r) * weight r t

private theorem inward (back : Bool) (r s : ℝ) :
    (∫ u in 0..s, source back r u) = polarFlux r (physical back s) := by
  cases back with
  | false => simp only [source,physical,Bool.false_eq_true,if_false,polarFlux]; apply intervalIntegral.integral_congr; intro t _; ring
  | true =>
    simp only [physical,if_true,reflected_flux]
    apply intervalIntegral.integral_congr
    intro t _; simp [source,physical,weight,cos_pi_sub,sin_pi_sub]; ring

private theorem grid_physical (back : Bool) {j : ℕ} (hj : j < 1024) {t : ℝ}
    (ht : t ∈ Icc (angle 11 j) (angle 11 (j+1))) :
    physical back t ∈ Icc (angle 11 (index back j)) (angle 11 (index back j+1)) := by
  cases back with
  | false => exact ht
  | true =>
    obtain ⟨l,h⟩ := ht
    simp only [physical,index,if_true]
    have hsub : j ≤ 2047 := by omega
    simp [angle, Nat.cast_sub hsub] at *
    constructor <;> linarith

def lowerSlope (back : Bool) (c : Cell) (ml mh wl wh : ℤ) :=
  loMul (if back then ml-c.cosHi else c.cosLo-mh) wl wh
def upperSlope (back : Bool) (c : Cell) (ml mh wl wh : ℤ) :=
  hiMul (if back then mh-c.cosLo else c.cosHi-ml) wl wh

def increment (lower back : Bool) (j : ℕ) (rl rh : ℤ) :=
  let c := angleCell (index back j)
  (if lower then lowerSlope else upperSlope) back c (meanLo rl rh) (meanHi rl rh) (weightLo c rl rh) (weightHi c rl rh)

theorem slope_sound (back : Bool) {j : ℕ} (hj : j < 1024) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 j) (angle 11 (j+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    (increment true back j rl rh:ℝ)/q ≤ source back r t ∧ source back r t ≤ (increment false back j rl rh:ℝ)/q := by
  let i := index back j
  have hi : i < 2048 := by cases back <;> simp [i,index] <;> omega
  have ht' := grid_physical back hj ht
  obtain ⟨cl,ch,_,_⟩ := grid_enclosure hi ht'
  obtain ⟨ml,mh⟩ := centered_mean_sound hr hl hh h0 h1 h2
  obtain ⟨wl,wh⟩ := weight_sound hi ht' hr hl hh (exponent_range i h0 h1 h2).1 (exponent_range i h0 h1 h2).2
  let c := angleCell i
  let l := if back then meanLo rl rh-c.cosHi else c.cosLo-meanHi rl rh
  let h := if back then meanHi rl rh-c.cosLo else c.cosHi-meanLo rl rh
  let delta := if back then meanCos r-cos (physical back t) else cos (physical back t)-meanCos r
  have low : (l:ℝ)/q ≤ delta := by
    change (c.cosLo:ℝ)/q ≤ _ at cl; change _ ≤ (c.cosHi:ℝ)/q at ch
    cases back <;> simp only [l,delta,Bool.false_eq_true,if_true,if_false,Int.cast_sub, sub_div] at * <;> linarith
  have high : delta ≤ (h:ℝ)/q := by
    change (c.cosLo:ℝ)/q ≤ _ at cl; change _ ≤ (c.cosHi:ℝ)/q at ch
    cases back <;> simp only [h,delta,Bool.false_eq_true,if_true,if_false,Int.cast_sub, sub_div] at * <;> linarith
  have pos : 0 ≤ polarWeight r (physical back t) := by unfold polarWeight; positivity
  exact ⟨(mul_bounds l _ _ wl wh).1.trans (mul_le_mul_of_nonneg_right low pos),
    (mul_le_mul_of_nonneg_right high pos).trans (mul_bounds h _ _ wl wh).2⟩

def runningSlope (lower back : Bool) (j : ℕ) (rl rh : ℤ) := ∑ k ∈ Finset.range j, increment lower back k rl rh

private theorem width (j : ℕ) : angle 11 (j+1) - angle 11 j = π/2048 := by
  simp only [angle,Nat.cast_add,Nat.cast_one]; ring

private theorem bin (f : ℝ → ℝ) (c : Continuous f) {a b : ℝ} (ab : a ≤ b) {l h : ℝ}
    (bounds : ∀ t ∈ Icc a b, l ≤ f t ∧ f t ≤ h) :
    (b-a)*l ≤ (∫ t in a..b, f t) ∧ (∫ t in a..b, f t) ≤ (b-a)*h := by
  have lo := intervalIntegral.integral_mono_on (μ := volume) ab (intervalIntegrable_const (c:=l))
    (c.intervalIntegrable _ _) (fun t ht => (bounds t ht).1)
  have hi := intervalIntegral.integral_mono_on (μ := volume) ab (c.intervalIntegrable _ _)
    (intervalIntegrable_const (c:=h)) (fun t ht => (bounds t ht).2)
  simpa using And.intro lo hi

private theorem src_cont (back : Bool) (r : ℝ) : Continuous (source back r) := by
  cases back <;> unfold source physical weight <;> simp only [Bool.false_eq_true,if_true,if_false] <;> fun_prop

theorem flux_at_edge (back : Bool) {r : ℝ} {rl rh : ℤ} (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q)
    (j : ℕ) (hj : j ≤ 1024) :
    (π/2048)*((runningSlope true back j rl rh:ℝ)/q) ≤ (∫ t in 0..angle 11 j, source back r t) ∧
    (∫ t in 0..angle 11 j, source back r t) ≤ (π/2048)*((runningSlope false back j rl rh:ℝ)/q) := by
  induction j with
  | zero => simp [runningSlope,angle]
  | succ j ih =>
    have prev := ih (by omega)
    have ab : angle 11 j ≤ angle 11 (j+1) := by linarith [width j,pi_pos]
    have inc := bin _ (src_cont back r) ab (fun t ht => slope_sound back (by omega : j<1024) ht hr hl hh h0 h1 h2)
    rw [width] at inc
    rw [← intervalIntegral.integral_add_adjacent_intervals ((src_cont back r).intervalIntegrable 0 (angle 11 j))
      ((src_cont back r).intervalIntegrable (angle 11 j) (angle 11 (j+1)))]
    have ps (lower : Bool) : runningSlope lower back (j+1) rl rh = runningSlope lower back j rl rh + increment lower back j rl rh :=
      Finset.sum_range_succ _ _
    rw [ps,ps]; push_cast
    simp only [add_div,mul_add]
    exact ⟨add_le_add prev.1 inc.1, add_le_add prev.2 inc.2⟩

private theorem partial_bin (f : ℝ → ℝ) (c : Continuous f) {a b t l h : ℝ} (ht : t ∈ Icc a b)
    (box : ∀ u ∈ Icc a b, l ≤ f u ∧ f u ≤ h) :
    (b-a)*min 0 l ≤ (∫ u in a..t, f u) ∧ (∫ u in a..t, f u) ≤ (b-a)*max 0 h := by
  have v := bin f c ht.1 (fun u hu => box u ⟨hu.1,hu.2.trans ht.2⟩)
  have w : 0 ≤ t-a := sub_nonneg.mpr ht.1
  have span : t-a ≤ b-a := by linarith [ht.2]
  constructor
  · calc (b-a)*min 0 l ≤ (t-a)*min 0 l := mul_le_mul_of_nonpos_right span (min_le_left _ _)
        _ ≤ (t-a)*l := mul_le_mul_of_nonneg_left (min_le_right _ _) w
        _ ≤ _ := v.1
  · calc _ ≤ (t-a)*h := v.2
         _ ≤ (t-a)*max 0 h := mul_le_mul_of_nonneg_left (le_max_right _ _) w
         _ ≤ (b-a)*max 0 h := mul_le_mul_of_nonneg_right span (le_max_left _ _)

def fluxCap (fl fh dl dh : ℤ) : ℤ := ceilDiv (max (-(fl+min 0 dl)) (fh+max 0 dh)) 2048

set_option maxRecDepth 4000 in
theorem partial_flux_cap (back : Bool) {j : ℕ} (hj : j < 1024) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 j) (angle 11 (j+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    let cap := fluxCap (runningSlope true back j rl rh) (runningSlope false back j rl rh)
      (increment true back j rl rh) (increment false back j rl rh)
    |polarFlux r (physical back t)| ≤ π*((cap:ℝ)/q) := by
  let fl := runningSlope true back j rl rh
  let fh := runningSlope false back j rl rh
  let dl := increment true back j rl rh
  let dh := increment false back j rl rh
  have start := flux_at_edge back hr hl hh h0 h1 h2 j hj.le
  have sub := partial_bin _ (src_cont back r) ht
    (fun u hu => slope_sound back hj hu hr hl hh h0 h1 h2)
  have div_min : min 0 ((dl:ℝ)/q) = (min 0 dl:ℤ)/(q:ℝ) := by
    push_cast; simpa only [zero_div] using min_div_div_right (by norm_num [q] : (0:ℝ) ≤ q) 0 (dl:ℝ)
  have div_max : max 0 ((dh:ℝ)/q) = (max 0 dh:ℤ)/(q:ℝ) := by
    push_cast; simpa only [zero_div] using max_div_div_right (by norm_num [q] : (0:ℝ) ≤ q) 0 (dh:ℝ)
  change _ * min 0 ((dl:ℝ)/q) ≤ _ ∧ _ ≤ _ * max 0 ((dh:ℝ)/q) at sub
  rw [width,div_min,div_max] at sub
  let f := source back r
  have sum := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) ((src_cont back r).intervalIntegrable 0 (angle 11 j))
    ((src_cont back r).intervalIntegrable (angle 11 j) t)
  have lower := add_le_add start.1 sub.1
  have upper := add_le_add start.2 sub.2
  rw [sum] at lower upper
  change π/2048*((fl:ℝ)/q)+_ ≤ _ at lower
  change _ ≤ π/2048*((fh:ℝ)/q)+_ at upper
  have ce := ceil_mul_bound (max (-(fl+min 0 dl)) (fh+max 0 dh)) (show (0:ℤ)<2048 by decide)
  change _ ≤ (fluxCap fl fh dl dh : ℝ)*2048 at ce
  push_cast at ce
  have a := (le_max_left _ _).trans ce
  have b := (le_max_right _ _).trans ce
  let sc := π/(2048*(q:ℝ))
  have pos : 0 ≤ sc := by dsimp [sc,q]; positivity
  have a' := mul_le_mul_of_nonneg_left a pos
  have b' := mul_le_mul_of_nonneg_left b pos
  change |polarFlux _ _| ≤ π*((fluxCap fl fh dl dh:ℝ)/q)
  rw [← inward, abs_le]
  push_cast at lower upper
  dsimp [sc] at a' b'; norm_num only [q, Int.cast_ofNat] at lower upper a' b' ⊢
  constructor <;> linarith

def cellCost (j : ℕ) (wh wl f : ℤ) := if j=0 then ceilDiv (16*wh) 4194304 else ceilDiv (f*f) wl

private theorem cap_density {F p : ℝ} {a wl : ℤ} (absF : |F| ≤ π*((a:ℝ)/q))
    (low : (wl:ℝ)/q ≤ p) (positive : 0 < wl) :
    F^2/p ≤ π^2*((ceilDiv (a*a) wl:ℝ)/q) := by
  have qp : (0:ℝ)<q := by norm_num [q]
  have w : 0 < (wl:ℝ) := by exact_mod_cast positive
  have pp := (div_pos w qp).trans_le low
  have up := ceil_mul_bound (a*a) positive
  push_cast at up
  have pos : (0:ℝ) ≤ ceilDiv (a*a) wl := by
    by_contra! h
    nlinarith [mul_neg_of_neg_of_pos h w, sq_nonneg (a:ℝ)]
  have hmul := mul_le_mul_of_nonneg_left low (div_nonneg pos qp.le)
  have sq := pow_le_pow_left₀ (abs_nonneg F) absF 2
  rw [sq_abs] at sq
  apply (div_le_iff₀ pp).2
  calc F^2 ≤ π^2*((a:ℝ)*a/(q:ℝ)^2) := by norm_num [q] at sq ⊢; linarith
       _ ≤ π^2*((ceilDiv (a*a) wl:ℝ)*wl/(q:ℝ)^2) :=
         mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right up (sq_nonneg _)) (sq_nonneg _)
       _ ≤ _ := by
         have z := mul_le_mul_of_nonneg_left hmul (sq_nonneg π)
         norm_num [q] at z ⊢; linarith

def energyCell (back : Bool) (j : ℕ) (rl rh : ℤ) :=
  let c := angleCell (index back j)
  let f := fluxCap (runningSlope true back j rl rh) (runningSlope false back j rl rh)
    (increment true back j rl rh) (increment false back j rl rh)
  cellCost j (weightHi c rl rh) (weightLo c rl rh) f

def integrand (r t : ℝ) := polarFlux r t ^ 2 / weight r t

theorem energy_cell_sound (back : Bool) {j : ℕ} (hj : j < 1024) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 j) (angle 11 (j+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q)
    (den : j ≠ 0 → 0 < weightLo (angleCell (index back j)) rl rh) :
    integrand r (physical back t) ≤ π^2*((energyCell back j rl rh:ℝ)/q) := by
  have ht' := grid_physical back hj ht
  by_cases zero : j=0
  · subst j
    have edge : index back 0 = 0 ∨ index back 0 = 2047 := by cases back <;> simp [index]
    exact end_cell_cost edge ht' hr hl hh h0 h1 h2
  · have hi : index back j < 2048 := by cases back <;> simp [index] <;> omega
    have w := (weight_sound hi ht' hr hl hh (exponent_range _ h0 h1 h2).1 (exponent_range _ h0 h1 h2).2).1
    have f := partial_flux_cap back hj ht hr hl hh h0 h1 h2
    simp only [energyCell,cellCost,if_neg zero]
    exact cap_density f w (den zero)

def gridCost (i : ℕ) (rl rh : ℤ) :=
  if i < 1024 then energyCell false i rl rh else energyCell true (2047-i) rl rh

private theorem grid_cost_sound {i : ℕ} (hi : i < 2048) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q)
    (den : ∀ i < 2048, i ≠ 0 → i ≠ 2047 → 0 < weightLo (angleCell i) rl rh) :
    integrand r t ≤ π^2*((gridCost i rl rh:ℝ)/q) := by
  by_cases first : i<1024
  · simpa [gridCost,first,physical] using energy_cell_sound false first ht hr hl hh h0 h1 h2
      (fun h => den i hi h (by omega))
  · let j := 2047-i
    have eq : index true j = i := by simp [index,j]; omega
    have rev : π-t ∈ Icc (angle 11 j) (angle 11 (j+1)) := by
      obtain ⟨a,b⟩ := ht; have h : i ≤ 2047 := by omega
      simp [angle,j,Nat.cast_sub h] at *; constructor <;> linarith
    have jj : j<1024 := by dsimp [j]; omega
    have nonzero (hn : j ≠ 0) : i ≠ 2047 := by dsimp [j] at hn; omega
    have d (hn : j ≠ 0) : 0 < weightLo (angleCell (index true j)) rl rh := by
      rw [eq]; exact den i hi (by omega) (nonzero hn)
    simpa [gridCost,first,physical,j] using energy_cell_sound true jj rev hr hl hh h0 h1 h2 d

private theorem energy_continuous {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (integrand r) (Icc 0 π) := by
  have w : Continuous (weight r) := by unfold weight; fun_prop
  have h := ((polarSpeed_continuousOn hr).pow 2).mul w.continuousOn
  apply h.congr
  intro t _
  dsimp [integrand]
  by_cases hz : weight r t = 0
  · simp [hz]
  · field_simp

def energyAverage (rl rh : ℤ) := ceilDiv (∑ i ∈ Finset.range 2048, gridCost i rl rh) 2048
def ratioCap (rl rh : ℤ) := ceilDiv (energyAverage rl rh * q) (averageLo weightLo rl rh)
def parallelCap (rl rh : ℤ) := ceilDiv (ratioCap rl rh * 986961) 100000

/-- The inward integer flux sums and both pole branches bound the normalized continuous
polar energy, with the same outward-rounded π² factor used by the Omega evaluator. -/
theorem normalized_parallel {r : ℝ} {rl rh : ℤ} (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    parallelEnergy r ≤ (parallelCap rl rh:ℝ)/q := by
  have den := fun i hi left right => @interior_weight_pos i hi left right rl rh h0 h1 h2
  let f := fun t => integrand r t / π^2
  let N := ∫ t in 0..π, f t
  let Z := ∫ t in 0..π, weight r t
  let H := energyAverage rl rh
  let L := averageLo weightLo rl rh
  let R := ratioCap rl rh
  have cont : ContinuousOn f (Icc 0 π) := (energy_continuous hr).div_const _
  have order (i : ℕ) (_ : i < 2048) : angle 11 i ≤ angle 11 (i+1) := by linarith [width i,pi_pos]
  have ends : angle 11 0 = 0 ∧ angle 11 2048 = π := by norm_num [angle]
  have sub (i : ℕ) (hi : i < 2048) : Icc (angle 11 i) (angle 11 (i+1)) ⊆ Icc 0 π := by
    apply Icc_subset_Icc
    · unfold angle; positivity
    · have b : (i:ℝ)+1 ≤ 2048 := by exact_mod_cast (show i+1 ≤ 2048 by omega)
      simp [angle]; nlinarith [mul_le_mul_of_nonneg_right b pi_pos.le]
  have hg (i : ℕ) (hi : i < 2048) := (cont.mono (sub i hi)).intervalIntegrable_of_Icc (μ := volume) (order i hi)
  have point (t : ℝ) : 0 ≤ f t := by dsimp [f,integrand,weight]; positivity
  have bd (i : ℕ) (hi : i < 2048) (t : ℝ) (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) :
      0 ≤ f t ∧ f t ≤ (gridCost i rl rh:ℝ)/q := by
    refine ⟨point t,(div_le_iff₀ (sq_pos_of_pos pi_pos)).2 ?_⟩
    simpa only [mul_comm (π^2)] using grid_cost_sound hi ht hr hl hh h0 h1 h2 den
  have upper := (integral_enclosure order hg bd).2
  simp only [width,ends.1,ends.2] at upper
  have c := ceil_mul_bound (∑ i ∈ Finset.range 2048, gridCost i rl rh) (show (0:ℤ)<2048 by decide)
  change _ ≤ (H:ℝ)*2048 at c
  push_cast at c
  have rel : N ≤ (π/(q:ℝ))*H := by
    have k : 0 ≤ π/(2048*(q:ℝ)) := by dsimp [q]; positivity
    have eq : (∑ i ∈ Finset.range 2048, π/2048*((gridCost i rl rh:ℝ)/q)) =
      π/(2048*q)*∑ i ∈ Finset.range 2048,(gridCost i rl rh:ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [eq] at upper
    have rescale (x : ℝ) : π/(2048*q)*(x*2048) = (π/(q:ℝ))*x := by norm_num [q]; ring
    rw [← rescale]; exact upper.trans (mul_le_mul_of_nonneg_left c k)
  have z := (average_bounds (partition_and_moment hr hl hh h0 h1 h2).1).1
  change (π/(q:ℝ))*L ≤ Z at z
  have lp := normalizer_lower_pos h0 h1 h2
  have lp' : 0 < (L:ℝ) := by exact_mod_cast lp
  have qp : (0:ℝ)<q := by norm_num [q]
  have cp := div_pos pi_pos qp
  have zp := (mul_pos cp lp').trans_le z
  have np : 0 ≤ N := intervalIntegral.integral_nonneg pi_pos.le (fun t _ => point t)
  have hp := nonneg_of_mul_nonneg_right (np.trans rel) cp
  have frac : N/Z ≤ (H:ℝ)/L := by
    apply (div_le_div_iff₀ zp lp').2
    calc N*(L:ℝ) ≤ (π/(q:ℝ)*H)*L := mul_le_mul_of_nonneg_right rel lp'.le
         _ = H*(π/(q:ℝ)*L) := by ring
         _ ≤ H*Z := mul_le_mul_of_nonneg_left z hp
  have u := ceil_mul_bound (H*q) lp
  change _ ≤ (R:ℝ)*L at u; push_cast at u
  have ur : (H:ℝ)/L ≤ (R:ℝ)/q := (div_le_div_iff₀ lp' qp).2 u
  have rp := (div_nonneg hp lp'.le).trans ur
  have pi2 : π^2 ≤ 986961/100000 := by
    have d := pow_le_pow_left₀ pi_pos.le pi_lt_d6.le 2
    norm_num at d ⊢; linarith
  have e := ceil_mul_bound (R*986961) (show (0:ℤ)<100000 by decide)
  change _ ≤ (parallelCap rl rh:ℝ)*100000 at e; push_cast at e
  have scaled : parallelEnergy r = π^2 * (N/Z) := by
    dsimp [N,Z,f,parallelEnergy,integrand]
    rw [intervalIntegral.integral_div]
    field_simp [pi_ne_zero]
  rw [scaled]
  calc π^2*(N/Z) ≤ π^2*((R:ℝ)/q) := mul_le_mul_of_nonneg_left (frac.trans ur) (sq_nonneg _)
       _ ≤ (986961/100000)*((R:ℝ)/q) := mul_le_mul_of_nonneg_right pi2 rp
       _ ≤ _ := by norm_num [q] at e ⊢; linarith

#print axioms normalized_parallel
#print axioms partial_flux_cap
#print axioms flux_at_edge
#print axioms centered_mean_sound
#print axioms end_cell_cost
#print axioms two_pole_cells
end
end YangMills.DyadicPolarFlux
