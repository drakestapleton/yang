import DyadicTrig
import DyadicExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory Set YangMills.DyadicTrig YangMills.DyadicExp

namespace YangMills.DyadicPartition

structure Cell where
  cosLo : Int
  cosHi : Int
  sinLo : Int
  sinHi : Int
  deriving Inhabited

def angleCell (i : ℕ) : Cell :=
  let sq := sinSqBounds i
  ⟨(cosBounds 11 (i+1)).1 / 4, ceilDiv (cosBounds 11 i).2 4,
   sq.1 / 4194304, ceilDiv sq.2 4194304⟩

def loMul (x lo hi : Int) := min (x*lo) (x*hi) / q
def hiMul (x lo hi : Int) := ceilDiv (max (x*lo) (x*hi)) q

def weightLo (c : Cell) (rl rh : ℤ) := c.sinLo * expLo (loMul c.cosLo rl rh) / q
def weightHi (c : Cell) (rl rh : ℤ) := ceilDiv (c.sinHi * expHi (hiMul c.cosHi rl rh)) q

theorem floor_mul_bound (x : ℤ) {d : ℤ} (hd : 0 < d) :
    ((x / d : ℤ) : ℝ) * d ≤ x := by exact_mod_cast Int.ediv_mul_le x hd.ne'

theorem ceil_mul_bound (x : ℤ) {d : ℤ} (hd : 0 < d) :
    (x:ℝ) ≤ (ceilDiv x d : ℝ) * d := by
  have h := floor_mul_bound (-x) hd
  simp [ceilDiv] at *
  linarith

theorem grid_enclosure {i : ℕ} (hi : i < 2048) {t : ℝ}
    (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) :
    (angleCell i).cosLo / (q:ℝ) ≤ Real.cos t ∧ Real.cos t ≤ (angleCell i).cosHi / (q:ℝ) ∧
    (angleCell i).sinLo / (q:ℝ) ≤ Real.sin t ^ 2 ∧ Real.sin t ^ 2 ≤ (angleCell i).sinHi / (q:ℝ) := by
  obtain ⟨a,b,c,d⟩ := grid_cell_sound hi ht
  have e := floor_mul_bound (cosBounds 11 (i+1)).1 (show (0:ℤ)<4 by decide)
  have f := ceil_mul_bound (cosBounds 11 i).2 (show (0:ℤ)<4 by decide)
  have g := floor_mul_bound (sinSqBounds i).1 (show (0:ℤ)<4194304 by decide)
  have h := ceil_mul_bound (sinSqBounds i).2 (show (0:ℤ)<4194304 by decide)
  dsimp [angleCell, q, scale] at *
  norm_num only [Int.cast_ofNat] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

noncomputable def polarWeight (r t : ℝ) := Real.sin t ^ 2 * Real.exp (r * Real.cos t)

theorem mul_bounds (x rl rh : ℤ) {r : ℝ}
    (hl : (rl : ℝ)/q ≤ r) (hh : r ≤ (rh : ℝ)/q) :
    (loMul x rl rh : ℝ)/q ≤ (x:ℝ)/q * r ∧
    (x:ℝ)/q * r ≤ (hiMul x rl rh : ℝ)/q := by
  have a := floor_mul_bound (min (x*rl) (x*rh)) (show 0 < q by decide)
  have b := ceil_mul_bound (max (x*rl) (x*rh)) (show 0 < q by decide)
  change (loMul x rl rh : ℝ)*q ≤ _ at a
  change _ ≤ (hiMul x rl rh : ℝ)*q at b
  push_cast at a b
  have hq : (0:ℝ) < q := by norm_num [q]
  rcases le_total 0 (x:ℝ) with hx | hx
  · have l := mul_le_mul_of_nonneg_left hl hx
    have h := mul_le_mul_of_nonneg_left hh hx
    have a' := a.trans (min_le_left _ _)
    have b' := (le_max_right _ _).trans b
    norm_num [q] at l h a' b' ⊢; constructor <;> linarith
  · have l := mul_le_mul_of_nonpos_left hl hx
    have h := mul_le_mul_of_nonpos_left hh hx
    have a' := a.trans (min_le_right _ _)
    have b' := (le_max_left _ _).trans b
    norm_num [q] at l h a' b' ⊢; constructor <;> linarith

/-- The actual integer weight bounds enclose the continuous density throughout one angular cell. -/
theorem weight_sound {i : ℕ} (hi : i < 2048) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q)
    (el : -(2*q) ≤ loMul (angleCell i).cosLo rl rh)
    (eh : hiMul (angleCell i).cosHi rl rh ≤ 2*q) :
    (weightLo (angleCell i) rl rh : ℝ) / q ≤ polarWeight r t ∧
    polarWeight r t ≤ (weightHi (angleCell i) rl rh : ℝ) / q := by
  let c := angleCell i
  obtain ⟨cl,ch,sl,sh⟩ := grid_enclosure hi ht
  have xl := (mul_bounds c.cosLo rl rh hl hh).1.trans (mul_le_mul_of_nonneg_right cl hr)
  have xh := (mul_le_mul_of_nonneg_right ch hr).trans (mul_bounds c.cosHi rl rh hl hh).2
  have al := (expLo_sound el).trans (Real.exp_le_exp.mpr xl)
  have ah := (Real.exp_le_exp.mpr xh).trans (expHi_sound eh)
  have ep : (0:ℝ) ≤ (expLo (loMul c.cosLo rl rh) : ℝ) / q :=
    div_nonneg (by exact_mod_cast (expLo_pos el).le) (by norm_num [q])
  have sl' := mul_le_mul sl al ep (sq_nonneg (Real.sin t))
  have sh' := mul_le_mul sh ah (Real.exp_pos _).le ((sq_nonneg (Real.sin t)).trans sh)
  have dl := floor_mul_bound (c.sinLo * expLo (loMul c.cosLo rl rh)) (show 0 < q by decide)
  have uh := ceil_mul_bound (c.sinHi * expHi (hiMul c.cosHi rl rh)) (show 0 < q by decide)
  change (weightLo c rl rh : ℝ)*q ≤ _ at dl
  change _ ≤ (weightHi c rl rh : ℝ)*q at uh
  push_cast at dl uh
  change (c.sinLo:ℝ)/q * _ ≤ _ at sl'
  change _ ≤ (c.sinHi:ℝ)/q * _ at sh'
  change (weightLo c rl rh : ℝ)/q ≤ polarWeight r t ∧ polarWeight r t ≤ (weightHi c rl rh : ℝ)/q
  unfold polarWeight
  rw [mul_comm r]
  norm_num [q] at dl uh sl' sh' ⊢
  constructor <;> linarith

/-- Integer upper cost used by the transverse trial field in the replay. -/
def transverseCap (c : Cell) (rl rh : ℤ) : ℤ :=
  let xl := loMul c.cosLo rl rh
  let xh := hiMul c.cosHi rl rh
  let d := max (-((2*q-hiMul xh c.sinLo c.sinHi)/6)) (ceilDiv (2*q-loMul xl c.sinLo c.sinHi) 6)
  let a := max (-c.cosLo) c.cosHi
  ceilDiv (ceilDiv (a*a) q) 27 + ceilDiv (2*ceilDiv (d*d) q) 3

noncomputable def transverseTrial (r t : ℝ) :=
  Real.cos t ^ 2/27 + (2/3:ℝ)*(1/3-r*Real.cos t*(Real.sin t)^2/6)^2

private theorem weighted_trial_nonneg (r t : ℝ) : 0 ≤ polarWeight r t * transverseTrial r t := by
  unfold polarWeight transverseTrial
  positivity

private theorem rounded_square (z : ℤ) (x : ℝ) (h : |x| ≤ z/(q:ℝ)) :
    x^2 ≤ (ceilDiv (z*z) q:ℝ)/q := by
  have nonneg := (abs_nonneg x).trans h
  have sq := pow_le_pow_left₀ (abs_nonneg x) h 2
  rw [sq_abs] at sq
  have u := ceil_mul_bound (z*z) (show 0 < q by decide)
  push_cast at u; norm_num [q] at u sq ⊢; linarith

theorem transverse_cost_sound {i : ℕ} (hi : i < 2048) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) :
    transverseTrial r t ≤ (transverseCap (angleCell i) rl rh : ℝ)/q := by
  let c := angleCell i
  obtain ⟨cl,ch,sl,sh⟩ := grid_enclosure hi ht
  let xl := loMul c.cosLo rl rh
  let xh := hiMul c.cosHi rl rh
  have b1 := (mul_bounds c.cosLo rl rh hl hh).1.trans (mul_le_mul_of_nonneg_right cl hr)
  have b2 := (mul_le_mul_of_nonneg_right ch hr).trans (mul_bounds c.cosHi rl rh hl hh).2
  have p1 := (mul_bounds xl c.sinLo c.sinHi sl sh).1.trans (mul_le_mul_of_nonneg_right b1 (sq_nonneg (Real.sin t)))
  have p2 := (mul_le_mul_of_nonneg_right b2 (sq_nonneg (Real.sin t))).trans (mul_bounds xh c.sinLo c.sinHi sl sh).2
  let a := max (-c.cosLo) c.cosHi
  have ah : |Real.cos t| ≤ a/(q:ℝ) := by
    dsimp [a]; push_cast; rw [abs_le]; constructor
    · have h := le_max_left (-(c.cosLo:ℝ)) c.cosHi
      change (c.cosLo:ℝ)/q ≤ _ at cl
      norm_num [q] at cl ⊢; linarith
    · have h := le_max_right (-(c.cosLo:ℝ)) c.cosHi
      change _ ≤ (c.cosHi:ℝ)/q at ch
      norm_num [q] at ch ⊢; linarith
  let v := (1/3:ℝ)-r*Real.cos t*Real.sin t^2/6
  let dl := (2*q-hiMul xh c.sinLo c.sinHi)/6
  let dh := ceilDiv (2*q-loMul xl c.sinLo c.sinHi) 6
  let d := max (-dl) dh
  have low := floor_mul_bound (2*q-hiMul xh c.sinLo c.sinHi) (show (0:ℤ)<6 by decide)
  have high := ceil_mul_bound (2*q-loMul xl c.sinLo c.sinHi) (show (0:ℤ)<6 by decide)
  change (dl:ℝ)*6 ≤ _ at low
  change _ ≤ (dh:ℝ)*6 at high
  push_cast at low high
  have dv : |v| ≤ d/(q:ℝ) := by
    have m1 := le_max_left (-dl) dh
    have m2 := le_max_right (-dl) dh
    change -dl ≤ d at m1
    change dh ≤ d at m2
    have m1' : -(dl:ℝ) ≤ d := by exact_mod_cast m1
    have m2' : (dh:ℝ) ≤ d := by exact_mod_cast m2
    rw [abs_le]; dsimp [v]; norm_num [q] at low high p1 p2 ⊢
    constructor <;> linarith
  have s1 := rounded_square a _ ah
  have s2 := rounded_square d _ dv
  have t1 := ceil_mul_bound (ceilDiv (a*a) q) (show (0:ℤ)<27 by decide)
  have t2 := ceil_mul_bound (2*ceilDiv (d*d) q) (show (0:ℤ)<3 by decide)
  push_cast at t1 t2
  change Real.cos t^2/27 + (2/3:ℝ)*v^2 ≤
    ((ceilDiv (ceilDiv (a*a) q) 27 + ceilDiv (2*ceilDiv (d*d) q) 3 : ℤ) : ℝ)/q
  push_cast
  norm_num only [q, Int.cast_ofNat] at s1 s2 t1 t2 ⊢
  linarith

/-- A signed integrand enclosed on every cell can be integrated using the endpoint sums. -/
theorem integral_enclosure {n : ℕ} {edges lo hi : ℕ → ℝ} {f : ℝ → ℝ}
    (order : ∀ i < n, edges i ≤ edges (i+1))
    (integrable : ∀ i < n, IntervalIntegrable f volume (edges i) (edges (i+1)))
    (boxes : ∀ i < n, ∀ t ∈ Icc (edges i) (edges (i+1)), lo i ≤ f t ∧ f t ≤ hi i) :
    (∑ i ∈ Finset.range n, (edges (i+1)-edges i)*lo i) ≤ ∫ t in edges 0..edges n, f t ∧
    (∫ t in edges 0..edges n, f t) ≤ ∑ i ∈ Finset.range n, (edges (i+1)-edges i)*hi i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals integrable]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    have h := intervalIntegral.integral_mono_on (order i (Finset.mem_range.mp hi))
      (intervalIntegrable_const (c := lo i)) (integrable i (Finset.mem_range.mp hi))
      (fun t ht => (boxes i (Finset.mem_range.mp hi) t ht).1)
    simpa using h
  · apply Finset.sum_le_sum
    intro i hi
    have h := intervalIntegral.integral_mono_on (order i (Finset.mem_range.mp hi))
      (integrable i (Finset.mem_range.mp hi)) (intervalIntegrable_const (c := _))
      (fun t ht => (boxes i (Finset.mem_range.mp hi) t ht).2)
    simpa using h

/-- Increments of two increasing functions need opposite endpoints when subtracted. -/
theorem signed_cell {f g : ℝ → ℝ} {a b t : ℝ}
    (hf : MonotoneOn f (Icc a b)) (hg : MonotoneOn g (Icc a b)) (ht : t ∈ Icc a b) :
    f a - g b ≤ f t - g t ∧ f t - g t ≤ f b - g a := by
  have hab := ht.1.trans ht.2
  have ha := left_mem_Icc.mpr hab
  have hb := right_mem_Icc.mpr hab
  exact ⟨sub_le_sub (hf ha ht ht.1) (hg ht hb ht.2), sub_le_sub (hf ht hb ht.2) (hg ha ht ht.1)⟩

def momentLo (c : Cell) (rl rh : ℤ) := loMul c.cosLo (weightLo c rl rh) (weightHi c rl rh)
def momentHi (c : Cell) (rl rh : ℤ) := hiMul c.cosHi (weightLo c rl rh) (weightHi c rl rh)

theorem moment_sound {i : ℕ} (hi : i < 2048) {r t : ℝ} {rl rh : ℤ}
    (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q)
    (el : -(2*q) ≤ loMul (angleCell i).cosLo rl rh)
    (eh : hiMul (angleCell i).cosHi rl rh ≤ 2*q) :
    (momentLo (angleCell i) rl rh:ℝ)/q ≤ Real.cos t * polarWeight r t ∧
    Real.cos t * polarWeight r t ≤ (momentHi (angleCell i) rl rh:ℝ)/q := by
  obtain ⟨wl,wh⟩ := weight_sound hi ht hr hl hh el eh
  obtain ⟨cl,ch,_,_⟩ := grid_enclosure hi ht
  have hw : 0 ≤ polarWeight r t := by unfold polarWeight; positivity
  exact ⟨(mul_bounds _ _ _ wl wh).1.trans (mul_le_mul_of_nonneg_right cl hw),
    (mul_le_mul_of_nonneg_right ch hw).trans (mul_bounds _ _ _ wl wh).2⟩

private theorem cos_range (n i : ℕ) :
    -scale ≤ (cosBounds n i).1 ∧ (cosBounds n i).2 ≤ scale := by
  cases n with
  | zero => simp only [cosBounds]; split <;> norm_num [scale]
  | succ n =>
    simp only [cosBounds]
    split <;> try norm_num [scale]
    split <;> try norm_num [scale]
    split <;> try norm_num [scale]
    split <;> simp [half, reflect, scale]

private theorem angle_range (i : ℕ) : -q ≤ (angleCell i).cosLo ∧ (angleCell i).cosHi ≤ q := by
  have a := (cos_range 11 (i+1)).1
  have b := (cos_range 11 i).2
  dsimp [angleCell, ceilDiv, scale, q] at *
  omega

theorem exponent_range (i : ℕ) {rl rh : ℤ} (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    -(2*q) ≤ loMul (angleCell i).cosLo rl rh ∧ hiMul (angleCell i).cosHi rl rh ≤ 2*q := by
  obtain ⟨hl,hh⟩ := angle_range i
  have aux (y : ℤ) (hy : 0 ≤ y) (h : y ≤ 2*q) :
      -(2*q)*q ≤ (angleCell i).cosLo*y ∧ (angleCell i).cosHi*y ≤ (2*q)*q := by
    have a := mul_le_mul_of_nonneg_right hl hy
    have b := mul_le_mul_of_nonneg_right hh hy
    dsimp [q] at *; constructor <;> linarith
  have a := aux rl h0 (h1.trans h2)
  have b := aux rh (h0.trans h1) h2
  constructor
  · exact (Int.le_ediv_iff_mul_le (show 0 < q by decide)).2 (le_min a.1 b.1)
  · have hm := max_le a.2 b.2
    unfold hiMul ceilDiv
    apply neg_le_of_neg_le
    apply (Int.le_ediv_iff_mul_le (show 0 < q by decide)).2
    linarith

/-- The density and its signed cosine moment are the two integral inputs to the polar flux. -/
theorem partition_and_moment {r : ℝ} {rl rh : ℤ} (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q)
    (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    let bounded := fun (f : ℝ → ℝ) (l h : Cell → ℤ → ℤ → ℤ) =>
      (∑ i ∈ Finset.range 2048, (Real.pi/2048) * (l (angleCell i) rl rh / (q:ℝ))) ≤ (∫ t in 0..Real.pi, f t) ∧
      (∫ t in 0..Real.pi, f t) ≤ ∑ i ∈ Finset.range 2048, (Real.pi/2048) * (h (angleCell i) rl rh / (q:ℝ))
    bounded (polarWeight r) weightLo weightHi ∧
    bounded (fun t => Real.cos t * polarWeight r t) momentLo momentHi := by
  have step (i : ℕ) : angle 11 (i+1) - angle 11 i = Real.pi/2048 := by
    simp only [angle, Nat.cast_add, Nat.cast_one]; ring
  have order (i : ℕ) (_ : i < 2048) : angle 11 i ≤ angle 11 (i+1) := by
    linarith [step i, Real.pi_pos]
  have ends : angle 11 0 = 0 ∧ angle 11 2048 = Real.pi := by norm_num [angle]
  have con : Continuous (polarWeight r) := by unfold polarWeight; fun_prop
  have first := integral_enclosure order (fun i _ => con.intervalIntegrable _ _)
    (fun i hi t ht => weight_sound hi ht hr hl hh (exponent_range i h0 h1 h2).1 (exponent_range i h0 h1 h2).2)
  have second := integral_enclosure order (fun i _ => (Real.continuous_cos.mul con).intervalIntegrable _ _)
    (fun i hi t ht => moment_sound hi ht hr hl hh (exponent_range i h0 h1 h2).1 (exponent_range i h0 h1 h2).2)
  simpa only [step, ends.1, ends.2, Pi.mul_apply] using And.intro first second

def weightedCap (c : Cell) (rl rh : ℤ) :=
  ceilDiv (transverseCap c rl rh * weightHi c rl rh) q

def averageLo (l : Cell → ℤ → ℤ → ℤ) (rl rh : ℤ) : ℤ :=
  (∑ i ∈ Finset.range 2048, l (angleCell i) rl rh) / 2048

def averageHi (h : Cell → ℤ → ℤ → ℤ) (rl rh : ℤ) : ℤ :=
  ceilDiv (∑ i ∈ Finset.range 2048, h (angleCell i) rl rh) 2048

theorem average_bounds {f : ℝ → ℝ} {l h : Cell → ℤ → ℤ → ℤ} {rl rh : ℤ}
    (bounds : (∑ i ∈ Finset.range 2048, (Real.pi/2048)*(l (angleCell i) rl rh/(q:ℝ))) ≤ (∫ t in 0..Real.pi, f t) ∧
      (∫ t in 0..Real.pi, f t) ≤ ∑ i ∈ Finset.range 2048, (Real.pi/2048)*(h (angleCell i) rl rh/(q:ℝ))) :
    (Real.pi/(q:ℝ)) * averageLo l rl rh ≤ (∫ t in 0..Real.pi, f t) ∧
    (∫ t in 0..Real.pi, f t) ≤ (Real.pi/(q:ℝ)) * averageHi h rl rh := by
  have dl := floor_mul_bound (∑ i ∈ Finset.range 2048, l (angleCell i) rl rh) (show (0:ℤ)<2048 by decide)
  have uh := ceil_mul_bound (∑ i ∈ Finset.range 2048, h (angleCell i) rl rh) (show (0:ℤ)<2048 by decide)
  change (averageLo l rl rh : ℝ)*2048 ≤ _ at dl
  change _ ≤ (averageHi h rl rh : ℝ)*2048 at uh
  push_cast at dl uh
  have sum_scale (a : ℕ → ℤ) :
      (∑ i ∈ Finset.range 2048, (Real.pi/2048)*((a i:ℝ)/q)) =
      (Real.pi/(2048*q)) * ∑ i ∈ Finset.range 2048, (a i:ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have factor : 0 ≤ Real.pi/(2048*q) := by norm_num [q]; positivity
  have rescale (x : ℝ) : (Real.pi/(2048*q))*(x*2048) = (Real.pi/(q:ℝ))*x := by norm_num [q]; ring
  rw [sum_scale, sum_scale] at bounds
  constructor
  · rw [← rescale]; exact (mul_le_mul_of_nonneg_left dl factor).trans bounds.1
  · rw [← rescale]; exact bounds.2.trans (mul_le_mul_of_nonneg_left uh factor)

private theorem sine_lower_nonneg (i : ℕ) : 0 ≤ (angleCell i).sinLo := by
  unfold angleCell sinSqBounds
  dsimp
  exact Int.ediv_nonneg (Int.ediv_nonneg (sq_nonneg _) (by decide)) (by decide)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 2000000 in
private theorem interior_sines :
    (List.range 2046).all (fun j => decide (8 ≤ (angleCell (j+1)).sinLo)) = true := by
  decide +kernel

/-- Positive integer lower density on every non-pole cell across the full field range. -/
theorem interior_weight_pos {i : ℕ} (hi : i < 2048) (left : i ≠ 0) (right : i ≠ 2047)
    {rl rh : ℤ} (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    0 < weightLo (angleCell i) rl rh := by
  have hj : i-1 ∈ List.range 2046 := List.mem_range.mpr (by omega)
  have sine := of_decide_eq_true (List.all_eq_true.mp interior_sines (i-1) hj)
  rw [show i-1+1=i by omega] at sine
  have exponential := expLo_floor (exponent_range i h0 h1 h2).1
  have prod := mul_le_mul sine exponential (show 0 ≤ q/8 by decide) (by omega)
  have base : (8:ℤ)*(q/8) = q := by decide
  rw [base] at prod
  unfold weightLo
  norm_num [q] at prod ⊢
  omega

set_option maxRecDepth 12000 in
/-- The middle cell alone makes the integer lower normalizer positive. -/
theorem normalizer_lower_pos {rl rh : ℤ} (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    0 < averageLo weightLo rl rh := by
  have nonneg (i : ℕ) : 0 ≤ weightLo (angleCell i) rl rh :=
    Int.ediv_nonneg (mul_nonneg (sine_lower_nonneg i) (expLo_pos (exponent_range i h0 h1 h2).1).le) (by decide)
  have central : (angleCell 1023).cosLo = 0 := by decide
  have fixed (n : ℕ) : squareDown n q = q := by
    induction n with
    | zero => rfl
    | succ n ih => rw [squareDown, ih]; decide
  have zero : expLo 0 = q := by simpa [expLo] using fixed 12
  have enough : 2048 ≤ (angleCell 1023).sinLo * expLo 0 / q := by
    rw [zero]; norm_num [q]
    decide +kernel
  have wl : 2048 ≤ weightLo (angleCell 1023) rl rh := by
    simpa [weightLo, loMul, central] using enough
  have sum := Finset.single_le_sum (f := fun i => weightLo (angleCell i) rl rh)
    (fun i _ => nonneg i) (Finset.mem_range.mpr (show 1023 < 2048 by decide))
  have lower := wl.trans sum
  unfold averageLo
  omega

/-- The exact integer used for the normalized transverse replay row bounds the
continuous normalized trial energy. The middle angular cell supplies a positive denominator. -/
theorem normalized_transverse {r : ℝ} {rl rh : ℤ} (hr : 0 ≤ r)
    (hl : (rl:ℝ)/q ≤ r) (hh : r ≤ (rh:ℝ)/q) (h0 : 0 ≤ rl) (h1 : rl ≤ rh) (h2 : rh ≤ 2*q) :
    (∫ t in 0..Real.pi, polarWeight r t * transverseTrial r t) /
      (∫ t in 0..Real.pi, polarWeight r t) ≤
    (ceilDiv (averageHi weightedCap rl rh * q) (averageLo weightLo rl rh) : ℝ)/q := by
  have hz := normalizer_lower_pos h0 h1 h2
  have step (i : ℕ) : angle 11 (i+1) - angle 11 i = Real.pi/2048 := by
    simp only [angle, Nat.cast_add, Nat.cast_one]; ring
  have order (i : ℕ) (_ : i < 2048) : angle 11 i ≤ angle 11 (i+1) := by
    linarith [step i, Real.pi_pos]
  have con : Continuous (fun t => polarWeight r t * transverseTrial r t) := by
    unfold polarWeight transverseTrial; fun_prop
  have boxes (i : ℕ) (hi : i < 2048) (t : ℝ) (ht : t ∈ Icc (angle 11 i) (angle 11 (i+1))) :
      0 ≤ polarWeight r t * transverseTrial r t ∧
      polarWeight r t * transverseTrial r t ≤ (weightedCap (angleCell i) rl rh:ℝ)/q := by
    have w := (weight_sound hi ht hr hl hh (exponent_range i h0 h1 h2).1 (exponent_range i h0 h1 h2).2).2
    have v := transverse_cost_sound hi ht hr hl hh
    have v0 : 0 ≤ transverseTrial r t := by unfold transverseTrial; positivity
    have w0 : 0 ≤ polarWeight r t := by unfold polarWeight; positivity
    have m := mul_le_mul v w w0 (v0.trans v)
    have u := ceil_mul_bound (transverseCap (angleCell i) rl rh * weightHi (angleCell i) rl rh) (show 0 < q by decide)
    change _ ≤ (weightedCap (angleCell i) rl rh:ℝ)*q at u
    push_cast at u
    refine ⟨mul_nonneg w0 v0, ?_⟩
    rw [mul_comm]
    norm_num [q] at u m ⊢; linarith
  have ends : angle 11 0 = 0 ∧ angle 11 2048 = Real.pi := by norm_num [angle]
  have cap := (integral_enclosure order (fun i _ => con.intervalIntegrable _ _) boxes).2
  simp only [step, ends.1, ends.2] at cap
  have lower := (partition_and_moment hr hl hh h0 h1 h2).1.1
  let N := ∫ t in 0..Real.pi, polarWeight r t * transverseTrial r t
  let Z := ∫ t in 0..Real.pi, polarWeight r t
  let L := averageLo weightLo rl rh
  let H := averageHi weightedCap rl rh
  have l := floor_mul_bound (∑ i ∈ Finset.range 2048, weightLo (angleCell i) rl rh) (show (0:ℤ)<2048 by decide)
  have u := ceil_mul_bound (∑ i ∈ Finset.range 2048, weightedCap (angleCell i) rl rh) (show (0:ℤ)<2048 by decide)
  change (L:ℝ)*2048 ≤ _ at l
  change _ ≤ (H:ℝ)*2048 at u
  push_cast at l u
  have scale_sum (f : ℕ → ℤ) :
      (∑ i ∈ Finset.range 2048, (Real.pi/2048)*((f i:ℝ)/q)) =
      (Real.pi/(2048*q)) * ∑ i ∈ Finset.range 2048, (f i:ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [scale_sum] at cap lower
  have factor : 0 ≤ Real.pi/(2048*q) := by norm_num [q]; positivity
  have l' := (mul_le_mul_of_nonneg_left l factor).trans lower
  have u' := cap.trans (mul_le_mul_of_nonneg_left u factor)
  have p : 0 < Real.pi/(q:ℝ) := by norm_num [q]; positivity
  have Lpos : (0:ℝ) < L := by exact_mod_cast hz
  have rescale (x : ℝ) : (Real.pi/(2048*q))*(x*2048) = (Real.pi/(q:ℝ))*x := by norm_num [q]; ring
  have zl : (Real.pi/(q:ℝ))*L ≤ Z := by rw [← rescale]; exact l'
  have nu : N ≤ (Real.pi/(q:ℝ))*H := by rw [← rescale]; exact u'
  have npos : 0 ≤ N := intervalIntegral.integral_nonneg Real.pi_pos.le (fun t _ => weighted_trial_nonneg r t)
  have nh : 0 ≤ (H:ℝ) := nonneg_of_mul_nonneg_right (npos.trans nu) p
  have rat : N/Z ≤ (H:ℝ)/L := by
    apply (div_le_div_iff₀ ((mul_pos p Lpos).trans_le zl) Lpos).2
    calc N*(L:ℝ) ≤ ((Real.pi/(q:ℝ))*H)*L := mul_le_mul_of_nonneg_right nu Lpos.le
         _ = H*((Real.pi/(q:ℝ))*L) := by ring
         _ ≤ H*Z := mul_le_mul_of_nonneg_left zl nh
  have final := ceil_mul_bound (H*q) hz
  push_cast at final
  apply rat.trans
  apply (div_le_div_iff₀ Lpos (show (0:ℝ)<q by norm_num [q])).2
  exact final

#print axioms normalized_transverse
#print axioms weight_sound
#print axioms signed_cell
#print axioms partition_and_moment

end YangMills.DyadicPartition
