import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace YangMills.DyadicExp

def q : ℤ := 268435456

/-- Downward-rounded positive squaring on the OM-2 dyadic grid. -/
def squareDown : ℕ → ℤ → ℤ
  | 0, v => v
  | n+1, v => let w := squareDown n v; w*w/q

def expLo (x : ℤ) := squareDown 12 (q + x/4096)
def ceilDiv (n d : ℤ) := -((-n)/d)
def expHi (x : ℤ) := ceilDiv (q*q) (expLo (-x))

private theorem floor_spec (a b : ℤ) (hb : 0 < b) :
    ((a/b : ℤ) : ℝ) ≤ (a : ℝ)/(b:ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

private theorem ceil_spec (a b : ℤ) (hb : 0 < b) :
    (a : ℝ)/(b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  unfold ceilDiv
  push_cast
  have := floor_spec (-a) b hb
  push_cast at this
  rw [neg_div] at this
  linarith

private theorem squares_le {v : ℤ} {b : ℝ} (hv : 0 ≤ v) (hb : (v:ℝ) / q ≤ b)
    (n : ℕ) : 0 ≤ squareDown n v ∧ (squareDown n v : ℝ)/q ≤ b^(2^n) := by
  induction n with
  | zero => simpa [squareDown] using And.intro hv hb
  | succ n ih =>
    let w := squareDown n v
    have hw : 0 ≤ w := ih.1
    refine ⟨Int.ediv_nonneg (mul_nonneg hw hw) (by decide), ?_⟩
    have hh := floor_spec (w*w) q (by decide)
    push_cast at hh
    have hpow := pow_le_pow_left₀ (show 0 ≤ (w:ℝ)/q by unfold q; positivity) ih.2 2
    rw [pow_succ 2, pow_mul]
    change ((w*w/q : ℤ):ℝ)/q ≤ _
    calc _ ≤ ((w:ℝ)/q)^2 := by dsimp [q] at hh ⊢; linarith
         _ ≤ _ := hpow

theorem expLo_sound {x : ℤ} (hx : -(2*q) ≤ x) :
    (expLo x : ℝ)/q ≤ Real.exp ((x:ℝ)/q) := by
  have hf := floor_spec x 4096 (by decide)
  have hv : 0 ≤ q + x/4096 := by dsimp [q] at *; omega
  have hp := Real.add_one_le_exp ((x:ℝ)/(q*4096))
  have hbase : ((q+x/4096 : ℤ):ℝ)/q ≤ Real.exp ((x:ℝ)/(q*4096)) := by
    push_cast
    dsimp [q] at *; linarith
  have hh := (squares_le hv hbase 12).2
  rw [← Real.exp_nat_mul] at hh
  convert hh using 2 <;> norm_num [expLo, q]
  ring

private theorem squareDown_mono {v w : ℤ} (hv : 0 ≤ v) (hvw : v ≤ w) (n : ℕ) :
    0 ≤ squareDown n v ∧ squareDown n v ≤ squareDown n w := by
  induction n with
  | zero => exact ⟨hv,hvw⟩
  | succ n ih =>
    have hw := ih.1.trans ih.2
    exact ⟨Int.ediv_nonneg (mul_nonneg ih.1 ih.1) (by decide),
      Int.ediv_le_ediv (by decide) (mul_le_mul ih.2 ih.2 ih.1 hw)⟩

theorem expLo_floor {x : ℤ} (hx : -(2*q) ≤ x) : q / 8 ≤ expLo x := by
  have hv : 0 ≤ q + (-(2*q))/4096 := by decide
  have hh : q + (-(2*q))/4096 ≤ q + x/4096 :=
    add_le_add_right (Int.ediv_le_ediv (by decide) hx) q
  exact (show q / 8 ≤ expLo (-(2*q)) by decide).trans (squareDown_mono hv hh 12).2

theorem expLo_pos {x : ℤ} (hx : -(2*q) ≤ x) : 0 < expLo x :=
  (show 0 < q / 8 by decide).trans_le (expLo_floor hx)

theorem expHi_sound {x : ℤ} (hx : x ≤ 2*q) :
    Real.exp ((x:ℝ)/q) ≤ (expHi x : ℝ)/q := by
  have hd := expLo_pos (x := -x) (by omega)
  have hl := expLo_sound (x := -x) (by omega)
  push_cast at hl
  rw [neg_div, Real.exp_neg] at hl
  have he := (le_div_iff₀ (Real.exp_pos ((x:ℝ)/q))).mp (by simpa [one_div] using hl :
    (expLo (-x) : ℝ)/q ≤ 1/Real.exp ((x:ℝ)/q))
  have hden : 0 < (expLo (-x) : ℝ) := by exact_mod_cast hd
  have hu := ceil_spec (q*q) (expLo (-x)) hd
  push_cast at hu
  have hinv : Real.exp ((x:ℝ)/q) ≤ (q:ℝ)/(expLo (-x):ℝ) := by
    apply (le_div_iff₀ hden).2
    dsimp [q] at he ⊢; linarith
  apply hinv.trans
  apply (le_div_iff₀ (show (0:ℝ)<q by norm_num [q])).2
  rw [div_mul_eq_mul_div]
  exact hu

#print axioms expLo_sound
#print axioms expHi_sound
end YangMills.DyadicExp
