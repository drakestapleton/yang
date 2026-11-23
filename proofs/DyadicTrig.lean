import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds

namespace YangMills.DyadicTrig

/-- Integer endpoints represent multiples of 2⁻³⁰. -/
abbrev Bounds := ℤ × ℤ

def scale : ℤ := 1073741824

def Contains (b : Bounds) (x : ℝ) : Prop :=
  (b.1 : ℝ) ≤ scale * x ∧ scale * x ≤ (b.2 : ℝ)

def halfRoot (a : ℤ) : ℕ := ((scale + a).toNat * 536870912).sqrt

def half (b : Bounds) : Bounds :=
  (halfRoot b.1, min scale ((halfRoot b.2 : ℤ) + 1))

def reflect (b : Bounds) : Bounds := (-b.2, -b.1)

/-- Half-angle enclosure. Truncation to Nat also permits a lower endpoint below -scale. -/
theorem half_sound {b : Bounds} {t : ℝ} (ht : 0 ≤ Real.cos t)
    (h : Contains b (Real.cos (2*t))) : Contains (half b) (Real.cos t) := by
  have id := Real.cos_two_mul t
  have hb := Real.cos_le_one t
  obtain ⟨hl, hu⟩ := h
  simp only [scale, Int.cast_ofNat] at hl hu
  have lower := Nat.sqrt_le' ((scale + b.1).toNat * 536870912)
  have upper := Nat.lt_succ_sqrt' ((scale + b.2).toNat * 536870912)
  change (halfRoot b.1)^2 ≤ _ at lower
  change _ < (halfRoot b.2).succ ^ 2 at upper
  have hu0 : 0 ≤ scale + b.2 := by
    have : (0:ℝ) ≤ 1073741824 + b.2 := by linarith [Real.neg_one_le_cos (2*t)]
    exact_mod_cast this
  have huCast : (((scale + b.2).toNat : ℕ) : ℝ) = 1073741824 + b.2 := by
    exact_mod_cast Int.toNat_of_nonneg hu0
  have hU : (((scale+b.2).toNat : ℕ) : ℝ) * 536870912 < ((halfRoot b.2 : ℝ)+1)^2 := by exact_mod_cast upper
  rw [huCast] at hU
  simp only [Contains, half, scale, Int.cast_natCast, Int.cast_ofNat, Int.cast_min, Int.cast_add, Int.cast_one]
  constructor
  · by_cases hp : 0 ≤ scale + b.1
    · have hCast : (((scale + b.1).toNat : ℕ) : ℝ) = 1073741824 + b.1 := by
        exact_mod_cast Int.toNat_of_nonneg hp
      have hL : (halfRoot b.1 : ℝ)^2 ≤ (((scale+b.1).toNat : ℕ) : ℝ) * 536870912 := by exact_mod_cast lower
      rw [hCast] at hL
      apply le_of_sq_le_sq _ (by positivity)
      nlinarith [hl, id]
    · have hz : (scale+b.1).toNat = 0 := Int.toNat_of_nonpos (by omega)
      simp [halfRoot, hz, ht]
  · apply le_min (by linarith)
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [hu, id]

noncomputable def angle (n i : ℕ) : ℝ := (i : ℝ) * Real.pi / (2:ℝ)^n

/-- The cosine of the reflected angle changes sign. Quarter-turn endpoints are exact. -/
def cosBounds : ℕ → ℕ → Bounds
  | 0, i => if i = 0 then (scale, scale) else (-scale, -scale)
  | n+1, i =>
    if i = 0 then (scale, scale)
    else if i = 2^(n+1) then (-scale, -scale)
    else if i = 2^n then (0, 0)
    else if i < 2^n then half (cosBounds n i)
    else reflect (half (cosBounds n (2^(n+1)-i)))

private theorem half_step {n i : ℕ} (hi : i ≤ 2^n)
    (h : Contains (cosBounds n i) (Real.cos (angle n i))) :
    Contains (half (cosBounds n i)) (Real.cos (angle (n+1) i)) := by
  apply half_sound
  · apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ angle (n+1) i := by unfold angle; positivity
      linarith [Real.pi_pos]
    · unfold angle
      apply (div_le_iff₀ (by positivity)).2
      have hi' : (i:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hi
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hi' Real.pi_pos.le]
  · convert h using 2
    unfold angle
    rw [pow_succ]
    field_simp

theorem cosBounds_sound (n i : ℕ) (hi : i ≤ 2^n) :
    Contains (cosBounds n i) (Real.cos (angle n i)) := by
  induction n generalizing i with
  | zero =>
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl <;> simp [cosBounds, angle, Contains, scale]
  | succ n ih =>
    by_cases h0 : i = 0
    · subst i; simp [cosBounds, angle, Contains, scale]
    by_cases hend : i = 2^(n+1)
    · subst i; simp [cosBounds, angle, Contains, scale, ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) _)]
    by_cases hmid : i = 2^n
    · subst i
      have heq : angle (n+1) (2^n) = Real.pi/2 := by simp [angle, pow_succ]; field_simp
      simp [cosBounds, hend, heq, Contains]
    by_cases hlt : i < 2^n
    · simpa [cosBounds, h0, hend, hmid, hlt] using half_step hlt.le (ih i hlt.le)
    · let j := 2^(n+1) - i
      have hj : j ≤ 2^n := by dsimp [j]; rw [pow_succ]; omega
      have hjAngle : angle (n+1) i = Real.pi - angle (n+1) j := by
        simp only [angle, j, Nat.cast_sub hi, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
        ring
      obtain ⟨lo, up⟩ := half_step hj (ih j hj)
      rw [hjAngle, Real.cos_pi_sub]
      simpa [cosBounds, h0, hend, hmid, hlt, reflect, Contains, j] using
        And.intro (neg_le_neg up) (neg_le_neg lo)

def sinLowIdx (i : ℕ) := if i < 1024 then 1024-i else i-1023
def sinHighIdx (i : ℕ) := if i < 1024 then 1023-i else i-1024

def sinSqBounds (i : ℕ) : Bounds :=
  let l := max 0 (cosBounds 11 (sinLowIdx i)).1
  let h := (cosBounds 11 (sinHighIdx i)).2
  (l^2/1024, (h^2+1023)/1024)

/-- Bounds throughout the cell, including the regridding of the squared sine to 2⁻⁵⁰. -/
theorem grid_cell_sound {i : ℕ} (hi : i < 2048) {t : ℝ}
    (ht : t ∈ Set.Icc (angle 11 i) (angle 11 (i+1))) :
    ((cosBounds 11 (i+1)).1 : ℝ) ≤ scale * Real.cos t ∧
    scale * Real.cos t ≤ ((cosBounds 11 i).2 : ℝ) ∧
    ((sinSqBounds i).1 : ℝ) ≤ 1125899906842624 * Real.sin t ^ 2 ∧
    1125899906842624 * Real.sin t ^ 2 ≤ ((sinSqBounds i).2 : ℝ) := by
  have ends (k : ℕ) (hk : k ≤ 2048) : angle 11 k ∈ Set.Icc 0 Real.pi := by
    constructor
    · unfold angle; positivity
    · have hk' : (k:ℝ) ≤ 2048 := by exact_mod_cast hk
      unfold angle; norm_num
      nlinarith [mul_le_mul_of_nonneg_right hk' Real.pi_pos.le]
  have left := ends i (by omega)
  have right := ends (i+1) (by omega)
  have ht0 := left.1.trans ht.1
  have htπ := ht.2.trans right.2
  have hQ : (0:ℝ) ≤ scale := by norm_num [scale]
  refine ⟨(cosBounds_sound 11 (i+1) (by norm_num; omega)).1.trans
    (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi ht0 right.2 ht.2) hQ),
    (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi left.1 htπ ht.1) hQ).trans
    (cosBounds_sound 11 i (by norm_num; omega)).2, ?_⟩
  let a := |Real.pi/2 - t|
  have ha : angle 11 (sinHighIdx i) ≤ a ∧ a ≤ angle 11 (sinLowIdx i) := by
    obtain ⟨hl,hu⟩ := ht
    norm_num [angle] at hl hu
    by_cases h : i < 1024
    · have hcast : (i:ℝ)+1 ≤ 1024 := by exact_mod_cast (show i+1 ≤ 1024 by omega)
      have hab : 0 ≤ Real.pi/2-t := by nlinarith [mul_le_mul_of_nonneg_right hcast Real.pi_pos.le]
      simp [a, abs_of_nonneg hab, sinHighIdx, sinLowIdx, h, angle, Nat.cast_sub (show i ≤ 1023 by omega),
        Nat.cast_sub (show i ≤ 1024 by omega)]
      constructor <;> linarith
    · have hcast : 1024 ≤ (i:ℝ) := by exact_mod_cast (show 1024 ≤ i by omega)
      have hab : Real.pi/2-t ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_right hcast Real.pi_pos.le]
      simp only [a, abs_of_nonpos hab, sinHighIdx, sinLowIdx, if_neg h, angle,
        Nat.cast_sub (show 1024 ≤ i by omega), Nat.cast_sub (show 1023 ≤ i by omega), Nat.cast_ofNat]
      norm_num
      constructor <;> linarith
  have jl : sinLowIdx i ≤ 2048 := by unfold sinLowIdx; split <;> omega
  have jh : sinHighIdx i ≤ 2048 := by unfold sinHighIdx; split <;> omega
  have hs : Real.cos a = Real.sin t := by rw [Real.cos_abs, Real.cos_pi_div_two_sub]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi ht0 htπ
  have lower := (cosBounds_sound 11 _ (by simpa using jl)).1.trans
    (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (ends _ jl).2 ha.2) hQ)
  have upper := (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi (ends _ jh).1
    (ha.2.trans (ends _ jl).2) ha.1) hQ).trans (cosBounds_sound 11 _ (by simpa using jh)).2
  rw [hs] at lower upper
  let l := max 0 (cosBounds 11 (sinLowIdx i)).1
  let h := (cosBounds 11 (sinHighIdx i)).2
  have hl : (l:ℝ) ≤ scale * Real.sin t := by simpa [l] using max_le (mul_nonneg hQ hsin) lower
  have hln : (0:ℝ) ≤ l := by simp [l]
  have sl := pow_le_pow_left₀ hln hl 2
  have su := pow_le_pow_left₀ (mul_nonneg hQ hsin) upper 2
  have fl : (l^2/1024)*1024 ≤ l^2 := by omega
  have ce : h^2 ≤ ((h^2+1023)/1024)*1024 := by omega
  have fl' : ((l^2/1024 : ℤ):ℝ)*1024 ≤ (l:ℝ)^2 := by exact_mod_cast fl
  have ce' : (h:ℝ)^2 ≤ (((h^2+1023)/1024 : ℤ):ℝ)*1024 := by exact_mod_cast ce
  change ((l^2/1024 : ℤ):ℝ) ≤ _ ∧ _ ≤ (((h^2+1023)/1024 : ℤ):ℝ)
  change _ ≤ (h:ℝ)^2 at su
  norm_num [scale] at sl su
  constructor <;> nlinarith

/-- Integer angle indices for the first-quadrant star-cell cutoffs entered in radians. -/
def radialLo (a : ℕ) := a*204800000/(314160*268435456)
def radialHi (a : ℕ) := ((a+1)*204800000 + (314159*268435456-1))/(314159*268435456)

private theorem rounded_up_mul (a d : ℕ) (hd : 0 < d) :
    a ≤ ((a+(d-1))/d)*d := by
  have h := Nat.lt_mul_div_succ (a+(d-1)) hd
  rw [Nat.mul_succ, Nat.mul_comm d] at h
  omega

theorem radial_indices_sound {a : ℕ} {t : ℝ} (ht : t ≤ 3/2)
    (hl : (a:ℝ) ≤ t*268435456) (hu : t*268435456 ≤ a+1) :
    radialHi a ≤ 1024 ∧ angle 11 (radialLo a) ≤ t ∧ t ≤ angle 11 (radialHi a) := by
  have ha : a ≤ 402653184 := by exact_mod_cast (show (a:ℝ) ≤ 402653184 by linarith)
  have hL : radialLo a*(314160*268435456) ≤ a*204800000 := by norm_num [radialLo]; omega
  have hH : (a+1)*204800000 ≤ radialHi a*(314159*268435456) := rounded_up_mul _ _ (by decide)
  have hL' : (radialLo a:ℝ)*(314160*268435456) ≤ (a:ℝ)*204800000 := by exact_mod_cast hL
  have hH' : ((a:ℝ)+1)*204800000 ≤ (radialHi a:ℝ)*(314159*268435456) := by exact_mod_cast hH
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 314159*268435456)).2
    omega
  · have hp := mul_le_mul_of_nonneg_left Real.pi_lt_d4.le (show 0 ≤ (radialLo a:ℝ) by positivity)
    norm_num [angle]; linarith
  · have hp := mul_le_mul_of_nonneg_left Real.pi_gt_d6.le (show 0 ≤ (radialHi a:ℝ) by positivity)
    have hq := mul_le_mul_of_nonneg_left (show (3.14159:ℝ) ≤ 3.141592 by norm_num)
      (show 0 ≤ (radialHi a:ℝ) by positivity)
    norm_num [angle]; linarith

theorem radial_trig_sound {a : ℕ} {t : ℝ} (ht : t ≤ 3/2)
    (hl : (a:ℝ) ≤ t*268435456) (hu : t*268435456 ≤ a+1) :
    ((cosBounds 11 (radialHi a)).1 : ℝ) ≤ scale*Real.cos t ∧
    scale*Real.cos t ≤ ((cosBounds 11 (radialLo a)).2 : ℝ) ∧
    ((cosBounds 11 (1024-radialLo a)).1 : ℝ) ≤ scale*Real.sin t ∧
    scale*Real.sin t ≤ ((cosBounds 11 (1024-radialHi a)).2 : ℝ) := by
  obtain ⟨hh,hlt,hut⟩ := radial_indices_sound ht hl hu
  have ht0 : 0 ≤ t := by linarith [(Nat.cast_nonneg a : 0 ≤ (a:ℝ))]
  have hlow : radialLo a ≤ 1024 := by
    have ha : a ≤ 402653184 := by exact_mod_cast (show (a:ℝ) ≤ 402653184 by linarith)
    unfold radialLo; omega
  have endmem {j : ℕ} (hj : j ≤ 1024) : angle 11 j ∈ Set.Icc 0 (Real.pi/2) := by
    have hj' : (j:ℝ) ≤ 1024 := by exact_mod_cast hj
    norm_num [angle]; constructor
    · positivity
    · linarith [mul_le_mul_of_nonneg_right hj' Real.pi_pos.le]
  have hc {j k : ℕ} {u : ℝ} (hj : j ≤ 1024) (hk : k ≤ 1024)
      (hj' : angle 11 j ≤ u) (hk' : u ≤ angle 11 k) :
      ((cosBounds 11 k).1:ℝ) ≤ scale*Real.cos u ∧ scale*Real.cos u ≤ ((cosBounds 11 j).2:ℝ) := by
    have hkπ : angle 11 k ≤ Real.pi := by linarith [(endmem hk).2, Real.pi_pos]
    have hQ : 0 ≤ (scale:ℝ) := by norm_num [scale]
    exact ⟨(cosBounds_sound 11 k (by norm_num; omega)).1.trans
      (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi ((endmem hj).1.trans hj') hkπ hk') hQ),
      (mul_le_mul_of_nonneg_left (Real.cos_le_cos_of_nonneg_of_le_pi (endmem hj).1 (hk'.trans hkπ) hj') hQ).trans
        (cosBounds_sound 11 j (by norm_num; omega)).2⟩
  have refl {j : ℕ} (hj : j ≤ 1024) : angle 11 (1024-j) = Real.pi/2 - angle 11 j := by
    simp [angle, Nat.cast_sub hj]; ring
  have hs := hc (j := 1024-radialHi a) (k := 1024-radialLo a) (u := Real.pi/2-t)
    (by omega) (by omega) (by rw [refl hh]; linarith) (by rw [refl hlow]; linarith)
  rw [Real.cos_pi_div_two_sub] at hs
  exact ⟨(hc hlow hh hlt hut).1, (hc hlow hh hlt hut).2, hs⟩

#print axioms radial_trig_sound
#print axioms grid_cell_sound
#print axioms cosBounds_sound
end YangMills.DyadicTrig
