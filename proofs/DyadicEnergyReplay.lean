import DyadicPolarFlux
import Mathlib.Algebra.BigOperators.Intervals

open YangMills.DyadicExp YangMills.DyadicPartition YangMills.DyadicPolarFlux

namespace YangMills.DyadicEnergyReplay

/-- Materialize the angular data once for the two sweeps. -/
@[noinline] def cache {α : Type} (f : ℕ → α) : Array α :=
  Array.ofFn (fun i : Fin 2048 => f i)

def atIndex {α : Type} [Inhabited α] (a : Array α) (i : ℕ) := a[i]?.getD default

theorem cache_eq {α : Type} [Inhabited α] (f : ℕ → α) {i : ℕ} (hi : i < 2048) :
    atIndex (cache f) i = f i := by simp [atIndex,cache,hi]

def total (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => total f n + f n

theorem total_eq (f : ℕ → ℤ) (n : ℕ) : total f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp [total,ih,Finset.sum_range_succ]

structure Row where
  cell : Cell
  wl : ℤ
  wh : ℤ
  deriving Inhabited

def row (c : Cell) (rl rh : ℤ) : Row := ⟨c,weightLo c rl rh,weightHi c rl rh⟩

structure Scan where
  lo : ℤ
  hi : ℤ
  cost : ℤ

def sweep (read : ℕ → Row) (back : Bool) (ml mh : ℤ) : ℕ → Scan
  | 0 => ⟨0,0,0⟩
  | j+1 =>
    let s := sweep read back ml mh j
    let a := read (index back j)
    let dl := lowerSlope back a.cell ml mh a.wl a.wh
    let dh := upperSlope back a.cell ml mh a.wl a.wh
    ⟨s.lo+dl,s.hi+dh,s.cost + cellCost j a.wh a.wl (fluxCap s.lo s.hi dl dh)⟩

theorem sweep_eq (read : ℕ → Row) (back : Bool) (rl rh : ℤ)
    (lookup : ∀ i < 2048, read i = row (angleCell i) rl rh) {n : ℕ} (hn : n ≤ 1024) :
    sweep read back (meanLo rl rh) (meanHi rl rh) n =
    ⟨runningSlope true back n rl rh,runningSlope false back n rl rh,
      ∑ j ∈ Finset.range n, energyCell back j rl rh⟩ := by
  induction n with
  | zero => simp [sweep,runningSlope]
  | succ n ih =>
    have hi : index back n < 2048 := by cases back <;> simp [index] <;> omega
    simp only [sweep,ih (by omega),lookup _ hi,row,runningSlope,Finset.sum_range_succ,
      increment, if_true, Bool.false_eq_true, if_false, energyCell]

private theorem split_cost (rl rh : ℤ) :
    (∑ i ∈ Finset.range 2048, gridCost i rl rh) =
    (∑ j ∈ Finset.range 1024, energyCell false j rl rh) +
    (∑ j ∈ Finset.range 1024, energyCell true j rl rh) := by
  rw [show 2048=1024+1024 by decide, Finset.sum_range_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    simp [gridCost,Finset.mem_range.mp hi]
  · rw [← Finset.sum_range_reflect (fun j => energyCell true j rl rh) 1024]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [gridCost,show ¬1024+i<1024 by omega,if_false]
    rw [show 2047 - (1024+i) = 1024-1-i by omega]

/-- Both printed integers, including the rounded normalization and π² factor. -/
def evaluate (cells : Array Cell) (rl rh : ℤ) : ℤ × ℤ :=
  let rows := cache (fun i => row (atIndex cells i) rl rh)
  let read := atIndex rows
  let zl := total (fun i => (read i).wl) 2048 / 2048
  let zh := ceilDiv (total (fun i => (read i).wh) 2048) 2048
  let ml := ratioLo (total (fun i => loMul (read i).cell.cosLo (read i).wl (read i).wh) 2048 / 2048) zl zh
  let mh := ratioHi (ceilDiv (total (fun i => hiMul (read i).cell.cosHi (read i).wl (read i).wh) 2048) 2048) zl zh
  let trans := ceilDiv (total (fun i => ceilDiv (transverseCap (read i).cell rl rh * (read i).wh) q) 2048) 2048
  let energy := (sweep read false ml mh 1024).cost + (sweep read true ml mh 1024).cost
  (ceilDiv (ceilDiv (ceilDiv energy 2048*q) zl * 986961) 100000,ceilDiv (trans*q) zl)

theorem evaluate_eq (rl rh : ℤ) :
    evaluate (cache angleCell) rl rh =
    (parallelCap rl rh, ceilDiv (averageHi weightedCap rl rh*q) (averageLo weightLo rl rh)) := by
  let read := atIndex (cache (fun i => row (atIndex (cache angleCell) i) rl rh))
  have lookup (i : ℕ) (hi : i < 2048) : read i = row (angleCell i) rl rh := by
    simp [read,cache_eq _ hi]
  have sum (f : Row → ℤ) :
      total (fun i => f (read i)) 2048 = ∑ i ∈ Finset.range 2048, f (row (angleCell i) rl rh) := by
    rw [total_eq]; apply Finset.sum_congr rfl
    intro i hi; rw [lookup i (Finset.mem_range.mp hi)]
  have zl := sum Row.wl
  have zh := sum Row.wh
  have ml := sum (fun a => loMul a.cell.cosLo a.wl a.wh)
  have mh := sum (fun a => hiMul a.cell.cosHi a.wl a.wh)
  have tr := sum (fun a => ceilDiv (transverseCap a.cell rl rh*a.wh) q)
  change _ = ∑ i ∈ Finset.range 2048, momentLo (angleCell i) rl rh at ml
  change _ = ∑ i ∈ Finset.range 2048, momentHi (angleCell i) rl rh at mh
  change _ = ∑ i ∈ Finset.range 2048, weightedCap (angleCell i) rl rh at tr
  let zl' := averageLo weightLo rl rh
  let zh' := averageHi weightHi rl rh
  have eqzl : total (fun i => (read i).wl) 2048 / 2048 = zl' := congrArg (fun z : ℤ => z/2048) zl
  have eqzh : ceilDiv (total (fun i => (read i).wh) 2048) 2048 = zh' := congrArg (fun z => ceilDiv z 2048) zh
  have eqml : ratioLo (total (fun i => loMul (read i).cell.cosLo (read i).wl (read i).wh) 2048 / 2048) zl' zh' =
      meanLo rl rh := congrArg (fun z : ℤ => ratioLo (z/2048) zl' zh') ml
  have eqmh : ratioHi (ceilDiv (total (fun i => hiMul (read i).cell.cosHi (read i).wl (read i).wh) 2048) 2048) zl' zh' =
      meanHi rl rh := congrArg (fun z : ℤ => ratioHi (ceilDiv z 2048) zl' zh') mh
  have eqtr : ceilDiv (total (fun i => ceilDiv (transverseCap (read i).cell rl rh * (read i).wh) q) 2048) 2048 =
      averageHi weightedCap rl rh := congrArg (fun z => ceilDiv z 2048) tr
  have a := sweep_eq read false rl rh lookup (n:=1024) le_rfl
  have b := sweep_eq read true rl rh lookup (n:=1024) le_rfl
  dsimp only [evaluate]
  rw [← (show read = atIndex (cache (fun i => row (atIndex (cache angleCell) i) rl rh)) from rfl)]
  rw [eqzl,eqzh,eqml,eqmh,eqtr]
  rw [a,b]
  simp only
  rw [← split_cost]
  rfl

def fieldLo (b k : ℤ) := 6*b*q*k/1280000
def fieldHi (b k : ℤ) := ceilDiv (6*b*q*(k+1)) 1280000

open YangMills.OneLinkTransport

/-- One of the printed pairs bounds both real trial energies throughout its field box.
The endpoints of adjacent boxes may overlap by one integer rounding unit. -/
theorem field_bounds {b k : ℤ} (hb : 0 ≤ b) (hb' : b ≤ 2880) (hk : 0 ≤ k) (hk' : k < 128)
    {r : ℝ} (left : 6*(b:ℝ)*k/1280000 ≤ r) (right : r ≤ 6*(b:ℝ)*(k+1)/1280000) :
    let v := evaluate (cache angleCell) (fieldLo b k) (fieldHi b k)
    parallelEnergy r ≤ (v.1:ℝ)/q ∧ transverseEnergy r ≤ (v.2:ℝ)/q := by
  have hh := mul_le_mul hb' (show k+1 ≤ 128 by omega) (by omega) (by decide : (0:ℤ) ≤ 2880)
  have l0 : 0 ≤ fieldLo b k := by unfold fieldLo q; apply Int.ediv_nonneg <;> positivity
  have lnum := floor_mul_bound (6*b*q*k) (show (0:ℤ)<1280000 by decide)
  have hnum := ceil_mul_bound (6*b*q*(k+1)) (show (0:ℤ)<1280000 by decide)
  change (fieldLo b k:ℝ)*_ ≤ _ at lnum
  change _ ≤ (fieldHi b k:ℝ)*_ at hnum
  push_cast at lnum hnum
  have low : (fieldLo b k:ℝ)/q ≤ r := by norm_num [q] at lnum ⊢; linarith
  have high : r ≤ (fieldHi b k:ℝ)/q := by norm_num [q] at hnum ⊢; linarith
  have ord : fieldLo b k ≤ fieldHi b k := by
    have pos : (0:ℝ)<q := by norm_num [q]
    exact_mod_cast (div_le_div_iff_of_pos_right pos).mp (low.trans high)
  have up : fieldHi b k ≤ 2*q := by
    unfold fieldHi ceilDiv
    have bound : 6*b*q*(k+1) ≤ 2*q*1280000 := by norm_num [q] at *; nlinarith
    omega
  have hr : 0 ≤ r := (div_nonneg (by exact_mod_cast l0) (by norm_num [q])).trans low
  rw [evaluate_eq]
  refine ⟨normalized_parallel hr low high l0 ord up,?_⟩
  have cost (t : ℝ) : transverseCost r (Real.cos t) = transverseTrial r t := by
    unfold transverseCost transverseTrial
    rw [Real.sin_sq]; ring
  unfold transverseEnergy
  simp only [cost]
  exact normalized_transverse hr low high l0 ord up

#print axioms field_bounds
#print axioms evaluate_eq

end YangMills.DyadicEnergyReplay
