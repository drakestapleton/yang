-- SPDX-License-Identifier: Apache-2.0
import WilsonBlocking

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real
noncomputable section
private abbrev Config (l : ℕ+) := Configuration gaugeGroup l

/-- A product of normalized Wilson plaquette traces. Repeated faces are allowed. -/
def plaquetteProduct {l : ℕ+} : List (Face l) → Config l → ℝ
  | [], _ => 1
  | p :: ps, U => wilsonPlaquetteTrace p U * plaquetteProduct ps U

theorem plaquetteProduct_gauge {l : ℕ+} (ps : List (Face l)) (Ω : Site l → gaugeGroup.image) (U : Config l) :
    plaquetteProduct ps (gaugeAct Ω U) = plaquetteProduct ps U := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [plaquetteProduct, plaquetteProduct, wilsonPlaquetteTrace_gauge_invariant, ih]

theorem plaquetteProduct_abs_le_one {l : ℕ+} (ps : List (Face l)) (U : Config l) : |plaquetteProduct ps U| ≤ 1 := by
  induction ps with
  | nil => simp [plaquetteProduct]
  | cons p ps ih =>
    have eq : wilsonPlaquetteTrace p U = cos (polarAngle (plaquette U p.1 p.2.val.1 p.2.val.2)) := by
      rw [wilsonPlaquetteTrace, scalar_trace, cos_polarAngle]; ring
    rw [plaquetteProduct, abs_mul, eq]
    exact (mul_le_mul (abs_le.mpr ⟨neg_one_le_cos _,cos_le_one _⟩) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem plaquetteProduct_continuous {l : ℕ+} (ps : List (Face l)) : Continuous (plaquetteProduct ps) := by
  induction ps with
  | nil => exact continuous_const
  | cons p ps ih => exact (wilsonPlaquetteTrace_variation p).continuous.mul ih

private def productProfile (b : ℕ+) {l : ℕ+} : List (Face l) → Edge (b*l) → ℝ
  | [], _ => 0
  | p :: ps, e => blockProfile b (plaquetteWeight p) e + productProfile b ps e

private theorem productProfile_bounds (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) (ps : List (Face l)) (e : Edge (b*l)) :
    0 ≤ productProfile b ps e ∧ productProfile b ps e ≤ ps.length := by
  induction ps with
  | nil => simp [productProfile]
  | cons p ps ih =>
    obtain ⟨h0,h1⟩ := blockedPlaquetteProfile_bounds b hl p e
    exact ⟨add_nonneg h0 ih.1,by simpa [productProfile, add_comm] using add_le_add h1 ih.2⟩

private theorem productProfile_sum (b : ℕ+) {l : ℕ+} (ps : List (Face l)) :
    ∑ e, productProfile b ps e = 4*b.val*ps.length := by
  induction ps with
  | nil => simp [productProfile]
  | cons p ps ih =>
    simp only [productProfile, Finset.sum_add_distrib, blockedPlaquetteProfile_sum, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

private theorem product_variation (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) (ps : List (Face l)) :
    LinkVariation (productProfile b ps) (plaquetteProduct ps ∘ blockLinks b) := by
  induction ps with
  | nil => intro U V; simp [plaquetteProduct, productProfile, Function.comp]
  | cons p ps ih =>
    intro U V
    let u : Config l := blockLinks b U
    let v : Config l := blockLinks b V
    let x := wilsonPlaquetteTrace p u
    let y := wilsonPlaquetteTrace p v
    let s := plaquetteProduct ps u
    let t := plaquetteProduct ps v
    have hy : |y| ≤ 1 := by simpa [y,plaquetteProduct] using plaquetteProduct_abs_le_one [p] v
    have hs : |s| ≤ 1 := plaquetteProduct_abs_le_one ps u
    change |x*s-y*t| ≤ _
    calc
      _ = |(x-y)*s + y*(s-t)| := by congr 1; ring
      _ ≤ |(x-y)*s| + |y*(s-t)| := abs_add_le ..
      _ ≤ |x-y| + |s-t| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hs) (mul_le_of_le_one_left (abs_nonneg _) hy)
      _ ≤ _ := by
        have hp := (wilsonPlaquetteTrace_variation p).blockLinks b (fun e => (plaquetteWeight_bounds hl p e).1) U V
        simp only [productProfile, add_mul, Finset.sum_add_distrib]
        exact add_le_add hp (ih U V)

private theorem productProfile_support (b : ℕ+) {l : ℕ+} (ps : List (Face l)) (e : Edge (b*l))
    (he : productProfile b ps e ≠ 0) : ∃ p ∈ ps, blockProfile b (plaquetteWeight p) e ≠ 0 := by
  induction ps with
  | nil => exact (he rfl).elim
  | cons p ps ih =>
    by_cases h : blockProfile b (plaquetteWeight p) e = 0
    · have htail : productProfile b ps e ≠ 0 := by simpa [productProfile,h] using he
      obtain ⟨q,hq,hv⟩ := ih htail
      exact ⟨q,List.mem_cons_of_mem _ hq,hv⟩
    · exact ⟨p,List.mem_cons_self ..,h⟩

/-- Spatial insertions may occupy several slices in each word. Every cross
pair must respect k steps of cyclic time separation. -/
def separatedPlaquetteProducts {l : ℕ+} (t : Axis) (k : ℕ) (ps qs : List (Face l)) : Prop :=
  ∀ p ∈ ps, ∀ q ∈ qs, t ≠ p.2.val.1 ∧ t ≠ p.2.val.2 ∧ t ≠ q.2.val.1 ∧ t ≠ q.2.val.2 ∧
    k ≤ (q.1 t-p.1 t).valMinAbs.natAbs

theorem blockedProduct_clustering (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (t : Axis) (k : ℕ) (ps qs : List (Face l))
    (hs : separatedPlaquetteProducts t k ps qs) :
    |blockedCovariance b β (plaquetteProduct ps) (plaquetteProduct qs)| ≤
      (ps.length * (qs.length:ℝ)) * (4*b.val*π^2/(1-straightRow β)) * (straightRow β ^ b.val)^k := by
  have hfine : 1 < (b*l).val := hl.trans_le (Nat.le_mul_of_pos_left _ b.prop)
  have sep : SupportsSeparated (productProfile b ps) (productProfile b qs) (b.val*k) := by
    apply supportsSeparated_of_axis hfine t
    intro e a he ha
    obtain ⟨p,hp,hpe⟩ := productProfile_support b ps e he
    obtain ⟨q,hq,hqa⟩ := productProfile_support b qs a ha
    obtain ⟨hi,hj,hi',hj',hk⟩ := hs p hp q hq
    rw [periodicAxisDistance, blockedPlaquette_slice b t p hi hj e hpe, blockedPlaquette_slice b t q hi' hj' a hqa,
      blockCoordinate_distance b l]
    exact Nat.mul_le_mul_left _ hk
  rw [blockedCovariance_eq b β (plaquetteProduct_continuous ps) (plaquetteProduct_continuous qs)]
  have H := wilson_spatial_clustering hfine hβ hwindow (B := qs.length) (Nat.cast_nonneg _)
    (fun e => (productProfile_bounds b hl ps e).1) (fun e => (productProfile_bounds b hl qs e).1)
    (fun e => (productProfile_bounds b hl qs e).2) (product_variation b hl ps) (product_variation b hl qs) _ sep
  rw [productProfile_sum, pow_mul] at H
  convert H using 1
  ring

/-- One real coefficient in a signed expansion of connected Wilson correlations. -/
structure WilsonProductTerm (l : ℕ+) where
  coefficient : ℝ
  left : List (Face l)
  right : List (Face l)

def productExpansion (b : ℕ+) {l : ℕ+} (β : ℝ) (terms : List (WilsonProductTerm l)) :=
  (terms.map fun a => a.coefficient * blockedCovariance b β (plaquetteProduct a.left) (plaquetteProduct a.right)).sum

def productExpansionWeight {l : ℕ+} (terms : List (WilsonProductTerm l)) :=
  (terms.map fun a => |a.coefficient| * (a.left.length * (a.right.length:ℝ))).sum

theorem productExpansion_bound (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (t : Axis) (k : ℕ) (terms : List (WilsonProductTerm l))
    (hs : ∀ a ∈ terms, a.coefficient ≠ 0 → separatedPlaquetteProducts t k a.left a.right) :
    |productExpansion b β terms| ≤ productExpansionWeight terms *
      ((4*b.val*π^2/(1-straightRow β))*(straightRow β ^ b.val)^k) := by
  induction terms with
  | nil => simp [productExpansion, productExpansionWeight]
  | cons a as ih =>
    have hrest := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    simp only [productExpansion, productExpansionWeight, List.map_cons, List.sum_cons, add_mul]
    apply (abs_add_le ..).trans (add_le_add ?_ hrest)
    by_cases h : a.coefficient = 0
    · simp [h]
    · rw [abs_mul]
      apply (mul_le_mul_of_nonneg_left (blockedProduct_clustering b hl hβ hwindow t k _ _
        (hs a (List.mem_cons_self ..) h)) (abs_nonneg _)).trans_eq
      ring

#print axioms plaquetteProduct_gauge
#print axioms blockedProduct_clustering
#print axioms productExpansion_bound
end
end YangMills.PeriodicWilson
