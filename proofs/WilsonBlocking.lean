-- SPDX-License-Identifier: Apache-2.0
import WilsonPlaquetteClustering

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer Real MeasureTheory
noncomputable section
private abbrev Config (l : ℕ+) := Configuration gaugeGroup l

/-- Embed one coarse periodic coordinate at its block origin. -/
def blockCoordinate (b l : ℕ+) : ZMod l.val →+ ZMod (b*l).val where
  toFun x := (b.val * x.val : ℕ)
  map_zero' := by
    change ((b.val * (0 : ZMod l.val).val : ℕ) : ZMod (b*l).val) = 0
    rw [ZMod.val_zero, Nat.mul_zero, Nat.cast_zero]
  map_add' x y := by
    simp only [ZMod.val_add, ← Nat.cast_add, ← Nat.mul_add]
    apply (ZMod.natCast_eq_natCast_iff' ..).2
    change _ % (b.val*l.val) = _ % (b.val*l.val)
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]

@[simp] theorem blockCoordinate_val (b l : ℕ+) (x : ZMod l.val) :
    (blockCoordinate b l x).val = b.val*x.val :=
  ZMod.val_natCast_of_lt (Nat.mul_lt_mul_of_pos_left x.val_lt b.prop)

theorem blockCoordinate_distance (b l : ℕ+) (x y : ZMod l.val) :
    ((blockCoordinate b l y - blockCoordinate b l x).valMinAbs).natAbs =
      b.val*((y-x).valMinAbs).natAbs := by
  rw [← map_sub, ZMod.valMinAbs_natAbs_eq_min, ZMod.valMinAbs_natAbs_eq_min,
    blockCoordinate_val, PNat.mul_coe, ← Nat.mul_sub_left_distrib, Nat.mul_min_mul_left]

def blockSite (b : ℕ+) {l : ℕ+} (x : Site l) : Site (b*l) := fun t => blockCoordinate b l (x t)

private theorem blockSite_step (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) (x : Site l) (i : Axis) :
    blockSite b (x + Pi.single i 1) = blockSite b x + b.val • Pi.single i 1 := by
  haveI : Fact (1 < l.val) := ⟨hl⟩
  funext t
  change blockCoordinate b l (x t + (Pi.single i 1 : Site l) t) =
    blockCoordinate b l (x t) + b.val • ((Pi.single i 1 : Site (b*l)) t)
  rw [map_add]
  by_cases h : t = i
  · subst t
    simp only [Pi.single_eq_same, add_right_inj]
    change ((b.val * (1 : ZMod l.val).val : ℕ) : ZMod (b*l).val) = _
    rw [ZMod.val_one l.val, Nat.mul_one]
    exact (nsmul_one _).symm
  · simp only [Pi.single_eq_of_ne h, map_zero, nsmul_zero]

/-- Ordered product of the next n positive links, including periodic wraparound. -/
def straightPath {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (x : Site l) (i : Axis) :
    ℕ → g.image
  | 0 => 1
  | n+1 => straightPath U x i n * U (x + n • Pi.single i 1, i)

def blockLinks (b : ℕ+) {g : GaugeGroup} {l : ℕ+} (U : Configuration g (b*l)) :
    Configuration g l := fun e => straightPath U (blockSite b e.1) e.2 b.val

private theorem straightPath_gauge {g : GaugeGroup} {l : ℕ+} (Ω : Site l → g.image)
    (U : Configuration g l) (x : Site l) (i : Axis) (n : ℕ) :
    straightPath (gaugeAct Ω U) x i n =
      Ω x * straightPath U x i n * (Ω (x+n • Pi.single i 1))⁻¹ := by
  induction n with
  | zero => simp [straightPath]
  | succ n ih =>
    rw [straightPath, ih, straightPath]
    simp only [gaugeAct, succ_nsmul, ← add_assoc]
    group

/-- Interior gauge transformations cancel along each retained path. -/
theorem blockLinks_gauge {g : GaugeGroup} (b : ℕ+) {l : ℕ+} (hl : 1 < l.val)
    (Ω : Site (b*l) → g.image) (U : Configuration g (b*l)) :
    blockLinks b (gaugeAct Ω U) = gaugeAct (Ω ∘ blockSite b) (blockLinks b U) := by
  funext e
  simp only [blockLinks, straightPath_gauge, gaugeAct, Function.comp_apply, blockSite_step b hl]

theorem blockedPlaquette_gauge (b : ℕ+) {l : ℕ+} (hl : 1 < l.val)
    (Ω : Site (b*l) → gaugeGroup.image) (p : Face l) (U : Config (b*l)) :
    wilsonPlaquetteTrace p (blockLinks b (gaugeAct Ω U)) = wilsonPlaquetteTrace p (blockLinks b U) := by
  rw [blockLinks_gauge b hl, wilsonPlaquetteTrace_gauge_invariant]

private theorem straightPath_continuous {l : ℕ+} (x : Site l) (i : Axis) (n : ℕ) :
    Continuous (fun U : Config l => straightPath U x i n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.mul (continuous_apply _)

theorem blockLinks_continuous (b l : ℕ+) :
    Continuous (blockLinks b : Config (b*l) → Config l) :=
  continuous_pi fun e => straightPath_continuous (blockSite b e.1) e.2 b.val

/-- Exact marginal on ordered path products of the fine periodic Wilson field. -/
def blockedWilsonLaw (b l : ℕ+) (β : ℝ) : Measure (Config l) :=
  (wilsonLaw gaugeGroup (b*l) β su2Haar).map (blockLinks b)

instance blockedWilsonLaw_probability (b l : ℕ+) (β : ℝ) : IsProbabilityMeasure (blockedWilsonLaw b l β) := by
  haveI := wilson_probability (b*l) β
  exact Measure.isProbabilityMeasure_map (blockLinks_continuous b l).aemeasurable

theorem blockedWilsonLaw_integral (b l : ℕ+) (β : ℝ) {F : Config l → ℝ} (hF : Continuous F) :
    ∫ V, F V ∂blockedWilsonLaw b l β = ∫ U, F (blockLinks b U) ∂wilsonLaw gaugeGroup (b*l) β su2Haar :=
  integral_map (blockLinks_continuous b l).aemeasurable hF.aestronglyMeasurable

/-- The fine link with offset n in a retained coarse link. -/
def blockEdge (b : ℕ+) {l : ℕ+} (e : Edge l) (n : Fin b.val) : Edge (b*l) :=
  (blockSite b e.1 + n.val • Pi.single e.2 1, e.2)

private theorem blockEdge_coordinate (b : ℕ+) {l : ℕ+} (e : Edge l) (n : Fin b.val) (t : Axis) :
    ((blockEdge b e n).1 t).val = b.val*(e.1 t).val + (if t=e.2 then n.val else 0) := by
  have bound := Nat.mul_le_mul_left b.val (Nat.succ_le_of_lt (e.1 t).val_lt)
  rw [Nat.mul_succ] at bound
  change (blockCoordinate b l (e.1 t) + n.val • ((Pi.single e.2 1 : Site (b*l)) t)).val = _
  by_cases h : t = e.2
  · subst t
    simp only [Pi.single_eq_same, nsmul_eq_mul, mul_one]
    change (((b.val*(e.1 e.2).val : ℕ) : ZMod (b*l).val) + (n.val : ZMod (b*l).val)).val = _
    rw [← Nat.cast_add]
    apply ZMod.val_natCast_of_lt
    change _ < b.val*l.val
    omega
  · rw [Pi.single_eq_of_ne h, nsmul_zero, add_zero, blockCoordinate_val, if_neg h, Nat.add_zero]

/-- Distinct coarse links use disjoint fine links, even across a periodic seam. -/
theorem blockEdge_injective (b l : ℕ+) :
    Function.Injective (fun a : Edge l × Fin b.val => blockEdge b a.1 a.2) := by
  rintro ⟨⟨x,i⟩,n⟩ ⟨⟨y,j⟩,m⟩ h
  have hij : i=j := congrArg Prod.snd h
  subst j
  have coord (t : Axis) := congrArg (fun a : Edge (b*l) => (a.1 t).val) h
  simp only [blockEdge_coordinate] at coord
  have div (z : ℕ) (k : Fin b.val) : (b.val*z+k.val)/b.val = z :=
    (Nat.mul_add_div b.prop z k.val).trans ((congrArg (z + ·) (Nat.div_eq_of_lt k.isLt)).trans (Nat.add_zero z))
  have hx : x=y := by
    funext t
    apply ZMod.val_injective
    by_cases ht : t=i
    · have H := congrArg (fun a : ℕ => a/b.val) (coord t)
      simpa [ht, div] using H
    · have H := coord t
      simp [ht] at H
      exact H
  subst y
  have hn : n=m := by
    apply Fin.ext
    simpa using coord i
  subst m
  rfl

private theorem straightPath_distance {l : ℕ+} (U V : Config l) (x : Site l) (i : Axis) (n : ℕ) :
    linkGeodesic (straightPath U x i n) (straightPath V x i n) ≤
      ∑ k : Fin n, linkGeodesic (U (x + k.val • Pi.single i 1,i)) (V (x + k.val • Pi.single i 1,i)) := by
  induction n with
  | zero =>
    simp only [straightPath, Finset.univ_eq_empty, Finset.sum_empty]
    rw [linkGeodesic_eq_angle, InnerProductGeometry.angle_self]
    exact norm_ne_zero_iff.mp (by rw [coordinates_norm]; norm_num)
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    exact (linkGeodesic_product_le ..).trans (add_le_add ih le_rfl)

/-- Pull a coarse link Lipschitz profile back to its disjoint fine paths. -/
def blockProfile (b : ℕ+) {l : ℕ+} (v : Edge l → ℝ) (j : Edge (b*l)) : ℝ :=
  ∑ a : Edge l × Fin b.val, if blockEdge b a.1 a.2 = j then v a.1 else 0

private theorem blockProfile_on (b : ℕ+) {l : ℕ+} (v : Edge l → ℝ) (a : Edge l × Fin b.val) :
    blockProfile b v (blockEdge b a.1 a.2) = v a.1 := by
  have he (c : Edge l × Fin b.val) : blockEdge b c.1 c.2 = blockEdge b a.1 a.2 ↔ c=a :=
    (blockEdge_injective b l).eq_iff
  simp [blockProfile, he]

private theorem blockProfile_off (b : ℕ+) {l : ℕ+} (v : Edge l → ℝ) (j : Edge (b*l))
    (hj : ¬ ∃ a : Edge l × Fin b.val, blockEdge b a.1 a.2 = j) : blockProfile b v j = 0 := by
  push Not at hj
  simp [blockProfile, hj]

private theorem blockProfile_sum (b : ℕ+) {l : ℕ+} (v : Edge l → ℝ) :
    ∑ j, blockProfile b v j = b.val * ∑ e, v e := by
  unfold blockProfile
  rw [Finset.sum_comm]
  simp [Fintype.sum_prod_type, nsmul_eq_mul, Finset.mul_sum]

theorem LinkVariation.blockLinks {l : ℕ+} (b : ℕ+) {v : Edge l → ℝ} {F : Config l → ℝ}
    (hv : ∀ e, 0 ≤ v e) (hF : LinkVariation v F) : LinkVariation (blockProfile b v) (F ∘ blockLinks b) := by
  intro U V
  apply (hF _ _).trans
  calc
    _ ≤ ∑ e : Edge l, v e * ∑ n : Fin b.val,
          linkGeodesic (U (blockEdge b e n)) (V (blockEdge b e n)) :=
      Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (straightPath_distance ..) (hv e)
    _ = _ := by
      simp only [blockProfile, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp [Fintype.sum_prod_type, Finset.mul_sum]

private theorem plaquetteWeight_direction {l : ℕ+} (p : Face l) (e : Edge l)
    (he : plaquetteWeight p e ≠ 0) : e.2 = p.2.val.1 ∨ e.2 = p.2.val.2 := by
  by_contra! h
  have hcorner {c : Edge l} (hc : c.2 = p.2.val.1 ∨ c.2 = p.2.val.2) : e ≠ c := by
    rintro rfl
    exact hc.elim h.1 h.2
  exact he (by simp [plaquetteWeight, hcorner (.inl rfl : (corners p).1.2 = _ ∨ _),
    hcorner (.inr rfl : _ ∨ (corners p).2.1.2 = _),
    hcorner (.inl rfl : (corners p).2.2.1.2 = _ ∨ _),
    hcorner (.inr rfl : _ ∨ (corners p).2.2.2.2 = _)])

private theorem blockedPlaquette_slice (b : ℕ+) {l : ℕ+} (t : Axis) (p : Face l)
    (hi : t ≠ p.2.val.1) (hj : t ≠ p.2.val.2) (j : Edge (b*l))
    (h : blockProfile b (plaquetteWeight p) j ≠ 0) : j.1 t = blockCoordinate b l (p.1 t) := by
  by_cases hmem : ∃ a : Edge l × Fin b.val, blockEdge b a.1 a.2 = j
  · obtain ⟨a,rfl⟩ := hmem
    rw [blockProfile_on] at h
    have hdir : t ≠ a.1.2 := fun H => (plaquetteWeight_direction p a.1 h).elim
      (fun h1 => hi (H.trans h1)) (fun h2 => hj (H.trans h2))
    apply ZMod.val_injective
    exact (blockEdge_coordinate b a.1 a.2 t).trans (by rw [if_neg hdir, Nat.add_zero, plaquetteWeight_slice t hi hj h, blockCoordinate_val])
  · exact (h (blockProfile_off b _ j hmem)).elim

/-- Connected two-point function evaluated under the exact blocked law. -/
def blockedCovariance (b : ℕ+) {l : ℕ+} (β : ℝ) (F G : Config l → ℝ) :=
  let μ := blockedWilsonLaw b l β
  (∫ V, F V * G V ∂μ) - (∫ V, F V ∂μ) * ∫ V, G V ∂μ

theorem blockedCovariance_eq (b : ℕ+) {l : ℕ+} (β : ℝ) {F G : Config l → ℝ}
    (hF : Continuous F) (hG : Continuous G) :
    blockedCovariance b β F G = wilsonCovariance β (F ∘ blockLinks b) (G ∘ blockLinks b) := by
  dsimp only [blockedCovariance, wilsonCovariance, Function.comp_apply]
  rw [blockedWilsonLaw_integral b l β (F := fun V => F V * G V) (hF.mul hG), blockedWilsonLaw_integral b l β hF,
    blockedWilsonLaw_integral b l β hG]

/-- Spatial traces of b-by-b Wilson loops under exact blocking. The cyclic
time separation in the fine field is b times the coarse separation, and the
perimeter profile sums to 4b with no fine link counted twice. -/
theorem blockedWilson_plaquette_clustering (b : ℕ+) {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (t : Axis) (p q : Face l)
    (hpi : t ≠ p.2.val.1) (hpj : t ≠ p.2.val.2) (hqi : t ≠ q.2.val.1) (hqj : t ≠ q.2.val.2) :
    |blockedCovariance b β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)| ≤
      (4*b.val*π^2/(1-straightRow β))*(straightRow β ^ b.val)^((q.1 t-p.1 t).valMinAbs.natAbs) := by
  have hfine : 1 < (b*l).val := hl.trans_le (Nat.le_mul_of_pos_left _ b.prop)
  have bounds (f : Face l) (j : Edge (b*l)) :
      0 ≤ blockProfile b (plaquetteWeight f) j ∧ blockProfile b (plaquetteWeight f) j ≤ 1 := by
    by_cases H : ∃ a : Edge l × Fin b.val, blockEdge b a.1 a.2 = j
    · obtain ⟨a,rfl⟩ := H
      rw [blockProfile_on]
      exact plaquetteWeight_bounds hl f a.1
    · rw [blockProfile_off b _ _ H]
      norm_num
  let k := (q.1 t-p.1 t).valMinAbs.natAbs
  have sep : SupportsSeparated (blockProfile b (plaquetteWeight p)) (blockProfile b (plaquetteWeight q)) (b.val*k) := by
    apply supportsSeparated_of_axis hfine t
    intro e a he ha
    rw [periodicAxisDistance, blockedPlaquette_slice b t p hpi hpj e he,
      blockedPlaquette_slice b t q hqi hqj a ha]
    exact (blockCoordinate_distance b l (p.1 t) (q.1 t)).ge
  have variation (f : Face l) := (wilsonPlaquetteTrace_variation f).blockLinks b
    (fun e => (plaquetteWeight_bounds hl f e).1)
  have hsum : ∑ e, plaquetteWeight p e = 4 := by simp [plaquetteWeight, Finset.sum_add_distrib]; norm_num
  have H := wilson_spatial_clustering hfine hβ hwindow (B := 1) (by norm_num)
    (fun j => (bounds p j).1) (fun j => (bounds q j).1) (fun j => (bounds q j).2)
    (variation p) (variation q) _ sep
  rw [blockedCovariance_eq b β (wilsonPlaquetteTrace_variation p).continuous
    (wilsonPlaquetteTrace_variation q).continuous]
  rw [blockProfile_sum, hsum, pow_mul] at H
  convert H using 1
  dsimp [k]
  ring

/-- Converting the blocked exponential bound to physical time gives the
same inverse correlation length for a spacing R and a coarse spacing bR. -/
theorem block_physical_rate (b : ℕ+) (α R : ℝ) (hR : 0 < R) :
    -log (α^b.val) / (b.val * R) = -log α / R := by
  have hb : (0:ℝ) < b.val := by exact_mod_cast b.prop
  rw [log_pow]
  field_simp

#print axioms blockCoordinate_distance
#print axioms blockEdge_injective
#print axioms blockedPlaquette_gauge
#print axioms blockedWilsonLaw_integral
#print axioms LinkVariation.blockLinks
#print axioms blockedCovariance_eq
#print axioms blockedWilson_plaquette_clustering
#print axioms block_physical_rate
end
end YangMills.PeriodicWilson
