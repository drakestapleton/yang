-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaFrame

namespace YangMills.PeriodicWilson
open FundamentalSU2 MeasureTheory Real
noncomputable section

def cyclicDistance {l : ℕ+} (s v : ZMod l.val) : ℕ := (v-s).valMinAbs.natAbs

/-- The swap acts on every link based within r cyclic time steps of s. -/
def slabMask {l : ℕ+} (t : Axis) (s : ZMod l.val) (r : ℕ) (e : Edge l) : Bool :=
  decide (cyclicDistance (l := l) s (e.1 t) ≤ r)

private theorem distance_step {l : ℕ+} (hl : 1 < l.val) (s v : ZMod l.val) :
    cyclicDistance (l := l) s (v+1) ≤ cyclicDistance (l := l) s v + 1 ∧
    cyclicDistance (l := l) s v ≤ cyclicDistance (l := l) s (v+1) + 1 := by
  have ho : (1 : ZMod l.val).valMinAbs.natAbs = 1 := by
    rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_one'' (by omega)]
    omega
  constructor
  · unfold cyclicDistance
    rw [show v+1-s = (v-s)+1 by abel]
    exact ((ZMod.natAbs_valMinAbs_add_le ..).trans (Int.natAbs_add_le ..)).trans_eq (by rw [ho])
  · unfold cyclicDistance
    conv_lhs => rw [show v-s = (v+1-s)+(-1) by abel]
    exact ((ZMod.natAbs_valMinAbs_add_le ..).trans (Int.natAbs_add_le ..)).trans_eq
      (by rw [ZMod.natAbs_valMinAbs_neg,ho])

theorem face_base_times {l : ℕ+} (p : Face l) (t : Axis) {e : Edge l} (he : e ∈ faceEdges p) :
    e.1 t = p.1 t ∨ e.1 t = p.1 t+1 := by
  simp only [faceEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · change (p.1 + Pi.single p.2.val.1 (1:ZMod l.val) : Site l) t = p.1 t ∨
      (p.1 + Pi.single p.2.val.1 (1:ZMod l.val) : Site l) t = p.1 t+1
    by_cases h : t=p.2.val.1 <;> simp [h]
  · change (p.1 + Pi.single p.2.val.2 (1:ZMod l.val) : Site l) t = p.1 t ∨
      (p.1 + Pi.single p.2.val.2 (1:ZMod l.val) : Site l) t = p.1 t+1
    by_cases h : t=p.2.val.2 <;> simp [h]
  · exact .inl rfl

theorem slab_boundaries_disjoint {l : ℕ+} (hl : 1 < l.val) (t : Axis) (s : ZMod l.val)
    {i j : ℕ} (hij : i ≠ j) (p : Face l) : uniformOnFace (slabMask t s i) p ∨ uniformOnFace (slabMask t s j) p := by
  let d := cyclicDistance (l := l) s (p.1 t)
  let d' := cyclicDistance (l := l) s (p.1 t+1)
  have hc (r : ℕ) (h : d ≤ r ↔ d' ≤ r) : uniformOnFace (slabMask t s r) p := by
    refine ⟨decide (d ≤ r), fun e he => ?_⟩
    rcases face_base_times p t he with hx | hx
    · simp [slabMask,hx,d]
    · simp [slabMask,hx,d',Bool.decide_congr h.symm]
  have hh : d' ≤ d+1 ∧ d ≤ d'+1 := distance_step hl s (p.1 t)
  by_cases h : d ≤ i ↔ d' ≤ i
  · exact .inl (hc i h)
  · exact .inr (hc j (by omega))

def spatialSlice {l : ℕ+} (t : Axis) (s : ZMod l.val) (ps : List (Face l)) : Prop :=
  ∀ p ∈ ps, p.1 t = s ∧ t ≠ p.2.val.1 ∧ t ≠ p.2.val.2

private theorem blocked_trace_local {l : ℕ+} (hl : 1 < l.val) (b : ℕ+) (p : Face l) (t : Axis)
    (hi : t ≠ p.2.val.1) (hj : t ≠ p.2.val.2) (U V : WilsonConfig (b*l))
    (he : ∀ e : Edge (b*l), e.1 t = blockCoordinate b l (p.1 t) → U e = V e) :
    wilsonPlaquetteTrace p (blockLinks b U) = wilsonPlaquetteTrace p (blockLinks b V) := by
  have H := (wilsonPlaquetteTrace_variation p).blockLinks b (fun e => (plaquetteWeight_bounds hl p e).1) U V
  have hz (e : Edge (b*l)) : blockProfile b (plaquetteWeight p) e * linkGeodesic (U e) (V e) = 0 := by
    by_cases h : blockProfile b (plaquetteWeight p) e = 0
    · rw [h,zero_mul]
    · rw [he e (blockedPlaquette_slice b t p hi hj e h), linkGeodesic_eq_angle, InnerProductGeometry.angle_self, mul_zero]
      exact norm_ne_zero_iff.mp (by rw [coordinates_norm]; norm_num)
  simp only [hz,Finset.sum_const_zero,abs_nonpos_iff,sub_eq_zero,Function.comp_apply] at H
  exact H

private theorem blocked_product_local {l : ℕ+} (hl : 1 < l.val) (b : ℕ+) (ps : List (Face l)) (t : Axis)
    (s : ZMod l.val) (hs : spatialSlice t s ps) (U V : WilsonConfig (b*l))
    (he : ∀ e : Edge (b*l), e.1 t = blockCoordinate b l s → U e = V e) :
    plaquetteProduct ps (blockLinks b U) = plaquetteProduct ps (blockLinks b V) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨hp,hi,hj⟩ := hs p (List.mem_cons_self ..)
    rw [plaquetteProduct, plaquetteProduct, blocked_trace_local hl b p t hi hj U V (fun e h => he e (hp ▸ h)),
      ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))]

/-- The effective attenuation at separation k is an expectation of a product
under the *fine* Wilson law at its actual beta. No shell independence is required. -/
def slabMoment {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ)
    (ν : Measure (WilsonReplicas l) := replicaLaw l β) :=
  ∫ z, ∏ r ∈ Finset.range k, |tanh (exchangeField β (slabMask t s r) z)| ∂ν

private theorem blocked_shell_anti {l : ℕ+} (hl : 1 < l.val) (b : ℕ+)
    (t : Axis) (s u : ZMod l.val) (ps qs : List (Face l))
    (hp : spatialSlice t s ps) (hq : spatialSlice t u qs) :
    ∀ r ∈ Finset.range (b.val * cyclicDistance (l := l) s u), ∀ z,
      replicaDifference (plaquetteProduct ps ∘ blockLinks b) (plaquetteProduct qs ∘ blockLinks b)
        (exchangeLinks (slabMask t (blockCoordinate b l s) r) z) =
      -replicaDifference (plaquetteProduct ps ∘ blockLinks b) (plaquetteProduct qs ∘ blockLinks b) z := by
  let s' := blockCoordinate b l s
  let F := plaquetteProduct ps ∘ (blockLinks b : WilsonConfig (b*l) → WilsonConfig l)
  let G := plaquetteProduct qs ∘ (blockLinks b : WilsonConfig (b*l) → WilsonConfig l)
  intro r hr z
  have hru : r < cyclicDistance (l := b*l) s' (blockCoordinate b l u) := by
    rw [cyclicDistance,blockCoordinate_distance]; exact Finset.mem_range.mp hr
  let S := exchangeLinks (slabMask t s' r) z
  have at_s (e : Edge (b*l)) (he : e.1 t = blockCoordinate b l s) : slabMask t s' r e = true := by
    simp only [slabMask,cyclicDistance,he,s',sub_self,ZMod.valMinAbs_zero,Int.natAbs_zero,Nat.zero_le,decide_true]
  have at_u (e : Edge (b*l)) (he : e.1 t = blockCoordinate b l u) : slabMask t s' r e = false := by
    simpa [slabMask,he] using hru
  have f₁ : F S.1 = F z.2 := blocked_product_local hl b ps t s hp _ _ fun e he => by simp [S,exchangeLinks,at_s e he]
  have f₂ : F S.2 = F z.1 := blocked_product_local hl b ps t s hp _ _ fun e he => by simp [S,exchangeLinks,at_s e he]
  have g₁ : G S.1 = G z.1 := blocked_product_local hl b qs t u hq _ _ fun e he => by simp [S,exchangeLinks,at_u e he]
  have g₂ : G S.2 = G z.2 := blocked_product_local hl b qs t u hq _ _ fun e he => by simp [S,exchangeLinks,at_u e he]
  change (F S.1-F S.2)*(G S.1-G S.2) = -((F z.1-F z.2)*(G z.1-G z.2))
  rw [f₁,f₂,g₁,g₂]; ring

/-- All-beta, finite-volume correlation estimate for the actual blocked
Wilson products. Each fine shell between the two slices supplies one factor. -/
theorem blockedProduct_replica_bound {l : ℕ+} (hl : 1 < l.val) (b : ℕ+) (β : ℝ)
    (t : Axis) (s u : ZMod l.val) (ps qs : List (Face l))
    (hp : spatialSlice t s ps) (hq : spatialSlice t u qs) :
    |blockedCovariance b β (plaquetteProduct ps) (plaquetteProduct qs)| ≤
      2*slabMoment β t (blockCoordinate b l s) (b.val*cyclicDistance (l := l) s u) := by
  let s' := blockCoordinate b l s
  let k := b.val * cyclicDistance (l := l) s u
  rw [blockedCovariance_eq b β (plaquetteProduct_continuous ps) (plaquetteProduct_continuous qs)]
  apply replica_covariance_bound β (Finset.range k) (slabMask t s')
    ((plaquetteProduct_continuous ps).comp (blockLinks_continuous b l))
    ((plaquetteProduct_continuous qs).comp (blockLinks_continuous b l))
    (fun U => plaquetteProduct_abs_le_one ps _) (fun U => plaquetteProduct_abs_le_one qs _)
  · exact blocked_shell_anti hl b t s u ps qs hp hq
  · exact fun _ _ _ _ hij p => slab_boundaries_disjoint (hl.trans_le (Nat.le_mul_of_pos_left _ b.prop)) _ _ hij p

/-- The same blocked-product estimate with all exchanges evaluated in a pinned frame. -/
theorem framed_blockedProduct_replica_bound {l : ℕ+} (hl : 1 < l.val) (b : ℕ+) (β : ℝ) (P : PinnedFrame (b*l))
    (t : Axis) (s u : ZMod l.val) (ps qs : List (Face l))
    (hp : spatialSlice t s ps) (hq : spatialSlice t u qs) :
    |blockedCovariance b β (plaquetteProduct ps) (plaquetteProduct qs)| ≤
      2*slabMoment β t (blockCoordinate b l s) (b.val*cyclicDistance (l := l) s u) (P.framedLaw β) := by
  let F := plaquetteProduct ps ∘ (blockLinks b : WilsonConfig (b*l) → WilsonConfig l)
  let H := plaquetteProduct qs ∘ (blockLinks b : WilsonConfig (b*l) → WilsonConfig l)
  let D := replicaDifference F H
  have cF : Continuous F := (plaquetteProduct_continuous ps).comp (blockLinks_continuous b l)
  have cH : Continuous H := (plaquetteProduct_continuous qs).comp (blockLinks_continuous b l)
  have cD : Continuous D := ((cF.comp continuous_fst).sub (cF.comp continuous_snd)).mul ((cH.comp continuous_fst).sub (cH.comp continuous_snd))
  have hg (z : WilsonReplicas (b*l)) : D (P.pair z) = D z := by
    simp [D,F,H,replicaDifference,PinnedFrame.pair,PinnedFrame.project,blockLinks_gauge b hl,plaquetteProduct_gauge]
  rw [blockedCovariance_eq b β (plaquetteProduct_continuous ps) (plaquetteProduct_continuous qs)]
  apply replica_covariance_bound_of_integral β (P.framedLaw β) _ _ cF cH
    (fun U => plaquetteProduct_abs_le_one ps _) (fun U => plaquetteProduct_abs_le_one qs _)
  rw [twice_wilsonCovariance β cF cH, ← P.integral_projected β cD hg]
  exact shell_identity_of_exchange β _ (P.framed_exchange β) _ _ cD (blocked_shell_anti hl b t s u ps qs hp hq)
    fun _ _ _ _ hij p => slab_boundaries_disjoint (hl.trans_le (Nat.le_mul_of_pos_left _ b.prop)) _ _ hij p

#print axioms framed_blockedProduct_replica_bound
#print axioms slab_boundaries_disjoint
#print axioms blockedProduct_replica_bound
end
end YangMills.PeriodicWilson
