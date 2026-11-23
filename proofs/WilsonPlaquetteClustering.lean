-- SPDX-License-Identifier: Apache-2.0
import WilsonSpatialClustering

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer Real
noncomputable section
private abbrev G := gaugeGroup.image
private abbrev Config (l : ℕ+) := Configuration gaugeGroup l

/-- Half the real trace of the fundamental Wilson plaquette. -/
def wilsonPlaquetteTrace {l : ℕ+} (p : Face l) (U : Config l) : ℝ :=
  (suMat (plaquette U p.1 p.2.val.1 p.2.val.2)).trace.re / 2

theorem wilsonPlaquetteTrace_gauge_invariant {l : ℕ+} (p : Face l) (Ω : Site l → G) (U : Config l) :
    wilsonPlaquetteTrace p (gaugeAct Ω U) = wilsonPlaquetteTrace p U := by
  simp only [wilsonPlaquetteTrace,plaquette_gauge_covariant,scalar_trace,scalar_conjugate]

private def weight {l : ℕ+} (p : Face l) (e : Edge l) : ℝ :=
  (if e = (corners p).1 then 1 else 0) + (if e = (corners p).2.1 then 1 else 0) +
  (if e = (corners p).2.2.1 then 1 else 0) + (if e = (corners p).2.2.2 then 1 else 0)

private theorem edge_weights {l : ℕ+} (hl : 1 < l.val) (p : Face l) (e : Edge l) :
    0 ≤ weight p e ∧ weight p e ≤ 1 := by
  have h := corners_distinct hl p
  unfold weight
  generalize corners p = Q at *
  obtain ⟨a,b,c,d⟩ := Q
  dsimp only at *
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := h
  by_cases ha : e=a <;> by_cases hb : e=b <;> by_cases hc : e=c <;> by_cases hd : e=d <;> simp_all

private theorem product_distance (u v w z : G) :
    linkGeodesic (u*w) (v*z) ≤ linkGeodesic u v + linkGeodesic w z := by
  simpa only [linkGeodesic_mul_right,linkGeodesic_mul_left] using geo_triangle (u*w) (v*w) (v*z)

private theorem trace_variation {l : ℕ+} (p : Face l) :
    LinkVariation (weight p) (wilsonPlaquetteTrace p) := by
  intro U V
  let hol := fun W : Config l => plaquette W p.1 p.2.val.1 p.2.val.2
  have htrace (W : Config l) : wilsonPlaquetteTrace p W = cos (polarAngle (hol W)) := by
    rw [wilsonPlaquetteTrace,scalar_trace,cos_polarAngle]; dsimp [hol]; ring
  rw [htrace,htrace]
  apply (abs_cos_sub_cos_le ..).trans
  have angle (u : G) : polarAngle u = linkGeodesic u 1 := by simp [linkGeodesic]
  rw [angle,angle]
  have hang : |linkGeodesic (hol U) 1 - linkGeodesic (hol V) 1| ≤ linkGeodesic (hol U) (hol V) := by
    have h1 := geo_triangle (hol U) (hol V) 1
    have h2 := geo_triangle (hol V) (hol U) 1
    have hs : linkGeodesic (hol V) (hol U) = linkGeodesic (hol U) (hol V) := by
      simp only [linkGeodesic_eq_angle]; exact InnerProductGeometry.angle_comm ..
    rw [abs_le]; constructor <;> linarith
  apply hang.trans
  let a := (corners p).1
  let b := (corners p).2.1
  let c := (corners p).2.2.1
  let d := (corners p).2.2.2
  have hh : linkGeodesic (hol U) (hol V) ≤ linkGeodesic (U a) (V a) +
      (linkGeodesic (U b) (V b) + (linkGeodesic (U c) (V c) + linkGeodesic (U d) (V d))) := by
    apply (product_distance (U a) (V a) _ _).trans (add_le_add_right ?_ _)
    apply (product_distance (U b) (V b) _ _).trans (add_le_add_right ?_ _)
    change linkGeodesic ((U c)⁻¹*(U d)⁻¹) ((V c)⁻¹*(V d)⁻¹) ≤ _
    simpa only [pole_inverse_distance] using product_distance (U c)⁻¹ (V c)⁻¹ (U d)⁻¹ (V d)⁻¹
  apply hh.trans_eq
  simp only [weight,add_mul,ite_mul,one_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    a,b,c,d,add_assoc]

private theorem slice_support {l : ℕ+} (t : Axis) {p : Face l} (hi : t ≠ p.2.val.1) (hj : t ≠ p.2.val.2)
    {e : Edge l} (he : weight p e ≠ 0) : e.1 t = p.1 t := by
  by_cases h1 : e = (corners p).1
  · rw [h1]; rfl
  by_cases h2 : e = (corners p).2.1
  · rw [h2]; change (p.1 + Pi.single p.2.val.1 (1 : ZMod l.val) : Site l) t = p.1 t
    simp [hi]
  by_cases h3 : e = (corners p).2.2.1
  · rw [h3]; change (p.1 + Pi.single p.2.val.2 (1 : ZMod l.val) : Site l) t = p.1 t
    simp [hj]
  by_cases h4 : e = (corners p).2.2.2
  · rw [h4]; rfl
  simp [weight,h1,h2,h3,h4] at he

/-- Gauge-invariant spatial Wilson plaquette traces in two time slices
have exponentially decaying connected correlation, uniformly in lattice side.
The cyclic separation also accounts for the route through the periodic seam. -/
theorem wilson_plaquette_slice_clustering {l : ℕ+} (hl : 1 < l.val) {β : ℝ}
    (hβ : 0 ≤ β) (hwindow : β < sqrt 3/18) (t : Axis) (p q : Face l)
    (hpi : t ≠ p.2.val.1) (hpj : t ≠ p.2.val.2) (hqi : t ≠ q.2.val.1) (hqj : t ≠ q.2.val.2) :
    |wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)| ≤
      (4*π^2/(1-straightRow β))*(straightRow β)^((q.1 t-p.1 t).valMinAbs.natAbs) := by
  let k := (q.1 t-p.1 t).valMinAbs.natAbs
  have sep : SupportsSeparated (weight p) (weight q) k := by
    apply supportsSeparated_of_axis hl t
    intro e a he ha
    simp [periodicAxisDistance,k,slice_support t hpi hpj he,slice_support t hqi hqj ha]
  have hsum : ∑ e, weight p e = 4 := by simp [weight,Finset.sum_add_distrib]; norm_num
  have hb := wilson_spatial_clustering hl hβ hwindow (B := 1) (by norm_num)
    (fun e => (edge_weights hl p e).1) (fun e => (edge_weights hl q e).1) (fun e => (edge_weights hl q e).2)
    (trace_variation p) (trace_variation q) k sep
  simpa only [hsum,mul_one,mul_comm (π^2) 4] using hb

#print axioms wilsonPlaquetteTrace_gauge_invariant
#print axioms wilson_plaquette_slice_clustering
end
end YangMills.PeriodicWilson
