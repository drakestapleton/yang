-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaSlabs

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real
noncomputable section

/-- One element at each vertex, shared by all its incident links. -/
abbrev VertexGauge (l : ℕ+) := Site l → gaugeGroup.image

/-- Leave the first replica alone and gauge-transform the second, before any swaps. -/
def vertexReplica {l : ℕ+} (g : VertexGauge l) (z : WilsonReplicas l) : WilsonReplicas l :=
  (z.1, gaugeAct g z.2)

private theorem gaugeContinuous {l : ℕ+} (g : VertexGauge l) :
    Continuous (gaugeAct (l := l) g) := by
  apply continuous_pi; intro e
  change Continuous (fun U : WilsonConfig l => g e.1 * U e * (g (PinnedFrame.edgeEnd e))⁻¹)
  fun_prop

private theorem vertexContinuous {l : ℕ+} (g : VertexGauge l) : Continuous (vertexReplica g) :=
  continuous_fst.prodMk ((gaugeContinuous g).comp continuous_snd)

theorem vertexReplica_preserving {l : ℕ+} (β : ℝ) (g : VertexGauge l) :
    MeasurePreserving (vertexReplica g) (replicaLaw l β) (replicaLaw l β) := by
  let μ := wilsonLaw gaugeGroup l β su2Haar
  haveI : IsProbabilityMeasure μ := wilson_probability l β
  have hg : MeasurePreserving (gaugeAct g) μ μ :=
    ⟨(gaugeContinuous g).measurable, PhaseFour.wilsonLaw_map_gaugeAct β su2Haar g⟩
  exact (MeasurePreserving.id μ).prod hg

/-- Average a signed quantity over the list, counting repeated fields with multiplicity.
The list has no replica argument. An adaptive choice is not covered by the integral identity. -/
def vertexAverage {l : ℕ+} (gs : List (VertexGauge l)) (Q : WilsonReplicas l → ℝ)
    (z : WilsonReplicas l) : ℝ :=
  (∑ i : Fin gs.length, Q (vertexReplica gs[i] z)) / gs.length

theorem vertexAverage_abs_le {l : ℕ+} (gs : List (VertexGauge l)) (Q : WilsonReplicas l → ℝ)
    (z : WilsonReplicas l) : |vertexAverage gs Q z| ≤ vertexAverage gs (fun w => |Q w|) z := by
  rw [vertexAverage, vertexAverage, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ gs.length from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem vertexAverage_integral {l : ℕ+} (β : ℝ) (gs : List (VertexGauge l)) (hne : gs ≠ [])
    {D Q : WilsonReplicas l → ℝ} (cD : Continuous D) (cQ : Continuous Q)
    (fixed : ∀ g ∈ gs, ∀ z, D (vertexReplica g z) = D z) :
    (∫ z, D z * vertexAverage gs Q z ∂replicaLaw l β) = ∫ z, D z * Q z ∂replicaLaw l β := by
  let A := fun (i : Fin gs.length) z => D z * Q (vertexReplica gs[i] z)
  let I := ∫ z, D z * Q z ∂replicaLaw l β
  have eq (i : Fin gs.length) : (∫ z, A i z ∂replicaLaw l β) = I := by
    have hp := vertexReplica_preserving β gs[i]
    have c : Continuous (fun z => D z * Q z) := cD.mul cQ
    have h := integral_map hp.measurable.aemeasurable (c.aestronglyMeasurable
      (μ := (replicaLaw l β).map (vertexReplica gs[i])))
    rw [hp.map_eq] at h
    have hf (z : WilsonReplicas l) : D (vertexReplica gs[i] z) = D z :=
      fixed gs[i] (List.getElem_mem ..) z
    simpa only [A, I, hf] using h.symm
  have hi (i : Fin gs.length) : Integrable (A i) (replicaLaw l β) :=
    (cD.mul (cQ.comp (vertexContinuous gs[i]))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have factor (z : WilsonReplicas l) : D z * vertexAverage gs Q z = (∑ i, A i z) / gs.length := by
    rw [vertexAverage, mul_div_assoc', Finset.mul_sum]
  simp_rw [factor]; rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  have hn : (gs.length : ℝ) ≠ 0 := by
    have hnNat : gs.length ≠ 0 := fun hz => hne (List.length_eq_zero_iff.mp hz)
    exact_mod_cast hnNat
  simp [eq, hn, I]

theorem vertexAverage_bound {l : ℕ+} (β : ℝ) (gs : List (VertexGauge l)) (hne : gs ≠ [])
    {D Q : WilsonReplicas l → ℝ} (cD : Continuous D) (cQ : Continuous Q)
    (fixed : ∀ g ∈ gs, ∀ z, D (vertexReplica g z) = D z) :
    |∫ z, D z * Q z ∂replicaLaw l β| ≤ ∫ z, |D z| * |vertexAverage gs Q z| ∂replicaLaw l β := by
  rw [← vertexAverage_integral β gs hne cD cQ fixed]
  simpa only [abs_mul] using (abs_integral_le_integral_abs (μ := replicaLaw l β)
    (f := fun z => D z * vertexAverage gs Q z))

/-- The unframed *signed* shell product, not the product of shell magnitudes. -/
def signedSlabProduct {l : ℕ+} (β : ℝ) (t : Axis) (s : ZMod l.val) (k : ℕ) (z : WilsonReplicas l) : ℝ :=
  ∏ r ∈ Finset.range k, tanh (exchangeField β (slabMask t s r) z)

private theorem spatialFace_time {l : ℕ+} (p : Face l) (t : Axis)
    (hi : t ≠ p.2.val.1) (hj : t ≠ p.2.val.2) {e : Edge l} (he : e ∈ faceEdges p) : e.1 t = p.1 t := by
  simp only [faceEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · rfl
  · change (p.1 + Pi.single p.2.val.1 (1 : ZMod l.val) : Site l) t = _; simp [hi]
  · change (p.1 + Pi.single p.2.val.2 (1 : ZMod l.val) : Site l) t = _; simp [hj]
  · rfl

/-- For spatial plaquettes p and q, any k up to their cyclic separation gives the
exact covariance with k signed slab factors, averaged jointly in fixed vertex fields.
The bound takes the absolute value only *after* the signed average. -/
theorem plaquette_vertex_slab_covariance {l : ℕ+} (hl : 1 < l.val) (β : ℝ)
    (gs : List (VertexGauge l)) (hne : gs ≠ []) (p q : Face l) (t : Axis)
    (pi₁ : t ≠ p.2.val.1) (pi₂ : t ≠ p.2.val.2) (qi₁ : t ≠ q.2.val.1) (qi₂ : t ≠ q.2.val.2)
    (k : ℕ) (hk : k ≤ cyclicDistance (l := l) (p.1 t) (q.1 t)) :
    let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
    let Q := signedSlabProduct β t (p.1 t) k
    let C := wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
    2 * C = (∫ z, D z * vertexAverage gs Q z ∂replicaLaw l β) ∧
      |C| ≤ (∫ z, |D z| * |vertexAverage gs Q z| ∂replicaLaw l β) / 2 := by
  dsimp only
  let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
  let Q := signedSlabProduct β t (p.1 t) k
  have cp := (wilsonPlaquetteTrace_variation p).continuous
  have cq := (wilsonPlaquetteTrace_variation q).continuous
  have cD : Continuous D := ((cp.comp continuous_fst).sub (cp.comp continuous_snd)).mul
    ((cq.comp continuous_fst).sub (cq.comp continuous_snd))
  have cQ : Continuous Q := continuous_finsetProd _ fun r _ =>
    replica_tanh_continuous.comp (exchangeField_cont β (slabMask t (p.1 t) r))
  have fixed (g : VertexGauge l) (_ : g ∈ gs) (z : WilsonReplicas l) : D (vertexReplica g z) = D z := by
    simp [D, vertexReplica, replicaDifference, wilsonPlaquetteTrace_gauge_invariant]
  have anti (r : ℕ) (hr : r ∈ Finset.range k) (z : WilsonReplicas l) :
      D (exchangeLinks (slabMask t (p.1 t) r) z) = -D z := by
    let m := slabMask t (p.1 t) r
    have pIn (e : Edge l) (h : e ∈ faceEdges p) : m e = true := by
      simp [m, slabMask, spatialFace_time p t pi₁ pi₂ h, cyclicDistance]
    have qOut (e : Edge l) (h : e ∈ faceEdges q) : m e = false := by
      simpa [m, slabMask, spatialFace_time q t qi₁ qi₂ h] using (Finset.mem_range.mp hr).trans_le hk
    let S := exchangeLinks m z
    have p₁ : wilsonPlaquetteTrace p S.1 = wilsonPlaquetteTrace p z.2 :=
      trace_agrees p _ _ fun e h => by simp [S, exchangeLinks, pIn e h]
    have p₂ : wilsonPlaquetteTrace p S.2 = wilsonPlaquetteTrace p z.1 :=
      trace_agrees p _ _ fun e h => by simp [S, exchangeLinks, pIn e h]
    have q₁ : wilsonPlaquetteTrace q S.1 = wilsonPlaquetteTrace q z.1 :=
      trace_agrees q _ _ fun e h => by simp [S, exchangeLinks, qOut e h]
    have q₂ : wilsonPlaquetteTrace q S.2 = wilsonPlaquetteTrace q z.2 :=
      trace_agrees q _ _ fun e h => by simp [S, exchangeLinks, qOut e h]
    change (wilsonPlaquetteTrace p S.1 - wilsonPlaquetteTrace p S.2) *
      (wilsonPlaquetteTrace q S.1 - wilsonPlaquetteTrace q S.2) = -(_ * _)
    rw [p₁, p₂, q₁, q₂]; ring
  have eq : 2 * wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) =
      ∫ z, D z * Q z ∂replicaLaw l β := (twice_wilsonCovariance β cp cq).trans
    (replica_shell_identity β _ _ cD anti fun _ _ _ _ hij a => slab_boundaries_disjoint hl _ _ hij a)
  refine ⟨eq.trans (vertexAverage_integral β gs hne cD cQ fixed).symm, ?_⟩
  have H := vertexAverage_bound β gs hne cD cQ fixed
  rw [← eq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H
  change _ ≤ (∫ z, |D z| * |vertexAverage gs Q z| ∂replicaLaw l β) / 2
  linarith only [H]

#print axioms vertexReplica_preserving
#print axioms vertexAverage_abs_le
#print axioms vertexAverage_integral
#print axioms vertexAverage_bound
#print axioms plaquette_vertex_slab_covariance
end
end YangMills.PeriodicWilson
