-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaVertex
import Mathlib.MeasureTheory.Integral.Prod

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real
noncomputable section

/- The parameter law has no configuration argument: it is independent of the Wilson pair.
Compactness and continuity supply joint integrability, rather than assuming a Fubini step. -/
variable {A : Type*} [TopologicalSpace A] [CompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

/-- Signed averaging; the absolute value must be applied after this integral. -/
def vertexIntegral {l : ℕ+} (ν : Measure A) (g : A → VertexGauge l)
    (Q : WilsonReplicas l → ℝ) (z : WilsonReplicas l) : ℝ :=
  ∫ a, Q (vertexReplica (g a) z) ∂ν

omit [CompactSpace A] [MeasurableSpace A] [BorelSpace A] in
private theorem familyReplica_continuous {l : ℕ+} {g : A → VertexGauge l}
    (cg : Continuous g) :
    Continuous (fun w : A × WilsonReplicas l => vertexReplica (g w.1) w.2) := by
  apply Continuous.prodMk (continuous_fst.comp continuous_snd)
  apply continuous_pi; intro e
  change Continuous (fun w : A × WilsonReplicas l =>
    g w.1 e.1 * w.2.2 e * (g w.1 (PinnedFrame.edgeEnd e))⁻¹)
  fun_prop

/-- Fubini for an independent probability on any compact continuous family of gauges.
The endpoint factor is invariant for every field in that family. -/
theorem vertexIntegral_integral {l : ℕ+} (β : ℝ) (ν : Measure A)
    [IsProbabilityMeasure ν] {g : A → VertexGauge l} (cg : Continuous g)
    {D Q : WilsonReplicas l → ℝ} (cD : Continuous D) (cQ : Continuous Q)
    (fixed : ∀ a z, D (vertexReplica (g a) z) = D z) :
    (∫ z, D z * vertexIntegral ν g Q z ∂replicaLaw l β) =
      ∫ z, D z * Q z ∂replicaLaw l β := by
  let f := fun (a : A) (z : WilsonReplicas l) => D z * Q (vertexReplica (g a) z)
  have cf : Continuous (Function.uncurry f) :=
    (cD.comp continuous_snd).mul (cQ.comp (familyReplica_continuous cg))
  have hf : Integrable (Function.uncurry f) (ν.prod (replicaLaw l β)) :=
    cf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have eq (a : A) : (∫ z, f a z ∂replicaLaw l β) = ∫ z, D z * Q z ∂replicaLaw l β := by
    have hp := vertexReplica_preserving β (g a)
    have c : Continuous (fun z => D z * Q z) := cD.mul cQ
    have h := integral_map hp.measurable.aemeasurable
      (c.aestronglyMeasurable (μ := (replicaLaw l β).map (vertexReplica (g a))))
    rw [hp.map_eq] at h
    simpa only [f, fixed a] using h.symm
  calc
    _ = ∫ z, ∫ a, f a z ∂ν ∂replicaLaw l β := by
      simp only [vertexIntegral, f, integral_const_mul]
    _ = ∫ a, ∫ z, f a z ∂replicaLaw l β ∂ν :=
      (integral_integral_swap hf).symm
    _ = _ := by simp only [eq, integral_const, probReal_univ, one_smul]

/-- Cancellation is retained inside the absolute value, including between gauge draws. -/
theorem vertexIntegral_bound {l : ℕ+} (β : ℝ) (ν : Measure A)
    [IsProbabilityMeasure ν] {g : A → VertexGauge l} (cg : Continuous g)
    {D Q : WilsonReplicas l → ℝ} (cD : Continuous D) (cQ : Continuous Q)
    (fixed : ∀ a z, D (vertexReplica (g a) z) = D z) :
    |∫ z, D z * Q z ∂replicaLaw l β| ≤
      ∫ z, |D z| * |vertexIntegral ν g Q z| ∂replicaLaw l β := by
  rw [← vertexIntegral_integral β ν cg cD cQ fixed]
  simpa only [abs_mul] using (abs_integral_le_integral_abs (μ := replicaLaw l β)
    (f := fun z => D z * vertexIntegral ν g Q z))

/-- Concrete signed slab specialization, reusing the proved fixed-field slab identity. -/
theorem plaquette_probability_slab_covariance {l : ℕ+} (hl : 1 < l.val) (β : ℝ)
    (ν : Measure A) [IsProbabilityMeasure ν] {g : A → VertexGauge l} (cg : Continuous g)
    (p q : Face l) (t : Axis)
    (pi₁ : t ≠ p.2.val.1) (pi₂ : t ≠ p.2.val.2)
    (qi₁ : t ≠ q.2.val.1) (qi₂ : t ≠ q.2.val.2)
    (k : ℕ) (hk : k ≤ cyclicDistance (l := l) (p.1 t) (q.1 t)) :
    let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
    let Q := signedSlabProduct β t (p.1 t) k
    let C := wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
    2 * C = (∫ z, D z * vertexIntegral ν g Q z ∂replicaLaw l β) ∧
      |C| ≤ (∫ z, |D z| * |vertexIntegral ν g Q z| ∂replicaLaw l β) / 2 := by
  dsimp only
  let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
  let Q := signedSlabProduct β t (p.1 t) k
  have cp := (wilsonPlaquetteTrace_variation p).continuous
  have cq := (wilsonPlaquetteTrace_variation q).continuous
  have cD : Continuous D := ((cp.comp continuous_fst).sub (cp.comp continuous_snd)).mul
    ((cq.comp continuous_fst).sub (cq.comp continuous_snd))
  have cQ : Continuous Q := continuous_finsetProd _ fun r _ =>
    replica_tanh_continuous.comp (exchangeField_cont β (slabMask t (p.1 t) r))
  have fixed (a : A) (z : WilsonReplicas l) : D (vertexReplica (g a) z) = D z := by
    simp [D, vertexReplica, replicaDifference, wilsonPlaquetteTrace_gauge_invariant]
  have base := (plaquette_vertex_slab_covariance hl β [1] (by simp) p q t
    pi₁ pi₂ qi₁ qi₂ k hk).1
  have ident (z : WilsonReplicas l) : vertexReplica (1 : VertexGauge l) z = z := by
    ext e <;> simp [vertexReplica, gaugeAct]
  have eq : 2 * wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) =
      ∫ z, D z * Q z ∂replicaLaw l β := by
    simpa [vertexAverage, ident, D, Q] using base
  refine ⟨eq.trans (vertexIntegral_integral β ν cg cD cQ fixed).symm, ?_⟩
  have H := vertexIntegral_bound β ν cg cD cQ fixed
  rw [← eq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H
  change _ ≤ (∫ z, |D z| * |vertexIntegral ν g Q z| ∂replicaLaw l β) / 2
  linarith only [H]

/-- Independent normalized Haar at each selected vertex; no weights depend on the pair. -/
def boundaryHaar {l : ℕ+} (B : Finset (Site l)) : Measure (B → gaugeGroup.image) :=
  Measure.pi fun _ => su2Haar

instance boundaryHaar_probability {l : ℕ+} (B : Finset (Site l)) :
    IsProbabilityMeasure (boundaryHaar B) := by
  unfold boundaryHaar
  infer_instance

/-- Extend the boundary field by the identity, sharing one gauge at all incident links. -/
def boundaryField {l : ℕ+} (B : Finset (Site l)) (a : B → gaugeGroup.image) : VertexGauge l :=
  fun v => if h : v ∈ B then a ⟨v, h⟩ else 1

theorem boundaryField_off {l : ℕ+} (B : Finset (Site l)) (a : B → gaugeGroup.image)
    {v : Site l} (hv : v ∉ B) : boundaryField B a v = 1 := by
  simp [boundaryField, hv]

theorem boundaryField_continuous {l : ℕ+} (B : Finset (Site l)) : Continuous (boundaryField B) := by
  apply continuous_pi; intro v
  by_cases h : v ∈ B
  · simpa only [boundaryField, dif_pos h] using (continuous_apply (⟨v, h⟩ : B))
  · simpa only [boundaryField, dif_neg h] using
      (continuous_const : Continuous (fun _ : B → gaugeGroup.image => (1 : gaugeGroup.image)))

/-- The two top sheets of the radius-r slab boundary (the sampler's positive time direction).
For side four, source time zero and r=1, these are times two and three. -/
def outerTopSheets {l : ℕ+} (t : Axis) (s : ZMod l.val) (r : ℕ) : Finset (Site l) :=
  Finset.univ.filter fun v => v t = s + (r : ZMod l.val) + 1 ∨ v t = s - (r : ZMod l.val)

/-- Exact identification with the sampler's two outer top sheets at periodic side four. -/
theorem mem_outerTopSheets_four (t : Axis) (v : Site (⟨4, by decide⟩ : ℕ+)) :
    v ∈ outerTopSheets t 0 1 ↔ v t = 2 ∨ v t = 3 := by
  simp only [outerTopSheets, Finset.mem_filter, Finset.mem_univ, true_and]
  change (v t = (0 + 1 + 1 : ZMod 4) ∨ v t = (0 - 1 : ZMod 4)) ↔ _
  have a : (0 + 1 + 1 : ZMod 4) = 2 := by decide
  have b : (0 - 1 : ZMod 4) = 3 := by decide
  rw [a, b]
  rfl

/-- In particular, use B=outerTopSheets t s 1 for the two outer sheets.
This theorem is about the unframed SU(2) Wilson measure, not an adaptive optimizer,
a finite-draw error estimate, a U(1) theorem, or a continuum/mass-gap statement. -/
theorem plaquette_boundaryHaar_slab_covariance {l : ℕ+} (hl : 1 < l.val) (β : ℝ)
    (B : Finset (Site l)) (p q : Face l) (t : Axis)
    (pi₁ : t ≠ p.2.val.1) (pi₂ : t ≠ p.2.val.2)
    (qi₁ : t ≠ q.2.val.1) (qi₂ : t ≠ q.2.val.2)
    (k : ℕ) (hk : k ≤ cyclicDistance (l := l) (p.1 t) (q.1 t)) :
    let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
    let Q := signedSlabProduct β t (p.1 t) k
    let C := wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
    2 * C = (∫ z, D z * vertexIntegral (boundaryHaar B) (boundaryField B) Q z ∂replicaLaw l β) ∧
      |C| ≤ (∫ z, |D z| * |vertexIntegral (boundaryHaar B) (boundaryField B) Q z|
        ∂replicaLaw l β) / 2 :=
  plaquette_probability_slab_covariance hl β (boundaryHaar B) (boundaryField_continuous B)
    p q t pi₁ pi₂ qi₁ qi₂ k hk

#print axioms vertexIntegral_integral
#print axioms vertexIntegral_bound
#print axioms plaquette_probability_slab_covariance
#print axioms boundaryHaar_probability
#print axioms boundaryField_off
#print axioms boundaryField_continuous
#print axioms mem_outerTopSheets_four
#print axioms plaquette_boundaryHaar_slab_covariance
end
end YangMills.PeriodicWilson
