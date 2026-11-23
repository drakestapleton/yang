-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaFrame

namespace YangMills.PeriodicWilson.PinnedFrame
open FundamentalSU2 WilsonPolymer MeasureTheory Real
noncomputable section
variable {l : ℕ+} (P : PinnedFrame l)

/-- Both replicas are in the fixed frame on the pinned links. -/
def IsPinned (z : WilsonReplicas l) : Prop :=
  ∀ e ∈ P.edges, z.1 e = 1 ∧ z.2 e = 1

/-- Labels on pinned links are not part of a face's exchange geometry. -/
def freeFace (p : Face l) := faceEdges p \ P.edges

def freeUniform (m : Edge l → Bool) (p : Face l) : Prop :=
  ∃ b : Bool, ∀ e ∈ P.freeFace p, m e = b

/-- The discrete boundary used by a fixed-geometry cut certificate. -/
def freeBoundary (m : Edge l → Bool) : Finset (Face l) := by
  classical
  exact Finset.univ.filter fun p => ¬P.freeUniform m p

theorem freeBoundary_disjoint (m n : Edge l → Bool) :
    Disjoint (P.freeBoundary m) (P.freeBoundary n) ↔
      ∀ p : Face l, P.freeUniform m p ∨ P.freeUniform n p := by
  classical
  simp only [Finset.disjoint_left, freeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h p
    by_cases hp : P.freeUniform m p
    · exact Or.inl hp
    · exact Or.inr (not_not.mp (h hp))
  · intro h p hp hn
    exact (h p).elim hp hn

/-- Separated free supports supply the endpoint labels without requiring that
the full plaquette supports, which may share pinned links, be disjoint. -/
theorem free_anchor_labels (p q : Face l) (pq : Disjoint (P.freeFace p) (P.freeFace q)) :
    (∀ e ∈ P.freeFace p, decide (e ∈ P.freeFace p) = true) ∧
    (∀ e ∈ P.freeFace q, decide (e ∈ P.freeFace p) = false) := by
  constructor
  · intro e he; simp [he]
  · intro e he; simp [Finset.disjoint_left.mp pq.symm he]

private theorem pinned_pair (z : WilsonReplicas l) : P.IsPinned (P.pair z) :=
  fun e he => ⟨P.pins z.1 ⟨e,he⟩, P.pins z.2 ⟨e,he⟩⟩

private theorem pinned_exchange {z : WilsonReplicas l} (hz : P.IsPinned z) (m : Edge l → Bool) :
    P.IsPinned (exchangeLinks m z) := by
  intro e he
  cases h : m e <;> simp [exchangeLinks, h, (hz e he).1, (hz e he).2]

/-- Changing labels on pins leaves the actual exchange unchanged. -/
theorem exchange_eq_on_free (m n : Edge l → Bool)
    (hmn : ∀ e, e ∉ P.edges → m e = n e) {z : WilsonReplicas l} (hz : P.IsPinned z) :
    exchangeLinks m z = exchangeLinks n z := by
  apply Prod.ext <;> funext e <;> by_cases he : e ∈ P.edges
  all_goals first
    | simp [exchangeLinks, (hz e he).1, (hz e he).2]
    | simp [exchangeLinks, hmn e he]

/-- A retraction onto pinned pairs, not a second gauge transformation. -/
private def retractPair (z : WilsonReplicas l) : WilsonReplicas l :=
  (fun e => if e ∈ P.edges then 1 else z.1 e, fun e => if e ∈ P.edges then 1 else z.2 e)

private theorem retract_cont : Continuous P.retractPair := by
  apply Continuous.prodMk <;> apply continuous_pi <;> intro e <;>
    by_cases he : e ∈ P.edges <;> simp only [he, if_true, if_false] <;> fun_prop

private theorem retract_pinned (z : WilsonReplicas l) : P.IsPinned (P.retractPair z) := by
  intro e he; simp [retractPair, he]

private theorem retract_fixed {z : WilsonReplicas l} (hz : P.IsPinned z) : P.retractPair z = z := by
  apply Prod.ext
  · funext e
    by_cases he : e ∈ P.edges
    · exact (if_pos he).trans (hz e he).1.symm
    · exact if_neg he
  · funext e
    by_cases he : e ∈ P.edges
    · exact (if_pos he).trans (hz e he).2.symm
    · exact if_neg he

private theorem retract_exchange (m : Edge l → Bool) (z : WilsonReplicas l) :
    P.retractPair (exchangeLinks m z) = exchangeLinks m (P.retractPair z) := by
  apply Prod.ext <;> funext e <;> by_cases he : e ∈ P.edges <;> cases hm : m e <;>
    simp [retractPair, exchangeLinks, he, hm]

private theorem trace_free (p : Face l) (m : Edge l → Bool) (b : Bool)
    (hm : ∀ e ∈ P.freeFace p, m e = b) {z : WilsonReplicas l} (hz : P.IsPinned z) :
    wilsonPlaquetteTrace p (exchangeLinks m z).1 = wilsonPlaquetteTrace p (if b then z.2 else z.1) ∧
    wilsonPlaquetteTrace p (exchangeLinks m z).2 = wilsonPlaquetteTrace p (if b then z.1 else z.2) := by
  constructor <;> apply trace_agrees <;> intro e he <;> by_cases hp : e ∈ P.edges
  all_goals first
    | cases b <;> simp [exchangeLinks, (hz e hp).1, (hz e hp).2]
    | cases b <;> simp [exchangeLinks, hm e (Finset.mem_sdiff.mpr ⟨he,hp⟩)]

private theorem free_score (m : Edge l → Bool) (p : Face l) (hu : P.freeUniform m p)
    {z : WilsonReplicas l} (hz : P.IsPinned z) : faceScore p (exchangeLinks m z) = faceScore p z := by
  obtain ⟨b,hm⟩ := hu
  obtain ⟨a,c⟩ := P.trace_free p m b hm hz
  cases b <;> simp_all [faceScore, add_comm]

/-- A second exchange cannot change this field if no face is split by both masks
on its free links. Stability is asserted on the pinned support only. -/
theorem free_field_stable (β : ℝ) (m n : Edge l → Bool)
    (hd : ∀ p : Face l, P.freeUniform m p ∨ P.freeUniform n p)
    {z : WilsonReplicas l} (hz : P.IsPinned z) :
    exchangeField β m (exchangeLinks n z) = exchangeField β m z := by
  rw [exchangeField_eq_sum, exchangeField_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rcases hd p with h | h
  · rw [P.free_score m p h (P.pinned_exchange hz n), P.free_score m p h hz, sub_self, sub_self]
  · rw [exchangeLinks_commute m n, P.free_score n p h hz, P.free_score n p h (P.pinned_exchange hz m)]

/-- Extend by retraction to use the full-space exchange theorem. Pulling back
along the projection removes the extension from both integrals. -/
theorem free_exchange (β : ℝ) (m : Edge l → Bool) {H : WilsonReplicas l → ℝ} (hc : Continuous H)
    (odd : ∀ z, P.IsPinned z → H (exchangeLinks m z) = -H z) :
    (∫ z, H z ∂P.framedLaw β) = ∫ z, H z * tanh (exchangeField β m z) ∂P.framedLaw β := by
  let K := H ∘ P.retractPair
  have ck : Continuous K := hc.comp P.retract_cont
  have cT : Continuous (fun z => tanh (exchangeField β m z)) :=
    replica_tanh_continuous.comp (exchangeField_cont β m)
  have extOdd (z : WilsonReplicas l) : K (exchangeLinks m z) = -K z := by
    simp only [K, Function.comp_apply, P.retract_exchange, odd _ (P.retract_pinned z)]
  have eq := P.framed_exchange β m ck extOdd
  have pull {f : WilsonReplicas l → ℝ} (cf : Continuous f) :
      (∫ z, f z ∂P.framedLaw β) = ∫ z, f (P.pair z) ∂replicaLaw l β :=
    integral_map P.pair_cont.measurable.aemeasurable cf.aestronglyMeasurable
  rw [pull ck, pull (f := fun z => K z * tanh (exchangeField β m z)) (ck.mul cT)] at eq
  rw [pull hc, pull (f := fun z => H z * tanh (exchangeField β m z)) (hc.mul cT)]
  simpa only [K, Function.comp_apply, P.retract_fixed (P.pinned_pair _)] using eq

/-- Signed product under the projected Wilson law. Only pinned pairs have to
see an odd observable; only free links can witness a split face. -/
theorem free_shell_identity (β : ℝ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Edge l → Bool) {D : WilsonReplicas l → ℝ} (hc : Continuous D)
    (ha : ∀ i ∈ s, ∀ z, P.IsPinned z → D (exchangeLinks (m i) z) = -D z)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ p : Face l, P.freeUniform (m i) p ∨ P.freeUniform (m j) p) :
    (∫ z, D z ∂P.framedLaw β) = ∫ z, D z * ∏ i ∈ s, tanh (exchangeField β (m i) z) ∂P.framedLaw β := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let H := fun z => D z * ∏ j ∈ s, tanh (exchangeField β (m j) z)
    have cH : Continuous H := hc.mul (continuous_finsetProd _ fun j _ =>
      replica_tanh_continuous.comp (exchangeField_cont β (m j)))
    have odd (z : WilsonReplicas l) (hz : P.IsPinned z) : H (exchangeLinks (m i) z) = -H z := by
      have st (j) (hj : j ∈ s) := P.free_field_stable β (m j) (m i)
        (hd j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self ..) (fun eq => hi (eq ▸ hj))) hz
      simp only [H, ha i (Finset.mem_insert_self ..) z hz, neg_mul]
      rw [Finset.prod_congr rfl fun j hj => congrArg tanh (st j hj)]
    rw [ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))]
    change (∫ z, H z ∂P.framedLaw β) = _
    rw [P.free_exchange β (m i) cH odd]
    exact integral_congr_ae (.of_forall fun z => by simp [H, Finset.prod_insert hi]; ring)

/-- Each mask interchanges the free links of exactly one endpoint and leaves the
other endpoint's free links in place; the choice of endpoint may vary by mask.
The covariance and sampling law are the original ones, not tree-conditioned laws. -/
theorem free_plaquette_covariance (β : ℝ) (p q : Face l) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → Edge l → Bool)
    (ends : ∀ i ∈ s, ∃ b : Bool, (∀ e ∈ P.freeFace p, m i e = b) ∧
      (∀ e ∈ P.freeFace q, m i e = !b))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a : Face l, P.freeUniform (m i) a ∨ P.freeUniform (m j) a) :
    2 * wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) =
      ∫ z, replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) z *
        ∏ i ∈ s, tanh (exchangeField β (m i) (P.pair z)) ∂replicaLaw l β := by
  let D := replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q)
  have cp := (wilsonPlaquetteTrace_variation p).continuous
  have cq := (wilsonPlaquetteTrace_variation q).continuous
  have cD : Continuous D := ((cp.comp continuous_fst).sub (cp.comp continuous_snd)).mul
    ((cq.comp continuous_fst).sub (cq.comp continuous_snd))
  have odd i (hi : i ∈ s) (z : WilsonReplicas l) (hz : P.IsPinned z) : D (exchangeLinks (m i) z) = -D z := by
    obtain ⟨b,hp,hq⟩ := ends i hi
    obtain ⟨p₁,p₂⟩ := P.trace_free p (m i) b hp hz
    obtain ⟨q₁,q₂⟩ := P.trace_free q (m i) (!b) hq hz
    cases b <;> simp [D, replicaDifference, p₁, p₂, q₁, q₂] <;> ring
  have gauge (z : WilsonReplicas l) : D (P.pair z) = D z := by
    simp [D, replicaDifference, pair, project, wilsonPlaquetteTrace_gauge_invariant]
  have eq := P.free_shell_identity β s m cD odd hd
  have cR : Continuous (fun z => D z * ∏ i ∈ s, tanh (exchangeField β (m i) z)) :=
    cD.mul (continuous_finsetProd s fun i _ => replica_tanh_continuous.comp (exchangeField_cont β (m i)))
  unfold framedLaw at eq
  rw [integral_map P.pair_cont.measurable.aemeasurable cD.aestronglyMeasurable,
    integral_map P.pair_cont.measurable.aemeasurable cR.aestronglyMeasurable] at eq
  rw [twice_wilsonCovariance β cp cq]
  simpa only [gauge] using eq

/-- Dropping oddness gives a false one-mask identity: at zero coupling its
right side vanishes for any mask, whereas the normalized integral of one is one. -/
theorem no_exchange_without_odd (m : Edge l → Bool) :
    (∫ _ : WilsonReplicas l, (1 : ℝ) ∂P.framedLaw 0) ≠
      ∫ z, 1 * tanh (exchangeField 0 m z) ∂P.framedLaw 0 := by
  simp [exchangeField, logWeight, Real.tanh_zero]

#print axioms free_field_stable
#print axioms freeBoundary_disjoint
#print axioms free_anchor_labels
#print axioms exchange_eq_on_free
#print axioms free_exchange
#print axioms free_shell_identity
#print axioms free_plaquette_covariance
#print axioms no_exchange_without_odd
end
end YangMills.PeriodicWilson.PinnedFrame
