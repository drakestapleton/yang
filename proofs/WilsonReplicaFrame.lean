-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaShells

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real
noncomputable section

private abbrev G := gaugeGroup.image

/-- A frame determined by the links it pins. Rooted tree parallel transport
has precisely this triangular dependence. -/
structure PinnedFrame (l : ℕ+) where
  edges : Finset (Edge l)
  frame : ({e // e ∈ edges} → G) → Site l → G
  continuous_frame : Continuous frame
  pins : ∀ (U : WilsonConfig l) (e : {e // e ∈ edges}),
    gaugeAct (frame (fun a => U a.val)) U e.val = 1

namespace PinnedFrame
variable {l : ℕ+} (P : PinnedFrame l)

def empty (l : ℕ+) : PinnedFrame l where
  edges := ∅
  frame := fun _ _ => 1
  continuous_frame := continuous_const
  pins := fun _ e => False.elim (Finset.notMem_empty _ e.prop)

def edgeEnd (e : Edge l) : Site l := e.1 + Pi.single e.2 1

/-- Grow a pinned forest by one edge in either orientation. The child is a
new vertex for the previous pinned edges. A parent may begin a new component. -/
def attach (e : Edge l) (rev : Bool) (hne : e.1 ≠ edgeEnd e)
    (fresh : ∀ f ∈ P.edges, (if rev then e.1 else edgeEnd e) ≠ f.1 ∧
      (if rev then e.1 else edgeEnd e) ≠ edgeEnd f) : PinnedFrame l := by
  let child := if rev then e.1 else edgeEnd e
  let parent := if rev then edgeEnd e else e.1
  let restrict (v : {f // f ∈ insert e P.edges} → G) (f : {f // f ∈ P.edges}) :=
    v ⟨f.val,Finset.mem_insert_of_mem f.prop⟩
  let g (v : {f // f ∈ insert e P.edges} → G) := v ⟨e,Finset.mem_insert_self ..⟩
  let frame (v : {f // f ∈ insert e P.edges} → G) (x : Site l) :=
    if x=child then P.frame (restrict v) parent * (if rev then (g v)⁻¹ else g v)
    else P.frame (restrict v) x
  refine ⟨insert e P.edges,frame,?_,?_⟩
  · have cr : Continuous restrict := continuous_pi fun _ => continuous_apply _
    have cf := P.continuous_frame.comp cr
    have cg : Continuous g := continuous_apply _
    apply continuous_pi; intro x
    by_cases h : x=child
    · simp only [frame,if_pos h]
      cases rev <;> simp only [Bool.false_eq_true,if_false,if_true]
      · exact ((continuous_apply parent).comp cf).mul cg
      · exact ((continuous_apply parent).comp cf).mul cg.inv
    · simp only [frame,if_neg h]; exact (continuous_apply x).comp cf
  · intro U f
    rcases Finset.mem_insert.mp f.prop with he | hf
    · change frame (fun a => U a.val) f.val.1 * U f.val * (frame (fun a => U a.val) (edgeEnd f.val))⁻¹ = 1
      rw [he]
      cases rev <;> simp [frame,child,parent,g,restrict,hne,Ne.symm hne,mul_assoc]
    · obtain ⟨h₁,h₂⟩ := fresh f.val hf
      change frame (fun a => U a.val) f.val.1 * U f.val * (frame (fun a => U a.val) (edgeEnd f.val))⁻¹ = 1
      have hn₁ : f.val.1 ≠ child := Ne.symm h₁
      have hn₂ : edgeEnd f.val ≠ child := Ne.symm h₂
      simp only [frame,if_neg hn₁,if_neg hn₂]
      exact P.pins U ⟨f.val,hf⟩

def project (U : WilsonConfig l) := gaugeAct (P.frame fun e => U e.val) U

private def erase (U : WilsonConfig l) : WilsonConfig l := fun e => if e ∈ P.edges then 1 else U e

private theorem project_cont : Continuous P.project := by
  have cr : Continuous (fun U : WilsonConfig l => fun e : {e // e ∈ P.edges} => U e.val) := continuous_pi fun e => continuous_apply _
  have cf := P.continuous_frame.comp cr
  apply continuous_pi; intro e
  exact (((continuous_apply e.1).comp cf).mul (continuous_apply e)).mul (((continuous_apply _).comp cf).inv)

private theorem erase_cont : Continuous P.erase := by
  apply continuous_pi; intro e; by_cases he : e ∈ P.edges <;> simp [erase,he] <;> fun_prop

/-- Under independent Haar links the pinned coordinates become identities
and all remaining links keep their independent Haar laws. -/
theorem map_prior : (prior l).map P.project = (prior l).map P.erase := by
  let A := {e : Edge l // e ∈ P.edges}
  let B := {e : Edge l // e ∉ P.edges}
  letI : Fintype A := Subtype.fintype (fun e : Edge l => e ∈ P.edges)
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge l => G) (· ∈ P.edges)
  let out (v : A → G) (w : B → G) (e : B) := P.frame v e.val.1 * w e * (P.frame v (e.val.1 + Pi.single e.val.2 1))⁻¹
  have ho (v : A → G) : MeasurePreserving (out v) (Measure.pi fun _ : B => su2Haar) (Measure.pi fun _ : B => su2Haar) := by
    have hR (g : G) : MeasurePreserving (fun x : G => x*g) su2Haar su2Haar :=
      ⟨(continuous_mul_const _).measurable, PhaseFour.gaugeImage_haar_map_mul_right su2Haar _⟩
    have each (e : B) : MeasurePreserving (fun x : G => P.frame v e.val.1 * x * (P.frame v (edgeEnd e.val))⁻¹) su2Haar su2Haar :=
      (hR _).comp (measurePreserving_mul_left su2Haar _)
    exact measurePreserving_pi (fun _ : B => su2Haar) (fun _ : B => su2Haar) each
  have cm : Continuous (Function.uncurry out) := by
    apply continuous_pi; intro e
    have cf := P.continuous_frame.comp (continuous_fst : Continuous (Prod.fst : (A → G) × (B → G) → _))
    exact (((continuous_apply e.val.1).comp cf).mul ((continuous_apply e).comp continuous_snd)).mul (((continuous_apply (edgeEnd e.val)).comp cf).inv)
  have hs := (MeasurePreserving.id (Measure.pi fun _ : A => su2Haar)).skew_product (μc := Measure.pi fun _ : B => su2Haar) (μd := Measure.pi fun _ : B => su2Haar) (g := out) cm.measurable (.of_forall fun v => (ho v).map_eq)
  have hE := measurePreserving_piEquivPiSubtypeProd (fun _ : Edge l => su2Haar) (· ∈ P.edges)
  let chart (U : WilsonConfig l) := E.symm ((E U).1, out (E U).1 (E U).2)
  have hC : MeasurePreserving chart (prior l) (prior l) := (hE.symm E).comp (hs.comp hE)
  have factor : P.erase ∘ chart = P.project := by
    funext U e
    by_cases he : e ∈ P.edges
    · change (if e ∈ P.edges then 1 else chart U e) = P.project U e
      rw [if_pos he]; exact (P.pins U ⟨e,he⟩).symm
    · simp [Function.comp_apply,erase,chart,E,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,
        he,project,gaugeAct,out]
  rw [← factor, ← Measure.map_map P.erase_cont.measurable hC.measurable, hC.map_eq]

def pair (z : WilsonReplicas l) : WilsonReplicas l := (P.project z.1,P.project z.2)

def framedLaw (β : ℝ) := (replicaLaw l β).map P.pair

theorem pair_cont : Continuous P.pair :=
  (P.project_cont.comp continuous_fst).prodMk (P.project_cont.comp continuous_snd)

instance framedLaw_probability (β : ℝ) : IsProbabilityMeasure (P.framedLaw β) :=
  Measure.isProbabilityMeasure_map P.pair_cont.measurable.aemeasurable

theorem integral_projected (β : ℝ) {D : WilsonReplicas l → ℝ} (hc : Continuous D)
    (hg : ∀ z, D (P.pair z) = D z) : (∫ z, D z ∂P.framedLaw β) = ∫ z, D z ∂replicaLaw l β := by
  unfold framedLaw
  rw [integral_map P.pair_cont.measurable.aemeasurable hc.aestronglyMeasurable]
  exact integral_congr_ae (.of_forall hg)

private abbrev pairPrior := (prior l).prod (prior l)

private theorem prior_exchange (m : Edge l → Bool) : MeasurePreserving (exchangeLinks m)
    ((pairPrior (l := l)).map P.pair) ((pairPrior (l := l)).map P.pair) := by
  let eraseBoth (z : WilsonReplicas l) : WilsonReplicas l := (P.erase z.1,P.erase z.2)
  have ce : Continuous eraseBoth := (P.erase_cont.comp continuous_fst).prodMk (P.erase_cont.comp continuous_snd)
  have maps : (pairPrior (l := l)).map P.pair = (pairPrior (l := l)).map eraseBoth := by
    change Measure.map (Prod.map P.project P.project) _ = Measure.map (Prod.map P.erase P.erase) _
    rw [← Measure.map_prod_map _ _ P.project_cont.measurable P.project_cont.measurable,
      ← Measure.map_prod_map _ _ P.erase_cont.measurable P.erase_cont.measurable, P.map_prior]
  have commute : exchangeLinks m ∘ eraseBoth = eraseBoth ∘ exchangeLinks m := by
    funext z; apply Prod.ext <;> funext e <;> by_cases he : e ∈ P.edges <;> cases hm : m e <;>
      simp [eraseBoth,Function.comp_apply,exchangeLinks,erase,he,hm]
  refine ⟨(exchange_cont m).measurable, ?_⟩
  rw [maps,Measure.map_map (exchange_cont m).measurable ce.measurable,commute,
    ← Measure.map_map ce.measurable (exchange_cont m).measurable,(exchange_preserving m).map_eq]

private theorem framed_integral (β : ℝ) {D : WilsonReplicas l → ℝ} (hc : Continuous D) :
    ∫ z, D z ∂P.framedLaw β =
      (∫ z, exp (logWeight β z)*D z ∂(pairPrior (l := l)).map P.pair) /
        (∫ U, exp (-β*wilsonEnergy U) ∂prior l)^2 := by
  have cD : Continuous (fun z => exp (logWeight β z) * D z) := (continuous_exp.comp (logWeight_cont β)).mul hc
  unfold framedLaw
  rw [integral_map P.pair_cont.measurable.aemeasurable hc.aestronglyMeasurable,replica_integral,
    integral_map P.pair_cont.measurable.aemeasurable cD.aestronglyMeasurable]
  simp only [logWeight,pair,project,WilsonPolymer.wilsonEnergy_gauge_invariant]

theorem framed_exchange (β : ℝ) (m : Edge l → Bool) {D : WilsonReplicas l → ℝ}
    (hc : Continuous D) (ha : ∀ z, D (exchangeLinks m z) = -D z) :
    (∫ z, D z ∂P.framedLaw β) = ∫ z, D z * tanh (exchangeField β m z) ∂P.framedLaw β := by
  have cD : Continuous (fun z => D z * tanh (exchangeField β m z)) := hc.mul (replica_tanh_continuous.comp (exchangeField_cont β m))
  rw [P.framed_integral β hc,P.framed_integral β cD,
    weighted_exchange_identity β m _ (P.prior_exchange m) hc ha]

/-- Gauge-invariant observables can be measured on the original replicas,
while every exchange factor is evaluated after pinning each replica. -/
theorem framed_shell_identity (β : ℝ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Edge l → Bool) {D : WilsonReplicas l → ℝ} (hc : Continuous D)
    (hg : ∀ z, D (P.pair z) = D z)
    (ha : ∀ i ∈ s, ∀ z, D (exchangeLinks (m i) z) = -D z)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ p : Face l, uniformOnFace (m i) p ∨ uniformOnFace (m j) p) :
    (∫ z, D z ∂replicaLaw l β) = ∫ z, D z * ∏ i ∈ s, tanh (exchangeField β (m i) (P.pair z)) ∂replicaLaw l β := by
  have eq := shell_identity_of_exchange β _ (P.framed_exchange β) s m hc ha hd
  have cp : Continuous (fun z => D z * ∏ i ∈ s, tanh (exchangeField β (m i) z)) := hc.mul (continuous_finsetProd s fun i _ => replica_tanh_continuous.comp (exchangeField_cont β (m i)))
  unfold framedLaw at eq
  rw [integral_map P.pair_cont.measurable.aemeasurable hc.aestronglyMeasurable,
    integral_map P.pair_cont.measurable.aemeasurable cp.aestronglyMeasurable] at eq
  simpa only [hg] using eq

end PinnedFrame
#print axioms PinnedFrame.map_prior
#print axioms PinnedFrame.framed_shell_identity
end
end YangMills.PeriodicWilson
