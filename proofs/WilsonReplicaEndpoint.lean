-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaFrame
import WilsonReplicaSlabs

namespace YangMills.PeriodicWilson
open FundamentalSU2 WilsonPolymer MeasureTheory Real
open scoped Matrix.Norms.Frobenius
noncomputable section

def faceMask {l : ℕ+} (p : Face l) (e : Edge l) := decide (e ∈ faceEdges p)

private theorem spatial_edge_time {l : ℕ+} (p : Face l) (t : Axis) (hi : t ≠ p.2.val.1) (hj : t ≠ p.2.val.2)
    {e : Edge l} (he : e ∈ faceEdges p) : e.1 t = p.1 t := by
  simp only [faceEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · rfl
  · change (p.1 + Pi.single p.2.val.1 (1 : ZMod l.val) : Site l) t = _; simp [hi]
  · change (p.1 + Pi.single p.2.val.2 (1 : ZMod l.val) : Site l) t = _; simp [hj]
  · rfl

theorem separated_endpoint_cuts {l : ℕ+} (p q : Face l) (t : Axis)
    (pi₁ : t ≠ p.2.val.1) (pi₂ : t ≠ p.2.val.2) (qi₁ : t ≠ q.2.val.1) (qi₂ : t ≠ q.2.val.2)
    (h₀ : p.1 t ≠ q.1 t) (h₁ : p.1 t+1 ≠ q.1 t) (h₂ : q.1 t+1 ≠ p.1 t) :
    Disjoint (faceEdges p) (faceEdges q) ∧
      ∀ a : Face l, uniformOnFace (faceMask p) a ∨ uniformOnFace (faceMask q) a := by
  have pt := fun {e} he => spatial_edge_time p t pi₁ pi₂ (e := e) he
  have qt := fun {e} he => spatial_edge_time q t qi₁ qi₂ (e := e) he
  refine ⟨Finset.disjoint_left.mpr (fun _ hp hq => h₀ ((pt hp).symm.trans (qt hq))),?_⟩
  intro a
  by_cases h : ∃ e ∈ faceEdges a, e ∈ faceEdges p
  · obtain ⟨e,ea,ep⟩ := h
    refine .inr ⟨false, fun f fa => ?_⟩
    have hn : f ∉ faceEdges q := by
      intro fq
      have hp := face_base_times a t ea
      have hq := face_base_times a t fa
      rw [pt ep] at hp; rw [qt fq] at hq
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> grind
    simp [faceMask,hn]
  · exact .inl ⟨false, fun e ea => by simp [faceMask,show e ∉ faceEdges p from fun ep => h ⟨e,ea,ep⟩]⟩

private def suStaple {l : ℕ+} (U : WilsonConfig l) (e : Edge l) : M := stapleMatrix U e

/-- The signed exchange energy for one link is a product of two differences:
link matrices and the six-staple matrices in the two backgrounds. -/
def stapleExchange {l : ℕ+} (β : ℝ) (e : Edge l) (z : WilsonReplicas l) : ℝ :=
  β/4 * ((suMat (z.1 e) - suMat (z.2 e)) * (suStaple z.1 e - suStaple z.2 e)).trace.re

theorem singleLink_exchange {l : ℕ+} (hl : 1 < l.val) (β : ℝ) (e : Edge l) (z : WilsonReplicas l) :
    exchangeField β (fun f => decide (f=e)) z = stapleExchange β e z := by
  let S := exchangeLinks (fun f => decide (f=e)) z
  have first : S.1 = Function.update z.1 e (z.2 e) := by funext f; by_cases h : f=e <;> simp [S,exchangeLinks,Function.update,h]
  have second : S.2 = Function.update z.2 e (z.1 e) := by funext f; by_cases h : f=e <;> simp [S,exchangeLinks,Function.update,h]
  have energy (U : WilsonConfig l) (v : gaugeGroup.image) :
      wilsonEnergy (Function.update U e v) - wilsonEnergy U = fieldProjection U e (U e) - fieldProjection U e v := by
    have h₁ := one_link_energy_difference hl U e v
    have h₂ := one_link_energy_difference hl U e (U e)
    rw [Function.update_eq_self] at h₂; linarith
  change (-β*(wilsonEnergy z.1+wilsonEnergy z.2) - -β*(wilsonEnergy S.1+wilsonEnergy S.2))/2 = _
  rw [first,second]
  have h₁ := energy z.1 (z.2 e)
  have h₂ := energy z.2 (z.1 e)
  change _ = (suMat (z.1 e) * suStaple z.1 e).trace.re/2 - (suMat (z.2 e) * suStaple z.1 e).trace.re/2 at h₁
  change _ = (suMat (z.2 e) * suStaple z.2 e).trace.re/2 - (suMat (z.1 e) * suStaple z.2 e).trace.re/2 at h₂
  simp only [stapleExchange,sub_mul,mul_sub,Matrix.trace_sub,Complex.sub_re]
  linear_combination β/2*(h₁+h₂)

private theorem trace_product_bound (A B : M) : |(A*B).trace.re| ≤ ‖A‖*‖B‖ := by
  let t := fun x : Fin 2 × Fin 2 => A x.1 x.2 * B x.2 x.1
  have htr : (A*B).trace = ∑ x, t x := by
    simp [t,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type]
  have habs := (Complex.abs_re_le_norm (∑ x, t x)).trans (norm_sum_le _ _)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun x => ‖A x.1 x.2‖) (fun x => ‖B x.2 x.1‖)
  have hf (C : M) : ‖C‖ = sqrt (∑ i, ∑ j, ‖C i j‖^2) := by
    simp [Matrix.frobenius_norm_def,Real.sqrt_eq_rpow]
  rw [htr,hf A,hf B]
  simp only [t,norm_mul] at habs
  simp only [Fintype.sum_prod_type] at habs hcs
  rw [Finset.sum_comm (f := fun i j : Fin 2 => ‖B j i‖^2)] at hcs
  simpa only [t,Fintype.sum_prod_type] using habs.trans hcs

/-- An observable sufficient test for moderate exchange fields. Both matrix
differences are measured in a common pinned frame. -/
theorem stapleExchange_abs_le {l : ℕ+} (β : ℝ) (e : Edge l) (z : WilsonReplicas l) :
    |stapleExchange β e z| ≤ |β|/4 *
      (linkChord (z.1 e) (z.2 e) * ‖stapleMatrix z.1 e - stapleMatrix z.2 e‖) := by
  rw [stapleExchange,abs_mul,abs_div,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left (trace_product_bound _ _) (by positivity)

/-- If three sides of the loop are pinned, exchanging its four links costs
exactly the signed one-link staple difference on its remaining side. -/
theorem framed_face_field {l : ℕ+} (P : PinnedFrame l) (hl : 1 < l.val) (β : ℝ) (p : Face l)
    (e : Edge l) (he : e ∈ faceEdges p) (pins : ∀ f ∈ faceEdges p, f ≠ e → f ∈ P.edges) (z : WilsonReplicas l) :
    exchangeField β (faceMask p) (P.pair z) = stapleExchange β e (P.pair z) := by
  rw [← singleLink_exchange hl]
  have eq : exchangeLinks (faceMask p) (P.pair z) = exchangeLinks (fun f => decide (f=e)) (P.pair z) := by
    apply Prod.ext <;> funext f <;> by_cases h : f=e
    all_goals try (subst f; simp [exchangeLinks,faceMask,he])
    all_goals by_cases hf : f ∈ faceEdges p
    all_goals try (solve | simp [exchangeLinks,faceMask,hf,h])
    all_goals
      have a : P.project z.1 f = 1 := P.pins z.1 ⟨f,pins f hf h⟩
      have b : P.project z.2 f = 1 := P.pins z.2 ⟨f,pins f hf h⟩
      simp [exchangeLinks,faceMask,hf,h,PinnedFrame.pair,a,b]
  unfold exchangeField; rw [eq]

set_option maxHeartbeats 750000 in
/-- Two separated plaquette endpoints admit two bounded-size exchange
surfaces. In the pinned forest each factor uses exactly one link and its staples. -/
theorem endpoint_covariance_identity {l : ℕ+} (P : PinnedFrame l) (hl : 1 < l.val) (β : ℝ)
    (p q : Face l) (e f : Edge l) (he : e ∈ faceEdges p) (hf : f ∈ faceEdges q)
    (pe : ∀ a ∈ faceEdges p, a ≠ e → a ∈ P.edges) (qf : ∀ a ∈ faceEdges q, a ≠ f → a ∈ P.edges)
    (pq : Disjoint (faceEdges p) (faceEdges q))
    (cut : ∀ a : Face l, uniformOnFace (faceMask p) a ∨ uniformOnFace (faceMask q) a) :
    2*wilsonCovariance β (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) =
      ∫ z, replicaDifference (wilsonPlaquetteTrace p) (wilsonPlaquetteTrace q) z *
        (tanh (stapleExchange β e (P.pair z)) * tanh (stapleExchange β f (P.pair z))) ∂replicaLaw l β := by
  let F := wilsonPlaquetteTrace p
  let H := wilsonPlaquetteTrace q
  let D := replicaDifference F H
  let mask := fun i : Bool => if i then faceMask q else faceMask p
  have cF : Continuous F := (wilsonPlaquetteTrace_variation p).continuous
  have cH : Continuous H := (wilsonPlaquetteTrace_variation q).continuous
  have cD : Continuous D := ((cF.comp continuous_fst).sub (cF.comp continuous_snd)).mul
    ((cH.comp continuous_fst).sub (cH.comp continuous_snd))
  have same (a : Face l) (m : Edge l → Bool) (b : Bool) (hm : ∀ x ∈ faceEdges a, m x = b) (z : WilsonReplicas l) :
      wilsonPlaquetteTrace a (exchangeLinks m z).1 = wilsonPlaquetteTrace a (if b then z.2 else z.1) ∧
      wilsonPlaquetteTrace a (exchangeLinks m z).2 = wilsonPlaquetteTrace a (if b then z.1 else z.2) := by
    constructor <;> apply trace_agrees <;> intro x hx <;> cases b <;> simp [exchangeLinks,hm x hx]
  have own (a : Face l) : ∀ x ∈ faceEdges a, faceMask a x = true := fun _ h => by simp [faceMask,h]
  have other {a b : Face l} (h : Disjoint (faceEdges a) (faceEdges b)) :
      ∀ x ∈ faceEdges a, faceMask b x = false := fun _ hx => by simp [faceMask,Finset.disjoint_left.mp h hx]
  have anti (i : Bool) (z : WilsonReplicas l) : D (exchangeLinks (mask i) z) = -D z := by
    cases i
    · obtain ⟨a,b⟩ := same p _ true (own p) z
      obtain ⟨c,d⟩ := same q _ false (other pq.symm) z
      simp only [D,replicaDifference,F,H,mask,Bool.false_eq_true,if_false,if_true] at *; rw [a,b,c,d]; ring
    · obtain ⟨a,b⟩ := same p _ false (other pq) z
      obtain ⟨c,d⟩ := same q _ true (own q) z
      simp only [D,replicaDifference,F,H,mask,if_true,if_false,Bool.false_eq_true] at *; rw [a,b,c,d]; ring
  have hg (z : WilsonReplicas l) : D (P.pair z) = D z := by
    simp [D,F,H,replicaDifference,PinnedFrame.pair,PinnedFrame.project,wilsonPlaquetteTrace_gauge_invariant]
  have eq := P.framed_shell_identity β (Finset.univ : Finset Bool) mask cD hg (fun i _ => anti i)
    (fun i _ j _ hij a => by
      cases i <;> cases j
      · exact False.elim (hij rfl)
      · exact cut a
      · exact (cut a).symm
      · exact False.elim (hij rfl))
  rw [twice_wilsonCovariance β cF cH,eq]
  apply integral_congr_ae
  exact .of_forall fun z => by simp [D,F,H,mask,framed_face_field P hl β p e he pe z,framed_face_field P hl β q f hf qf z,mul_comm]

#print axioms stapleExchange_abs_le
#print axioms singleLink_exchange
#print axioms endpoint_covariance_identity
end
end YangMills.PeriodicWilson
