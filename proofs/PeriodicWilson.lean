-- SPDX-License-Identifier: Apache-2.0
import OneLinkTransport
import FundamentalSU2

namespace YangMills.PeriodicWilson

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section

abbrev Edge (l : ℕ+) := Site l × Axis
abbrev Face (l : ℕ+) := Site l × Directions
private abbrev Mat (g : GaugeGroup) := Matrix (Fin (g.n+1)) (Fin (g.n+1)) ℂ
private def rep {g : GaugeGroup} (v : g.image) : Mat g := v.val.val
private def score {g : GaugeGroup} (v : g.image) : ℝ := (rep v).trace.re / (g.n+1 : ℕ)

private theorem score_cycle {g : GaugeGroup} (u v : g.image) : score (u*v) = score (v*u) := by
  unfold score
  change (rep u * rep v).trace.re / _ = (rep v * rep u).trace.re / _
  rw [Matrix.trace_mul_comm]

private theorem score_inv {g : GaugeGroup} (u : g.image) : score u⁻¹ = score u := by
  unfold score
  change (rep u).conjTranspose.trace.re / _ = _
  rw [Matrix.trace_conjTranspose]
  rfl

private theorem unitary_norm {g : GaugeGroup} (u : g.image) :
    ‖rep u‖ = Real.sqrt (g.n+1 : ℕ) := by
  have he : rep u * (rep u).conjTranspose = 1 := by
    change rep (u*u⁻¹) = rep (1 : g.image)
    rw [mul_inv_cancel]
  have row (i : Fin (g.n+1)) : ∑ j, ‖rep u i j‖ ^ 2 = 1 := by
    have hh := congrArg (fun A : Mat g => (A i i).re) he
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.one_re] at hh
    simpa [Complex.mul_re, Complex.normSq_apply, ← Complex.normSq_eq_norm_sq] using hh
  rw [Matrix.frobenius_norm_def]
  simp [row, Real.sqrt_eq_rpow]

private def shift {l : ℕ+} (i : Axis) : Site l := Pi.single i 1

private theorem shifted_ne {l : ℕ+} (hl : 1 < l.val) (x : Site l) (i : Axis) :
    x + shift i ≠ x := by
  haveI : Fact (1 < l.val) := ⟨hl⟩
  intro h
  have h' := congrFun h i
  simp [shift] at h'

private def corners {l : ℕ+} (p : Face l) : Edge l × Edge l × Edge l × Edge l :=
  let i := p.2.val.1
  let j := p.2.val.2
  ((p.1,i), (p.1+shift i,j), (p.1+shift j,i), (p.1,j))

/-- Incident faces of a positive oriented periodic link, in the ordered direction
convention of PublicWilson. Each transverse axis contributes the face based at the
link and the face one step back in that transverse direction. -/
def incidentFaces {l : ℕ+} (e : Edge l) : Finset (Face l) :=
  (Finset.univ.filter (fun p : Directions => p.val.1 = e.2 ∨ p.val.2 = e.2)).biUnion fun p =>
    {(e.1,p), (e.1 - shift (if p.val.1=e.2 then p.val.2 else p.val.1),p)}

private theorem direction_count (μ : Axis) :
    (Finset.univ.filter (fun p : Directions => p.val.1=μ ∨ p.val.2=μ)).card = 3 := by
  fin_cases μ <;> decide

theorem incident_faces_le_six {l : ℕ+} (e : Edge l) : (incidentFaces e).card ≤ 6 := by
  unfold incidentFaces
  apply Finset.card_biUnion_le.trans
  calc _ ≤ ∑ _p ∈ Finset.univ.filter (fun p : Directions => p.val.1=e.2 ∨ p.val.2=e.2), 2 :=
         Finset.sum_le_sum fun _ _ => Finset.card_insert_le _ _ |>.trans (by simp)
       _ = 6 := by simp [direction_count]


theorem incident_faces_eq_six {l : ℕ+} (hl : 1 < l.val) (e : Edge l) : (incidentFaces e).card = 6 := by
  classical
  unfold incidentFaces
  rw [Finset.card_biUnion]
  · calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Directions => p.val.1=e.2 ∨ p.val.2=e.2), 2 := by
           apply Finset.sum_congr rfl
           intro p _
           rw [Finset.card_insert_of_notMem, Finset.card_singleton]
           simp only [Finset.mem_singleton, Prod.mk.injEq, and_true, eq_sub_iff_add_eq]
           exact shifted_ne hl _ _
         _ = 6 := by simp [direction_count]
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro z hp hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with h | h <;> exact hpq (congrArg Prod.snd h)

/-- These labels retain multiplicity when two plaquettes use the same neighbor link. -/
def incidences {l : ℕ+} (e : Edge l) := (incidentFaces e) ×ˢ (Finset.univ : Finset (Fin 3))

theorem incidence_count {l : ℕ+} (hl : 1 < l.val) (e : Edge l) : (incidences e).card = 18 := by
  simp [incidences, incident_faces_eq_six hl]

private theorem incident_iff {l : ℕ+} (p : Face l) (e : Edge l) :
    p ∈ incidentFaces e ↔ (corners p).1 = e ∨ (corners p).2.1 = e ∨
      (corners p).2.2.1 = e ∨ (corners p).2.2.2 = e := by
  rcases p with ⟨x,q⟩
  have hmem : (x,q) ∈ incidentFaces e ↔ (q.val.1=e.2 ∨ q.val.2=e.2) ∧
      (x=e.1 ∨ x=e.1-shift (if q.val.1=e.2 then q.val.2 else q.val.1)) := by
    simp only [incidentFaces, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨q', h, ⟨ha,rfl⟩ | ⟨hb,rfl⟩⟩
      · exact ⟨h,Or.inl ha⟩
      · exact ⟨h,Or.inr hb⟩
    · rintro ⟨h, ha | hb⟩
      · exact ⟨q,h,Or.inl ⟨ha,rfl⟩⟩
      · exact ⟨q,h,Or.inr ⟨hb,rfl⟩⟩
  rw [hmem]
  have hij := ne_of_lt q.property
  rcases e with ⟨y,μ⟩
  by_cases hi : q.val.1 = μ <;> by_cases hj : q.val.2 = μ <;>
    simp [corners, hi, hj, eq_sub_iff_add_eq, or_comm] at *

/-- Product of the other three links, rotated so the updated link is the first
factor. For a negatively traversed link we reverse the entire plaquette. -/
private def staple {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (e : Edge l)
    (p : Face l) : g.image :=
  let (a,b,c,d) := corners p
  if a=e then U b*(U c)⁻¹*(U d)⁻¹
  else if b=e then (U c)⁻¹*(U d)⁻¹*U a
  else if c=e then (U b)⁻¹*(U a)⁻¹*U d
  else U c*(U b)⁻¹*(U a)⁻¹

/-- On the one-site torus a face traverses both of its links twice. Its action
is a commutator and the six three-link staples are not a linear external field. -/
theorem period_one_plaquette {g : GaugeGroup} (U : Configuration g 1) (x : Site 1) (i j : Axis) :
    plaquette U x i j = U (x,i) * (U (x,j) * ((U (x,i))⁻¹ * (U (x,j))⁻¹)) := by
  letI : Subsingleton (Site 1) := inferInstanceAs (Subsingleton (Fin 4 → Fin 1))
  unfold plaquette
  have hi : x + Pi.single i 1 = x := Subsingleton.elim _ _
  have hj : x + Pi.single j 1 = x := Subsingleton.elim _ _
  rw [hi,hj]

private theorem corners_distinct {l : ℕ+} (hl : 1 < l.val) (p : Face l) :
    let (a,b,c,d) := corners p
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  let a := (corners p).1
  let b := (corners p).2.1
  let c := (corners p).2.2.1
  let d := (corners p).2.2.2
  have ij := ne_of_lt p.2.property
  have ab : a ≠ b := fun h => ij (congrArg Prod.snd h)
  have ac : a ≠ c := fun h => shifted_ne hl p.1 p.2.val.2 (congrArg Prod.fst h).symm
  have ad : a ≠ d := fun h => ij (congrArg Prod.snd h)
  have bc : b ≠ c := fun h => ij (congrArg Prod.snd h).symm
  have bd : b ≠ d := fun h => shifted_ne hl p.1 p.2.val.1 (congrArg Prod.fst h)
  have cd : c ≠ d := fun h => ij (congrArg Prod.snd h)
  exact ⟨ab,ac,ad,bc,bd,cd⟩

/-- Each incidence names a real link and its orientation in the three-link staple.
The Boolean is true for inverse traversal. -/
def neighbor {l : ℕ+} (e : Edge l) (p : Face l) : Fin 3 → Edge l × Bool :=
  let (a,b,c,d) := corners p
  if a=e then ![(b,false),(c,true),(d,true)]
  else if b=e then ![(c,true),(d,true),(a,false)]
  else if c=e then ![(b,true),(a,true),(d,false)]
  else ![(c,false),(b,true),(a,true)]

theorem neighbor_ne_self {l : ℕ+} (hl : 1 < l.val) {e : Edge l} {p : Face l}
    (hp : p ∈ incidentFaces e) (j : Fin 3) : (neighbor e p j).1 ≠ e := by
  have h := corners_distinct hl p
  have hh := (incident_iff p e).mp hp
  unfold neighbor
  generalize corners p = Q at *
  obtain ⟨a,b,c,d⟩ := Q
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := h
  rcases hh with rfl | rfl | rfl | rfl <;> fin_cases j <;> simp_all [ne_comm]

private def traverse {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (k : Edge l × Bool) :=
  if k.2 then (U k.1)⁻¹ else U k.1

private theorem staple_eq_neighbor_product {g : GaugeGroup} {l : ℕ+} (U : Configuration g l)
    (e : Edge l) (p : Face l) : staple U e p = traverse U (neighbor e p 0) *
      traverse U (neighbor e p 1) * traverse U (neighbor e p 2) := by
  unfold staple neighbor
  generalize corners p = Q
  obtain ⟨a,b,c,d⟩ := Q
  by_cases ha : a=e <;> by_cases hb : b=e <;> by_cases hc : c=e <;> simp [ha,hb,hc,traverse]

private theorem face_delta {g : GaugeGroup} {l : ℕ+} (hl : 1 < l.val)
    (U : Configuration g l) (e : Edge l) (v : g.image) (p : Face l) :
    let V := Function.update U e v
    score (plaquette V p.1 p.2.val.1 p.2.val.2) - score (plaquette U p.1 p.2.val.1 p.2.val.2) =
      if p ∈ incidentFaces e then score (v*staple U e p) - score (U e*staple U e p) else 0 := by
  classical
  let a := (corners p).1
  let b := (corners p).2.1
  let c := (corners p).2.2.1
  let d := (corners p).2.2.2
  let V := Function.update U e v
  change score (V a*(V b*((V c)⁻¹*(V d)⁻¹))) - score (U a*(U b*((U c)⁻¹*(U d)⁻¹))) = _
  have hdis : a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d := corners_distinct hl p
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := hdis
  by_cases hp : p ∈ incidentFaces e
  · rw [if_pos hp]
    change _ = score (v * (if a=e then _ else if b=e then _ else if c=e then _ else _)) -
      score (U e * (if a=e then _ else if b=e then _ else if c=e then _ else _))
    by_cases ha : a=e
    · subst e
      simp [V, ab.symm, ac.symm, ad.symm, mul_assoc]
      rfl
    by_cases hb : b=e
    · subst e
      simp [V, ab, bc.symm, bd.symm, mul_assoc]
      rw [score_cycle (U a), score_cycle (U a)]
      simp [mul_assoc]
      rfl
    by_cases hc : c=e
    · subst e
      simp [V, ac, bc, cd.symm, mul_assoc]
      rw [← score_inv (U a * _), ← score_inv (U a * _)]
      simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
      rw [score_cycle (U d), score_cycle (U d)]
      simp [mul_assoc]
      rfl
    have hde : d=e := (((incident_iff p e).mp hp).resolve_left ha |>.resolve_left hb).resolve_left hc
    subst e
    simp [V, ad, bd, cd, mul_assoc]
    rw [← score_inv (U a * _), ← score_inv (U a * _)]
    simp [_root_.mul_inv_rev, mul_assoc]
    rfl
  · have habsent := mt (incident_iff p e).mpr hp
    simp only [not_or] at habsent
    obtain ⟨ha,hb,hc,hd⟩ := habsent
    simp [V, if_neg hp, show a≠e from ha, show b≠e from hb, show c≠e from hc, show d≠e from hd]

/-- Sum of the six oriented three-link staples. Anchoring the chosen link to the
identity makes independence from its value explicit in the data used for this sum. -/
def stapleMatrix {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (e : Edge l) : Mat g :=
  ∑ p ∈ incidentFaces e, rep (staple (Function.update U e 1) e p)

def fieldStrength {g : GaugeGroup} {l : ℕ+} (β : ℝ) (U : Configuration g l) (e : Edge l) : ℝ :=
  β * (‖stapleMatrix U e‖ / Real.sqrt (g.n+1 : ℕ))

def fieldProjection {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (e : Edge l)
    (v : g.image) : ℝ := ((rep v * stapleMatrix U e).trace.re) / (g.n+1 : ℕ)

private theorem projection_sum {g : GaugeGroup} {l : ℕ+} (U : Configuration g l)
    (e : Edge l) (v : g.image) :
    fieldProjection U e v = ∑ p ∈ incidentFaces e, score (v * staple (Function.update U e 1) e p) := by
  simp only [fieldProjection, stapleMatrix, Finset.mul_sum, Matrix.trace_sum,
    Complex.re_sum, Finset.sum_div]
  rfl

/-- This identity connects the staple to the actual ordered plaquettes in the Wilson
Hamiltonian. The period-one torus has self-incidences and is excluded. -/
theorem one_link_energy_difference {g : GaugeGroup} {l : ℕ+} (hl : 1 < l.val)
    (U : Configuration g l) (e : Edge l) (v : g.image) :
    wilsonEnergy (Function.update U e v) - wilsonEnergy (Function.update U e 1) =
      fieldProjection U e 1 - fieldProjection U e v := by
  classical
  let A := Function.update U e 1
  have h (p : Face l) := face_delta hl A e v p
  have hu : Function.update A e v = Function.update U e v := Function.update_idem _ _ _
  have ha : A e = 1 := Function.update_self ..
  simp only [hu,ha] at h
  unfold wilsonEnergy
  rw [← Finset.sum_sub_distrib, projection_sum, projection_sum, ← Finset.sum_sub_distrib]
  change (∑ p : Face l, ((1-score (plaquette (Function.update U e v) p.1 p.2.val.1 p.2.val.2)) -
    (1-score (plaquette A p.1 p.2.val.1 p.2.val.2)))) = _
  calc _ = ∑ p : Face l, if p ∈ incidentFaces e then score (1*staple A e p)-score (v*staple A e p) else 0 := by
         apply Finset.sum_congr rfl; intro p _
         by_cases hp : p ∈ incidentFaces e <;> have hh := h p <;> simp only [hp, if_true, if_false] at hh ⊢ <;> linarith
       _ = _ := by rw [← Finset.sum_filter]; simp [A]

/-- Exact full-measure factorization at a link. The background factor and staple are
evaluated with that link pinned. The variable link enters only in the exponential
of its normalized trace against the staple. -/
theorem wilsonLaw_one_link_factorization {g : GaugeGroup} {l : ℕ+} (hl : 1 < l.val)
    (β : ℝ) (haar : Measure g.image) (e : Edge l) :
    let prior := Measure.pi fun _ : Edge l => haar
    let Z := ∫ U, Real.exp (-β * wilsonEnergy U) ∂prior
    wilsonLaw g l β haar = prior.withDensity (fun U => ENNReal.ofReal
      (Real.exp (-β*(wilsonEnergy (Function.update U e 1) + fieldProjection U e 1)) *
       Real.exp (β * fieldProjection U e (U e)) / Z)) := by
  dsimp only [wilsonLaw]
  congr 1
  funext U
  have hh := one_link_energy_difference hl U e (U e)
  rw [Function.update_eq_self] at hh
  rw [← Real.exp_add]
  congr 3
  linear_combination -β * hh

theorem fieldStrength_mem {g : GaugeGroup} {l : ℕ+} {β : ℝ} (hb : 0 ≤ β)
    (U : Configuration g l) (e : Edge l) : fieldStrength β U e ∈ Set.Icc 0 (6*β) := by
  have hdim : 0 < Real.sqrt (g.n+1 : ℕ) := by positivity
  have hnorm := norm_sum_le (incidentFaces e) (fun p => rep (staple (Function.update U e 1) e p))
  simp only [unitary_norm, Finset.sum_const, nsmul_eq_mul] at hnorm
  have hcard : ((incidentFaces e).card:ℝ) ≤ 6 := by exact_mod_cast incident_faces_le_six e
  have hh : ‖stapleMatrix U e‖ / Real.sqrt (g.n+1 : ℕ) ≤ 6 :=
    (div_le_iff₀ hdim).2 (hnorm.trans (mul_le_mul_of_nonneg_right hcard hdim.le))
  exact ⟨mul_nonneg hb (div_nonneg (norm_nonneg _) hdim.le), by
    simpa [fieldStrength,mul_comm] using mul_le_mul_of_nonneg_left hh hb⟩

open OneLinkTransport

/-- Unfixed degree-18 trial coefficient at the Wilson staple, uniformly in the
configuration and link. The trial energies are the SU(2) fundamental S³ energies. -/
theorem periodic_trial_row_lt_one {g : GaugeGroup} {l : ℕ+} {β : ℝ}
    (hb : 0 ≤ β) (hβ : β < Real.sqrt 3/9) (U : Configuration g l) (e : Edge l)
    {c s : ℝ} (hunit : c^2+s^2=1) :
    let r := fieldStrength β U e
    18*β*Real.sqrt (c^2*parallelEnergy r + s^2*transverseEnergy r) < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hmax : β ≤ 7/25 := by nlinarith
  have h := OneLinkTransport.s3_w2_orthogonality_bound hmax (fieldStrength_mem hb U e) hunit
  calc 18*β*Real.sqrt _ ≤ 18*β*(1/(2*Real.sqrt 3)) := mul_le_mul_of_nonneg_left h (by positivity)
       _ = 18*(1/(2*Real.sqrt 3))*β := by ring
       _ < 1 := WilsonPolymer.su2_4d_w2_dobrushin_window hβ

theorem strict_witness : (19/100 : ℝ) < 24/125 ∧ (24/125 : ℝ) < Real.sqrt 3/9 := by
  constructor
  · norm_num
  · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]

open FundamentalSU2

def suMat (u : gaugeGroup.image) : M := u.val.val

/-- Frobenius chord length in the fundamental representation. The normalized S³
chord length is this quantity divided by √2. -/
def linkChord (u v : gaugeGroup.image) : ℝ := ‖suMat u - suMat v‖

private theorem norm_mul_unit {A : M} (ha : A ∈ quaternionAlgebra) (u : gaugeGroup.image) :
    ‖A * suMat u‖ = ‖A‖ ∧ ‖suMat u * A‖ = ‖A‖ := by
  obtain ⟨v,hv⟩ := polar ha
  have hrad := frobenius_eq ha
  have h (k : gaugeGroup.image) : ‖suMat k‖ = Real.sqrt 2 := unitary_norm k
  have hlen : 0 ≤ length A := Real.sqrt_nonneg _
  rw [hrad]
  constructor
  · calc ‖A * suMat u‖ = ‖(length A • suMat v) * suMat u‖ := congrArg (fun B : M => ‖B*suMat u‖) hv
         _ = _ := by
           rw [Matrix.smul_mul, norm_smul, Real.norm_of_nonneg hlen]
           change length A * ‖suMat (v*u)‖ = _
           rw [h]; ring
  · calc ‖suMat u * A‖ = ‖suMat u * (length A • suMat v)‖ := congrArg (fun B : M => ‖suMat u*B‖) hv
         _ = _ := by
           rw [Matrix.mul_smul, norm_smul, Real.norm_of_nonneg hlen]
           change length A * ‖suMat (u*v)‖ = _
           rw [h]; ring

private theorem chord_mul (u v a b : gaugeGroup.image) :
    linkChord (u*v) (a*b) ≤ linkChord u a + linkChord v b := by
  have hq (k : gaugeGroup.image) : suMat k ∈ quaternionAlgebra := k.prop
  change ‖suMat u*suMat v-suMat a*suMat b‖ ≤ _
  rw [show suMat u*suMat v-suMat a*suMat b = (suMat u-suMat a)*suMat v + suMat a*(suMat v-suMat b)
      by rw [sub_mul, mul_sub]; abel]
  apply (norm_add_le _ _).trans_eq
  rw [(norm_mul_unit (quaternionAlgebra.sub_mem (hq u) (hq a)) v).1,
      (norm_mul_unit (quaternionAlgebra.sub_mem (hq v) (hq b)) a).2]
  rfl

private theorem chord_traverse {l : ℕ+} (U V : Configuration gaugeGroup l) (k : Edge l × Bool) :
    linkChord (traverse U k) (traverse V k) = linkChord (U k.1) (V k.1) := by
  rcases k with ⟨i, rev⟩
  cases rev
  · rfl
  · change ‖(suMat (U i)).conjTranspose - (suMat (V i)).conjTranspose‖ = _
    rw [← Matrix.conjTranspose_sub, Matrix.frobenius_norm_conjTranspose]
    rfl

/-- Changing neighboring links changes the actual staple by at most the sum of
their chords, counted with the multiplicities of the periodic plaquettes. -/
theorem staple_perturbation {l : ℕ+} (hl : 1 < l.val) (U V : Configuration gaugeGroup l)
    (e : Edge l) :
    ‖stapleMatrix U e - stapleMatrix V e‖ ≤
      ∑ i ∈ incidences e, linkChord (U (neighbor e i.1 i.2).1) (V (neighbor e i.1 i.2).1) := by
  let A := Function.update U e 1
  let B := Function.update V e 1
  unfold stapleMatrix
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [incidences, Finset.sum_product]
  apply Finset.sum_le_sum
  intro p hp
  change linkChord (staple A e p) (staple B e p) ≤ _
  rw [staple_eq_neighbor_product, staple_eq_neighbor_product]
  let a := fun j : Fin 3 => traverse A (neighbor e p j)
  let b := fun j : Fin 3 => traverse B (neighbor e p j)
  have hdiff (j : Fin 3) : linkChord (a j) (b j) =
      linkChord (U (neighbor e p j).1) (V (neighbor e p j).1) := by
    rw [show linkChord (a j) (b j) = _ from chord_traverse A B (neighbor e p j)]
    simp only [A, B, Function.update_of_ne (neighbor_ne_self hl hp j)]
  have h₁ := chord_mul (a 0*a 1) (a 2) (b 0*b 1) (b 2)
  have h₂ := chord_mul (a 0) (a 1) (b 0) (b 1)
  apply h₁.trans
  rw [Fin.sum_univ_three, ← hdiff, ← hdiff, ← hdiff]
  linarith

/-- The normalized Wilson action sampled along the link uses an actual SU(2) pole,
including when the external field vanishes. -/
theorem su2_field_pole {l : ℕ+} (β : ℝ) (U : Configuration gaugeGroup l) (e : Edge l) :
    ∃ K : gaugeGroup.image, ∀ v : gaugeGroup.image,
      β * fieldProjection U e v = fieldStrength β U e * (suMat (v*K) 0 0).re := by
  let A : M := stapleMatrix U e
  have ha : A ∈ quaternionAlgebra :=
    quaternionAlgebra.sum_mem fun p _ => (staple (Function.update U e 1) e p).prop
  obtain ⟨K,hK⟩ := polar ha
  refine ⟨K, fun v => ?_⟩
  have hlen : ‖A‖ / Real.sqrt 2 = length A := by
    rw [frobenius_eq ha]
    field_simp
  have hproj : (suMat (v*K)).trace.re / 2 = (suMat (v*K) 0 0).re := by
    have hq : suMat (v*K) ∈ quaternionAlgebra := (v*K).prop
    have hdiag : suMat (v*K) 1 1 = star (suMat (v*K) 0 0) := hq.1
    change (suMat (v*K)).trace.re / 2 = (suMat (v*K) 0 0).re
    simp [Matrix.trace, Fin.sum_univ_two, hdiag]
  change β * ((suMat v * A).trace.re / 2) =
    (β*(‖A‖/Real.sqrt 2))*_
  rw [hlen]
  have ht : (suMat v*A).trace.re = length A * (suMat (v*K)).trace.re := calc
    _ = (suMat v * (length A • suMat K)).trace.re := congrArg (fun B : M => (suMat v * B).trace.re) hK
    _ = _ := by rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]; rfl
  rw [ht, ← hproj]
  change β * (length A * (suMat (v*K)).trace.re / 2) = β * length A * ((suMat (v*K)).trace.re / 2)
  ring

/-- Direct finite-volume SU(2) Wilson specialization. The first conclusion is the
full Wilson law at the selected link. Its tilt is the scalar part of v*K times the
actual field strength. The second bounds the sum of trial speeds over all oriented
plaquette incidences, uniformly in every configuration and every unit direction.
It does not identify this sum with the metric W₂ interdependence matrix. -/
theorem su2_wilson_degree18 {l : ℕ+} (hl : 1 < l.val) {β : ℝ} (hb : 0 ≤ β)
    (hβ : β < Real.sqrt 3/9) (haar : Measure gaugeGroup.image) (e : Edge l) :
    let prior := Measure.pi fun _ : Edge l => haar
    let Z := ∫ U, Real.exp (-β * wilsonEnergy U) ∂prior
    ∃ pole : Configuration gaugeGroup l → gaugeGroup.image,
      (∀ U v, pole (Function.update U e v) = pole U) ∧
      (wilsonLaw gaugeGroup l β haar = prior.withDensity (fun U => ENNReal.ofReal
        (Real.exp (-β*(wilsonEnergy (Function.update U e 1) + fieldProjection U e 1)) *
         Real.exp (fieldStrength β U e * (suMat (U e * pole U) 0 0).re) / Z))) ∧
      ∀ (U : Configuration gaugeGroup l) (c s : Face l × Fin 3 → ℝ),
        (∀ i ∈ incidences e, c i ^ 2 + s i ^ 2 = 1) →
        (∑ i ∈ incidences e, β*Real.sqrt
          (c i ^ 2 * parallelEnergy (fieldStrength β U e) +
           s i ^ 2 * transverseEnergy (fieldStrength β U e))) < 1 := by
  classical
  choose raw hraw using fun (U : Configuration gaugeGroup l) => su2_field_pole β U e
  let pole := fun U => raw (Function.update U e 1)
  have hPole (U : Configuration gaugeGroup l) (v : gaugeGroup.image) :
      β * fieldProjection U e v = fieldStrength β U e * (suMat (v*pole U) 0 0).re := by
    simpa only [pole, fieldProjection, fieldStrength, stapleMatrix, Function.update_idem]
      using hraw (Function.update U e 1) v
  refine ⟨pole, fun U v => by simp [pole, Function.update_idem], ?_, ?_⟩
  · rw [wilsonLaw_one_link_factorization hl β haar e]
    simp_rw [hPole]
  · intro U c s hu
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hmax : β ≤ 7/25 := by nlinarith
    calc _ ≤ ∑ _i ∈ incidences e, β * (1/(2*Real.sqrt 3)) :=
           Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
             (OneLinkTransport.s3_w2_orthogonality_bound hmax (fieldStrength_mem hb U e) (hu i hi)) hb
         _ = 18*(1/(2*Real.sqrt 3))*β := by simp [incidence_count hl]; ring
         _ < 1 := WilsonPolymer.su2_4d_w2_dobrushin_window hβ

/-- Normalized Haar probability measure on the concrete compact fundamental group. -/
def su2Haar : Measure gaugeGroup.image := Measure.haarMeasure ⊤

instance : su2Haar.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
instance : IsProbabilityMeasure su2Haar := by
  constructor
  change Measure.haarMeasure (G := gaugeGroup.image) ⊤ Set.univ = 1
  rw [← TopologicalSpace.PositiveCompacts.coe_top]
  exact Measure.haarMeasure_self

/-- Wilson resampling measure from the energy with the surrounding links held fixed. -/
def heatBath {l : ℕ+} (β : ℝ) (U : Configuration gaugeGroup l) (e : Edge l) :=
  su2Haar.tilted fun v => -β * wilsonEnergy (Function.update U e v)

theorem heatBath_eq_tilt {l : ℕ+} (hl : 1 < l.val) (β : ℝ)
    (U : Configuration gaugeGroup l) (e : Edge l) :
    ∃ K : gaugeGroup.image, heatBath β U e =
      su2Haar.tilted (fun v => fieldStrength β U e * (suMat (v*K) 0 0).re) := by
  obtain ⟨K,hK⟩ := su2_field_pole β U e
  refine ⟨K,?_⟩
  let C := Real.exp (-β*(wilsonEnergy (Function.update U e 1)+fieldProjection U e 1))
  let w := fun v : gaugeGroup.image => Real.exp (fieldStrength β U e * (suMat (v*K) 0 0).re)
  have hw : (fun v => Real.exp (-β * wilsonEnergy (Function.update U e v))) = fun v => C*w v := by
    funext v
    dsimp [C,w]
    rw [← Real.exp_add, ← hK]
    congr 1
    linear_combination -β * one_link_energy_difference hl U e v
  unfold heatBath Measure.tilted
  rw [hw, integral_const_mul]
  congr 1
  funext v
  apply congrArg ENNReal.ofReal
  change Real.exp (-β * wilsonEnergy (Function.update U e v)) / (C * ∫ a, w a ∂su2Haar) =
    w v / ∫ a, w a ∂su2Haar
  rw [show Real.exp (-β * wilsonEnergy (Function.update U e v)) = C*w v from congrFun hw v]
  exact mul_div_mul_left _ _ (Real.exp_pos _).ne'

theorem heatBath_probability {l : ℕ+} (hl : 1 < l.val)
    (β : ℝ) (U : Configuration gaugeGroup l) (e : Edge l) : IsProbabilityMeasure (heatBath β U e) := by
  obtain ⟨K,h⟩ := heatBath_eq_tilt hl β U e
  rw [h]
  apply isProbabilityMeasure_tilted
  have hc : Continuous (fun v : gaugeGroup.image => Real.exp (fieldStrength β U e * (suMat (v*K) 0 0).re)) := by
    have hmat : Continuous suMat := continuous_subtype_val.comp continuous_subtype_val
    have entry : Continuous (fun m : M => m 0 0) := (continuous_apply _).comp (continuous_apply _)
    exact Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp
      (entry.comp (hmat.comp (continuous_mul_const K)))))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A concrete coupling strictly above 0.19, on every nondegenerate periodic volume.
The heat-bath tilt and its subunit trial row use the same Wilson staple field. -/
theorem su2_wilson_at_0192 {l : ℕ+} (hl : 1 < l.val)
    (U : Configuration gaugeGroup l) (e : Edge l) :
    let β : ℝ := 24/125
    let r := fieldStrength β U e
    (∃ K : gaugeGroup.image, heatBath β U e =
      su2Haar.tilted (fun v => r * (suMat (v*K) 0 0).re)) ∧
    ∀ c s : Face l × Fin 3 → ℝ, (∀ i ∈ incidences e, c i^2 + s i^2 = 1) →
      (∑ i ∈ incidences e, β*Real.sqrt (c i^2*parallelEnergy r + s i^2*transverseEnergy r)) < 1 := by
  refine ⟨heatBath_eq_tilt hl _ U e, ?_⟩
  obtain ⟨_, _, _, h⟩ := su2_wilson_degree18 hl (by norm_num) strict_witness.2 su2Haar e
  exact h U

#print axioms staple_perturbation
#print axioms neighbor_ne_self
#print axioms heatBath_probability
#print axioms heatBath_eq_tilt
#print axioms su2_wilson_at_0192

#print axioms period_one_plaquette
#print axioms incidence_count
#print axioms su2_field_pole
#print axioms su2_wilson_degree18

#print axioms one_link_energy_difference
#print axioms wilsonLaw_one_link_factorization
#print axioms periodic_trial_row_lt_one
#print axioms strict_witness

end
end YangMills.PeriodicWilson
