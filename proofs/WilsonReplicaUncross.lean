-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaFreeShell

namespace YangMills.PeriodicWilson.PinnedFrame
open WilsonPolymer
noncomputable section
variable {l : ℕ+} (P : PinnedFrame l)

/-- Global complementation can align either mask without changing any split face. -/
theorem freeBoundary_complement (m : Edge l → Bool) :
    P.freeBoundary (fun e => !m e) = P.freeBoundary m := by
  classical
  ext p
  simp only [freeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
  apply not_congr
  constructor <;> rintro ⟨b, h⟩ <;> refine ⟨!b, fun e he => ?_⟩ <;>
    simpa using congrArg Bool.not (h e he)

private theorem freeUniform_congr_on {m n : Edge l → Bool} {p : Face l}
    (eq : ∀ e ∈ P.freeFace p, m e = n e) : P.freeUniform m p ↔ P.freeUniform n p := by
  constructor <;> rintro ⟨b, h⟩
  · exact ⟨b, fun e he => (eq e he).symm.trans (h e he)⟩
  · exact ⟨b, fun e he => (eq e he).trans (h e he)⟩

/-- On each face where at least one mask is uniform, sorting the two bits
is a fixed permutation of the two masks on all free links of that face. -/
private theorem sorted_uniformity (m n : Edge l → Bool) (p : Face l)
    (h : P.freeUniform m p ∨ P.freeUniform n p) :
    ((P.freeUniform (fun e => m e && n e) p ↔ P.freeUniform m p) ∧
     (P.freeUniform (fun e => m e || n e) p ↔ P.freeUniform n p)) ∨
    ((P.freeUniform (fun e => m e && n e) p ↔ P.freeUniform n p) ∧
     (P.freeUniform (fun e => m e || n e) p ↔ P.freeUniform m p)) := by
  rcases h with ⟨b, hb⟩ | ⟨b, hb⟩ <;> cases b
  · left; constructor <;> apply P.freeUniform_congr_on <;> intro e he <;> simp [hb e he]
  · right; constructor <;> apply P.freeUniform_congr_on <;> intro e he <;> simp [hb e he]
  · right; constructor <;> apply P.freeUniform_congr_on <;> intro e he <;> simp [hb e he]
  · left; constructor <;> apply P.freeUniform_congr_on <;> intro e he <;> simp [hb e he]

/-- Uncrossing preserves the entire set of split faces and counts each such
face in precisely one output, not necessarily in the same mask as before. -/
theorem freeBoundary_uncross (m n : Edge l → Bool)
    (hd : Disjoint (P.freeBoundary m) (P.freeBoundary n)) :
    Disjoint (P.freeBoundary (fun e => m e && n e)) (P.freeBoundary (fun e => m e || n e)) ∧
    P.freeBoundary (fun e => m e && n e) ∪ P.freeBoundary (fun e => m e || n e) =
      P.freeBoundary m ∪ P.freeBoundary n := by
  classical
  have h := (P.freeBoundary_disjoint m n).mp hd
  constructor
  · apply (P.freeBoundary_disjoint _ _).mpr
    intro p
    have sorted := P.sorted_uniformity m n p (h p)
    specialize h p
    tauto
  · ext p
    simp only [Finset.mem_union, freeBoundary, Finset.mem_filter, Finset.mem_univ, true_and]
    have sorted := P.sorted_uniformity m n p (h p)
    tauto

theorem freeBoundary_uncross_card (m n : Edge l → Bool)
    (hd : Disjoint (P.freeBoundary m) (P.freeBoundary n)) :
    (P.freeBoundary (fun e => m e && n e)).card + (P.freeBoundary (fun e => m e || n e)).card =
      (P.freeBoundary m).card + (P.freeBoundary n).card := by
  classical
  obtain ⟨hout, hu⟩ := P.freeBoundary_uncross m n hd
  rw [← Finset.card_union_of_disjoint hout, hu, Finset.card_union_of_disjoint hd]

/-- The true-link sets are nested, and sorting fixes every prescribed shared
label. Take the protected set to be both neighborhoods and vary the label by link. -/
theorem uncross_nested_labels (m n : Edge l → Bool) (s : Finset (Edge l)) (label : Edge l → Bool)
    (hm : ∀ e ∈ s, m e = label e) (hn : ∀ e ∈ s, n e = label e) :
    (∀ e, (m e && n e) = true → (m e || n e) = true) ∧
    (∀ e ∈ s, (m e && n e) = label e ∧ (m e || n e) = label e) := by
  constructor
  · intro e; cases m e <;> cases n e <;> decide
  · intro e he; simp [hm e he, hn e he]

/-- Every aligned admissible pair has a nested representative of exactly the
same total geometric cost. Concrete optimization inputs remain separate data. -/
theorem exists_nested_aligned_pair (m n : Edge l → Bool) (s : Finset (Edge l))
    (label : Edge l → Bool) (hm : ∀ e ∈ s, m e = label e) (hn : ∀ e ∈ s, n e = label e)
    (hd : Disjoint (P.freeBoundary m) (P.freeBoundary n)) :
    ∃ a b : Edge l → Bool,
      (∀ e, a e = true → b e = true) ∧
      (∀ e ∈ s, a e = label e ∧ b e = label e) ∧
      Disjoint (P.freeBoundary a) (P.freeBoundary b) ∧
      (P.freeBoundary a).card + (P.freeBoundary b).card =
        (P.freeBoundary m).card + (P.freeBoundary n).card := by
  have labels := uncross_nested_labels m n s label hm hn
  exact ⟨(fun e => m e && n e), (fun e => m e || n e),
    labels.1, labels.2, (P.freeBoundary_uncross m n hd).1, P.freeBoundary_uncross_card m n hd⟩

/-- Concrete failure without input disjointness: use the same direction-zero
mask twice on the empty-pinned side-two torus. Both sorted masks split (0,1). -/
theorem identical_split_counterexample :
    let m := fun e : Edge 2 => decide (e.2 = 0)
    ¬Disjoint ((empty 2).freeBoundary (fun e => m e && m e))
      ((empty 2).freeBoundary (fun e => m e || m e)) := by
  classical
  dsimp only
  let p : Face 2 := (0, ⟨(0, 1), by decide⟩)
  have ha : (corners p).1 ∈ (empty 2).freeFace p := by simp [freeFace, empty, faceEdges]
  have hb : (corners p).2.2.2 ∈ (empty 2).freeFace p := by simp [freeFace, empty, faceEdges]
  have split : p ∈ (empty 2).freeBoundary (fun e => decide (e.2 = 0)) := by
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rintro ⟨b, uniform⟩
    have eq := (uniform _ ha).trans (uniform _ hb).symm
    simp [p, corners] at eq
  intro hd
  exact Finset.disjoint_left.mp hd (by simpa using split) (by simpa using split)

#print axioms freeBoundary_complement
#print axioms freeUniform_congr_on
#print axioms sorted_uniformity
#print axioms freeBoundary_uncross
#print axioms freeBoundary_uncross_card
#print axioms uncross_nested_labels
#print axioms exists_nested_aligned_pair
#print axioms identical_split_counterexample
end
end YangMills.PeriodicWilson.PinnedFrame
