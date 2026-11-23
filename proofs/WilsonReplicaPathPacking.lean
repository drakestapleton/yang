-- SPDX-License-Identifier: Apache-2.0
import WilsonReplicaFreeShell

namespace YangMills.PeriodicWilson.PinnedFrame
open WilsonPolymer
noncomputable section
variable {l : ℕ+} (P : PinnedFrame l)

/-- A walk from one free link to another. Each step names a Wilson face and
both incident free links, and the shared link is literally the next start. -/
inductive FreeFacePath : Edge l → List (Face l) → Edge l → Prop where
  | nil {a} : a ∉ P.edges → FreeFacePath a [] a
  | cons {a b c p ps} : a ∈ P.freeFace p → b ∈ P.freeFace p →
      FreeFacePath b ps c → FreeFacePath a (p :: ps) c

/-- No split face is assumed: a changed label between two incident free links
contradicts uniformity, and equal labels propagate down the path. -/
theorem path_crosses_freeBoundary (m : Edge l → Bool) {a b ps}
    (path : P.FreeFacePath a ps b) (opp : m a ≠ m b) :
    ∃ p ∈ ps, p ∈ P.freeBoundary m := by
  classical
  induction path with
  | nil => exact (opp rfl).elim
  | @cons a b c p ps ha hb _ ih =>
    by_cases hab : m a = m b
    · obtain ⟨q, hq, hs⟩ := ih (fun h => opp (hab.trans h))
      exact ⟨q, List.mem_cons_of_mem _ hq, hs⟩
    · refine ⟨p, List.mem_cons_self, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rintro ⟨_, hu⟩
      exact hab ((hu a ha).trans (hu b hb).symm)

/-- A certificate for any pinned frame: only face disjointness between paths
is needed. Paths may share endpoints or revisit their own faces. The concrete
periodic tree, arcs and endpoint labels must be supplied separately. -/
theorem path_packing_le_freeBoundary (m : Edge l → Bool) {n : ℕ}
    (a b : Fin n → Edge l) (ps : Fin n → List (Face l))
    (paths : ∀ i, P.FreeFacePath (a i) (ps i) (b i))
    (opposite : ∀ i, m (a i) ≠ m (b i))
    (separate : ∀ i j, i ≠ j → ∀ p ∈ ps i, p ∉ ps j) :
    n ≤ (P.freeBoundary m).card := by
  classical
  choose f inPath inBoundary using fun i => P.path_crosses_freeBoundary m (paths i) (opposite i)
  let pick (i : Fin n) : ↥(P.freeBoundary m) := ⟨f i, inBoundary i⟩
  have inj : Function.Injective pick := by
    intro i j eq
    by_contra neq
    have same : f i = f j := congrArg Subtype.val eq
    exact separate i j neq (f i) (inPath i) (same ▸ inPath j)
  simpa using Fintype.card_le_of_injective pick inj

/-- Removing inter-path disjointness really fails. On the side-two torus
with empty pins, repeat one genuine crossing of a single (0,1) plaquette
more times than there are faces in the whole mask boundary. -/
theorem overlapping_paths_counterexample :
    ∃ (n : ℕ) (m : Edge 2 → Bool) (a b : Fin n → Edge 2) (ps : Fin n → List (Face 2)),
      (∀ i, (empty 2).FreeFacePath (a i) (ps i) (b i)) ∧
      (∀ i, m (a i) ≠ m (b i)) ∧ ¬ n ≤ ((empty 2).freeBoundary m).card := by
  let p : Face 2 := (0, ⟨(0, 1), by decide⟩)
  let a := (corners p).1
  let b := (corners p).2.2.2
  let m (e : Edge 2) : Bool := decide (e.2 = 0)
  have path : (empty 2).FreeFacePath a [p] b :=
    .cons (by simp [a, freeFace, empty, faceEdges]) (by simp [b, freeFace, empty, faceEdges])
      (.nil (by simp [empty]))
  exact ⟨((empty 2).freeBoundary m).card + 1, m, fun _ => a, fun _ => b, fun _ => [p],
    fun _ => path, fun _ => by simp [m, a, b, p, corners], Nat.not_succ_le_self _⟩

#print axioms path_crosses_freeBoundary
#print axioms path_packing_le_freeBoundary
#print axioms overlapping_paths_counterexample
end
end YangMills.PeriodicWilson.PinnedFrame
