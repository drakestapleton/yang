# UFBI Check #2: Audit of `yang-mills-group/OpenAI-YM-20261028` Lean 4 Construction

**Target audited:** [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028) (`main`), specifically:
- `PublicTheory.lean` (325 lines)
- `ChallengeSpec.lean` (190 lines)
- `HierarchyBridge.lean` (134 lines)
- `PublicWilson.lean` (92 lines)

**Question:** Is the Uniform Finite-Box Insensitivity (UFBI) mass-gap strategy structurally compatible with `OpenAI-YM-20261028`'s actual Lean 4 interface (`Hierarchy.Character`, `Hierarchy.phaseMeasure`, `EnergyMomentumMeasure.projection`, `W0`), or is it dead-on-arrival?

---

## Verdict: **COMPATIBLE — Direct Structural Fit (Two Exact Open Seams)**

UFBI is **not** dead-on-arrival against `OpenAI-YM-20261028`. In fact, `OpenAI-YM-20261028`'s public theorem `JointExistence` (`ChallengeSpec.lean:186–188`) leaves **two exact mathematical seams** where a uniform continuum UFBI bound plugs directly into their Lean types:

### Seam 1: `Hierarchy.Character` and `Hierarchy.phaseMeasure` (`ChallengeSpec.lean:34–41, 124–134`; `HierarchyBridge.lean:34–37`)

In `OpenAI-YM-20261028`, the infinite-volume Wilson continuum limit (`T.correlation none`) is **not** proved to be a single pure phase. Instead, `Hierarchy` constructs a compact metric space of extremal phases `Character := F.α.space.X` equipped with a full-support Borel probability measure `phaseMeasure := F.α.space.μ`:

```lean
-- ChallengeSpec.lean:34-41, 124-134
Character : Type
[characterMetric : MetricSpace Character]
[characterCompact : CompactSpace Character]
phaseMeasure : Measure Character
selected : Character
correlation {n : ℕ} : Option Character → (Fin n → Σ d, Field d) → Points n → ℂ

-- Reconstructed:
normalized : IsProbabilityMeasure T.phaseMeasure
fullSupport : T.phaseMeasure.IsOpenPosMeasure
mixture : (∫ i, T.correlation (some i) a x ∂T.phaseMeasure) = T.correlation none a x
```

`W0.uniqueVacuum` is then obtained **only after selecting one extremal phase `T.selected : Character`** (`ChallengeSpec.lean:138`: `T.continuation v (imaginaryTimes x) ... = T.correlation (some T.selected) v x`).

**How UFBI acts on Seam 1:**
- `Character` / `phaseMeasure` is the continuum extremal-Gibbs (Choquet) decomposition of boundary-condition-dependent infinite-volume limits.
- A uniform continuum UFBI bound on smeared local gauge-invariant `CentralObs` observables (whose span generates the local Wilson algebra via `T.represents : Surjective T.project`, `ChallengeSpec.lean:123`) implies **triviality of the tail $\sigma$-algebra**, forcing every separated correlation `T.correlation (some i) a x` to be independent of `i : Character`.
- Combined with `fullSupport` and `characterContinuity` (`ChallengeSpec.lean:125, 131–132`), UFBI collapses the phase decomposition so that the unselected Wilson limit `T.correlation none` equals the selected pure phase `T.correlation (some T.selected)` (and up to phase equivalence, `phaseMeasure` concentrates on a single physical phase).

---

### Seam 2: `EnergyMomentumMeasure.projection` and `W0.positiveEnergy` (`PublicTheory.lean:64–68, 180–200, 270–279`)

In `PublicTheory.lean`, the joint energy–momentum spectral projection is:

```lean
-- PublicTheory.lean:64-66, 180-200
def forwardCone : Set Spacetime := {x | ‖spatial x‖ ≤ time x}
def minkowskiSquare (x : Spacetime) : ℝ := time x ^ 2 - ‖spatial x‖ ^ 2

structure EnergyMomentumMeasure (H : HilbertSpace) where
  projection : Set Spacetime → H.Operator
  ...
  diagonal : H.carrier → Measure Spacetime
  finite (state : H.carrier) : IsFiniteMeasure (diagonal state)
  diagonalIdentity {region : Set Spacetime} (measurable : MeasurableSet region)
      (state : H.carrier) :
    ↑((diagonal state).real region) = inner ℂ state (projection region state)
```

And `W0` (`PublicTheory.lean:270–278`) proves **only** positivity of energy and uniqueness of the vacuum:

```lean
structure W0 (theory : WightmanTheory H Labels) : Prop where
  spectralRepresentation : ∀ state : H.carrier, ∀ momentum : Spacetime,
    charFun (theory.energyMomentum.diagonal state) momentum =
      inner ℂ state (theory.translations.operator momentum state)
  positiveEnergy :
    theory.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H.carrier) :
    (∀ x, theory.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • theory.fields.vacuum.1 = state
```

**Exact Clay Mass-Gap Target in `OpenAI-YM-20261028`'s Types:**

`W0.positiveEnergy` excludes `forwardConeᶜ`, leaving the open region $\{p \in \text{forwardCone} \mid p \neq 0 \land \text{minkowskiSquare } p < \Delta^2\}$ unconstrained. A strict spectral mass gap $\Delta > 0$ on `T.theory` is precisely:

```lean
def HasMassGap (theory : WightmanTheory H Labels) (Δ : ℝ) : Prop :=
  0 < Δ ∧
  theory.energyMomentum.projection
    {p : Spacetime | p ∈ forwardCone ∧ p ≠ 0 ∧ minkowskiSquare p < Δ ^ 2} = 0
```

(Equivalently, by Poincaré covariance `W2` and `W0.positiveEnergy`, it suffices to rule out the energy strip `0 < time p < Δ`: `theory.energyMomentum.projection {p | 0 < time p ∧ time p < Δ} = 0`, because any non-zero $p \in \text{forwardCone}$ with $p^2 < \Delta^2$ can be boosted into $0 < p_0 < \Delta$.)

---

### Exact Mapping from Our `proofs/UfbiMassGap.lean` onto `OpenAI-YM-20261028`

| `yang/proofs/UfbiMassGap.lean` | `OpenAI-YM-20261028` (`PublicTheory.lean` / `ChallengeSpec.lean`) | Status |
| --- | --- | --- |
| `TransferModel.specMass` / `evals` (discrete spectral weights) | `EnergyMomentumMeasure.diagonal state` pushed forward by `YangMills.time : Spacetime → ℝ` (finite positive Borel measure on $[0, \infty)$ by `W0.positiveEnergy`) | Exact continuous-measure analogue |
| `TransferModel.twoPoint t` ($\sum_k w_k e^{-E_k t}$) | Euclidean 2-point function `T.correlation (some T.selected) ![a, a] (timePair r)` linked via `Reconstructed.analytic`, `root`, `boundary` (`ChallengeSpec.lean:135–143`) and Laplace transform of `(diagonal state).map time` (`W0.spectralRepresentation`) | Exact Laplace-transform bridge |
| `ufbi_implies_connected_clustering` | Uniform boundary insensitivity on finite-volume `WilsonFamily.finiteMoment` (`PublicWilson.lean:54`) surviving the `Converges` mesh + volume limit (`PublicWilson.lean:85`) | Conditional on proving continuum UFBI bound (open) |
| `exponential_decay_implies_spectral_gap` | For every centered vector $\psi \perp \Omega$, if $\int_{[0,\infty)} e^{-r E}\, d\nu_\psi(E) \le C e^{-\Delta r}$ for all $r > 0$, then $\nu_\psi((0, \Delta)) = 0$; via `diagonalIdentity` and cyclic vacuum (`W1.domain.cyclicVacuum`), `projection {p \| 0 < time p < Δ} = 0` | Ready to formalize directly against `PublicTheory.lean` once Mathlib is linked |

---

## Key Takeaway for the `yang` Program

1. **No architectural mismatch:** `OpenAI-YM-20261028` already provides the heavy UV continuum existence, Wightman reconstruction (`W0`–`W3`), separated OPE, and non-freeness (`TraceTest`).
2. **One critical subtlety flagged by `PublicWilson.lean:20–54` & `ChallengeSpec.lean:12–22`:** In `OpenAI-YM-20261028`, lattice insertions (`C.insertion N p v x`) have a **fixed stencil in lattice units** (`WilsonRegularity`), renormalized as $a \to 0$ via `C.project : C.Token → (Σ d, Field d)` and smeared against **physical continuum test functions** (`WilsonFamily.smear`, `SeparatedTest n`). That directly mirrors the Check #4 $\to$ Check #5 lesson: **UFBI must be formulated on physically scaled/smeared observables (fixed physical support $\ell_{\text{obs}}$, normalized by bulk variance $\sigma_{\text{bulk}}$), never on unnormalized fixed-lattice-unit loops that vanish as $a^4$ when $a \to 0$.**
