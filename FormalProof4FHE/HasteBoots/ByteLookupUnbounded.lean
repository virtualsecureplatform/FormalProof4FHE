module

public import FormalProof4FHE.HasteBoots.ByteLookupTraceOrder
public import FormalProof4FHE.HasteBoots.CompletedContinuation

@[expose] public section

/-!
# The unbounded ideal-byte lookup observation measure

All operational depths define increasing completed-observation measures on
the actual typed vector and its raw traces. Their limit is countably additive
and has total mass one when the accepted reciprocal domain is nonempty.
Arbitrary later private-coin execution may inspect the full observation.
Production FS/XOF/Rust and expected whole-protocol hash work remain separate.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ByteLookupUnbounded

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width count size repetitions : ℕ} [Module (ZMod p) K] [DecidableEq K]

local instance : MeasurableSpace (ByteLookupPairTyped.Sample p degree K repetitions) := ⊤

def steps (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions n : ℕ) :=
  ByteLookupPairTyped.sample basis table n n n repetitions

def complete (observed : ByteLookupPairTyped.Sample p degree K repetitions) : Prop := observed.values ≠ none

theorem grows (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions i j : ℕ)
    (ordered : i ≤ j) : CompletedObservation.LE (steps basis table repetitions i) (steps basis table repetitions j) complete :=
  ByteLookupTraceOrder.typed basis table repetitions ordered ordered ordered

/-- A countably additive measure on complete typed vectors and all their raw
records, constructed from the actual byte programs at all depths. -/
def measure (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions : ℕ) :
    Measure (ByteLookupPairTyped.Sample p degree K repetitions) :=
  CompletedObservationLimit.measure (steps basis table repetitions) complete (grows basis table repetitions)

theorem event_tends (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions : ℕ)
    (event : ByteLookupPairTyped.Sample p degree K repetitions → Prop) :
    Filter.Tendsto (fun n => Pr{let observed ← steps basis table repetitions n}[complete observed ∧ event observed])
      Filter.atTop (nhds (measure basis table repetitions {observed | event observed})) :=
  CompletedObservationLimit.event_tends _ _ _ _

/-- The common depth is cofinal in all independent operational depths; it
neither imposes a retry cap nor equates distinct finite approximations. -/
theorem all_depths (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions : ℕ)
    (event : ByteLookupPairTyped.Sample p degree K repetitions → Prop) :
    measure basis table repetitions {observed | event observed} =
      ⨆ outer, ⨆ inner, ⨆ hashDepth,
        Pr{let observed ← ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions}[complete observed ∧ event observed] := by
  rw [measure, CompletedObservationLimit.measure_apply]
  have cofinal := ByteLookupPairDiagonal.iSup_diagonal
    (fun h i o => Pr{let observed ← ByteLookupPairTyped.sample basis table h i o repetitions}[complete observed ∧ event observed])
    (fun _ _ _ _ _ _ hh hi ho => ByteLookupTraceOrder.typed basis table repetitions hh hi ho event)
  simpa only [steps, Set.mem_ofPred_eq] using cofinal

theorem incomplete_zero (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions : ℕ) :
    measure basis table repetitions {observed | observed.values = none} = 0 := by
  simpa only [measure, complete, not_not] using
    CompletedObservationLimit.incomplete_zero (steps basis table repetitions) complete (grows basis table repetitions)

/-- Later execution may depend on every retained raw observation. The joint
measure includes its actual result rather than substituting a marginal law. -/
def joint {B : Type} (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions : ℕ)
    (next : ByteLookupPairTyped.Sample p degree K repetitions → ProbComp B) :
    @Measure (ByteLookupPairTyped.Sample p degree K repetitions × Option B) ⊤ :=
  CompletedContinuation.measure (steps basis table repetitions) complete (grows basis table repetitions) next

theorem earlier_marginal {B : Type} (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (repetitions : ℕ) (next : ByteLookupPairTyped.Sample p degree K repetitions → ProbComp B)
    (event : ByteLookupPairTyped.Sample p degree K repetitions → Prop) :
    joint basis table repetitions next {outcome | event outcome.1} = measure basis table repetitions {observed | event observed} :=
  CompletedContinuation.earlier_marginal _ _ _ _ _

variable [Fintype K] [SampleableType K] [NeZero p]

/-- Successful mass tends to one for the entire trace, not only for its
projected value law. No finite successful-mass normalization is used. -/
theorem completion_sup (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    (⨆ n, Pr{let observed ← steps basis table repetitions n}[complete observed]) = 1 := by
  have finite (n : ℕ) : Pr{let observed ← steps basis table repetitions n}[complete observed] =
      Pr{let raw ← ByteLookupPairVector.program basis table n n n repetitions}[
        raw.values.elim False (ObservedOptionalVector.All (fun _ => True))] := by
    rw [← ByteLookupPairTyped.sample_raw basis table n n n repetitions, prEvent_map]
    apply prEvent_congr
    intro observed
    have same : observed.raw.values.elim False (ObservedOptionalVector.All (fun _ => True)) ↔ observed.raw.values ≠ none := by
      cases tag : observed.raw.values <;> simp [ObservedOptionalVector.All]
    exact (ByteLookupTraceOrder.typed_complete observed).symm.trans same.symm
  simp_rw [finite]
  exact ByteLookupPairVector.completion_probability valid basis table enough repetitions

/-- The unbounded raw-byte observation law is a probability measure, with
partial outcomes excluded only in the limit where their mass is zero. -/
theorem probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    IsProbabilityMeasure (measure basis table repetitions) :=
  CompletedObservationLimit.probability _ _ _ (completion_sup valid basis table enough repetitions)

/-- Almost-sure completed lookup sampling followed by arbitrary total private
execution yields a probability measure on the full joint outcomes. -/
theorem joint_probability {B : Type} (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ)
    (next : ByteLookupPairTyped.Sample p degree K repetitions → ProbComp B) :
    IsProbabilityMeasure (joint basis table repetitions next) :=
  CompletedContinuation.probability _ _ _ _ (completion_sup valid basis table enough repetitions)

/-- The lookup failure bound holds for the actual unbounded complete-trace
measure, even when an event may expose all retained raw records. -/
theorem lookup_bound {char : ℕ} [CharP K char] (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (repetitions : ℕ) :
    measure basis table repetitions {observed | observed.values.elim False (LookupPairVector.AllPass sources table multiplicities)} ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  apply CompletedObservationLimit.event_bound
  intro n
  exact (prEvent_mono _ _ _ (fun _ present => present.2)).trans
    (ByteLookupPairTyped.finite_bound valid basis sources table multiplicities enough bad small n n n repetitions)

/-- Adaptive later work retains the same proved earlier lookup failure bound;
the entire joint result and raw observations stay in the probability model. -/
theorem joint_lookup_bound {B : Type} {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (repetitions : ℕ) (next : ByteLookupPairTyped.Sample p degree K repetitions → ProbComp B) :
    joint basis table repetitions next {outcome | outcome.1.values.elim False (LookupPairVector.AllPass sources table multiplicities)} ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  exact (earlier_marginal basis table repetitions next
    (fun observed => observed.values.elim False (LookupPairVector.AllPass sources table multiplicities))).trans_le
      (lookup_bound valid basis sources table multiplicities enough bad small repetitions)

end

end FormalProof4FHE.HasteBoots.ByteLookupUnbounded
