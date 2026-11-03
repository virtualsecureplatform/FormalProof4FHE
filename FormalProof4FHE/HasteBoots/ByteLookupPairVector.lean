module

public import FormalProof4FHE.HasteBoots.ObservedOptionalVector
public import FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal

@[expose] public section

/-!
# Repeated raw-byte lookup pairs with complete work observations

Each repetition calls the actual byte-backed pair program afresh. Suspension
stops the vector and preserves every completed pair and started raw trial.
The count is a true repetition count, separate from packing or field degree.
No independence between the two coordinates of any one pair is assumed.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.ByteLookupPairVector

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width count size : ℕ} [Module (ZMod p) K] [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

def program (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) :
    ProbComp (ObservedOptionalVector.Result (K × K) (ByteLookupPairSampler.Result p degree K) repetitions) :=
  ObservedOptionalVector.program (ByteLookupPairSampler.program basis table hashDepth inner outer) ByteLookupPairSampler.Result.value repetitions

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Exact all-pass mass is the actual finite successful pair mass raised to
the true number of fresh calls; suspended vectors never pass. -/
theorem probability (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) (event : K × K → Prop) :
    Pr{let result ← program basis table hashDepth inner outer repetitions}[result.values.elim False (ObservedOptionalVector.All event)] =
      Pr{let result ← ByteLookupPairSampler.program basis table hashDepth inner outer}[result.value.elim False event] ^ repetitions :=
  ObservedOptionalVector.probability _ _ _ _

/-- Both original lookup losses amplify at the repetition count. No retry
budget, pair-coordinate independence or finite uniform-completion law enters. -/
theorem finite_bound {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (hashDepth inner outer repetitions : ℕ) :
    Pr{let result ← program basis table hashDepth inner outer repetitions}[
      result.values.elim False (ObservedOptionalVector.All (TupleLookupPair.Passes sources table multiplicities))] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  rw [probability]
  exact pow_le_pow_left' (ByteLookupPairSampler.single_bound valid basis sources table multiplicities enough bad small hashDepth inner outer) repetitions

/-- Every common depth is an approximation to the unbounded sequential byte
program, and the supremum uses them all rather than imposing a native cap. -/
def allEventProbability (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (repetitions : ℕ) (event : K × K → Prop) : ENNReal :=
  ⨆ n, Pr{let result ← program basis table n n n repetitions}[result.values.elim False (ObservedOptionalVector.All event)]

/-- Unbounded repeated all-event law follows from fresh repeated syntax and
the full joint single-pair law, rather than an independence certificate. -/
theorem law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (repetitions : ℕ) (event : K × K → Prop) :
    allEventProbability basis table repetitions event =
      Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] ^ repetitions := by
  unfold allEventProbability
  simp_rw [probability]
  rw [ByteLookupPairDiagonal.iSup_power]
  · rw [ByteLookupPairDiagonal.law valid basis]
  · intro i j ordered
    exact ByteLookupPairDiagonal.probability_mono valid basis table event i i i j j j ordered ordered ordered

/-- Completing all requested byte-backed pairs has eventual mass one. -/
theorem completion_probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    allEventProbability basis table repetitions (fun _ => True) = 1 := by
  rw [law valid basis, TupleLookupPair.sample_total table enough, one_pow]

/-- The old all-pass repeated lookup law is recovered by actual byte sampling. -/
theorem lookup_law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K) (repetitions : ℕ) :
    allEventProbability basis table repetitions (TupleLookupPair.Passes sources table multiplicities) =
      Pr{let pairs ← TupleLookupPair.repeats (K := K) table repetitions}[TupleLookupPair.AllPass sources table multiplicities pairs] := by
  rw [law valid basis, TupleLookupPair.repeated_probability]

theorem bound {char : ℕ} [CharP K char] (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char) (repetitions : ℕ) :
    allEventProbability basis table repetitions (TupleLookupPair.Passes sources table multiplicities) ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  rw [lookup_law valid basis]
  exact TupleLookupPair.repeated_bound sources table multiplicities bad small repetitions

def consumedBytes {repetitions : ℕ}
    (result : ObservedOptionalVector.Result (K × K) (ByteLookupPairSampler.Result p degree K) repetitions) : ℕ :=
  ObservedOptionalVector.consumed ByteLookupPairWork.consumedBytes result

def expectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) : ENNReal :=
  ObservedOptionalVector.expectedCost (ByteLookupPairSampler.program basis table hashDepth inner outer)
    ByteLookupPairSampler.Result.value ByteLookupPairWork.consumedBytes repetitions

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- The actual finite work includes a final suspended pair, after all earlier
successful pairs. The completion sum is derived from that control flow. -/
theorem expectedBytes_formula (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ) :
    expectedBytes basis table hashDepth inner outer repetitions =
      ByteLookupPairWork.expectedBytes basis table hashDepth inner outer *
        ByteReciprocalLimit.geometricSum
          (Pr{let result ← ByteLookupPairSampler.program basis table hashDepth inner outer}[result.value.elim False (fun _ => True)]) repetitions :=
  ObservedOptionalVector.expectedCost_formula _ _ _ _

theorem work_monotone (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (repetitions : ℕ) :
    Monotone (fun n => expectedBytes basis table n n n repetitions) := by
  intro i j ordered
  simp only [expectedBytes_formula, ByteReciprocalLimit.geometricSum]
  have work := ByteLookupPairDiagonal.work_mono valid basis table i i i j j j ordered ordered ordered
  have completion := ByteLookupPairDiagonal.probability_mono valid basis table (fun _ => True) i i i j j j ordered ordered ordered
  gcongr

/-- The supremum includes every raw byte spent in each started repetition. -/
def totalExpectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (repetitions : ℕ) : ENNReal := ⨆ n, expectedBytes basis table n n n repetitions

/-- All repetitions eventually complete, so unbounded work is exactly the
true repetition count times the single pair's domain-dependent byte mean. -/
theorem totalExpectedBytes_eq (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    totalExpectedBytes basis table repetitions = ByteLookupPairWork.totalExpectedBytes basis table * (repetitions : ENNReal) := by
  by_cases zero : repetitions = 0
  · subst repetitions
    simp [totalExpectedBytes, expectedBytes, ObservedOptionalVector.expectedCost_zero]
  · have complete := ByteLookupPairDiagonal.probability_tends valid basis table (fun _ => True)
    rw [TupleLookupPair.sample_total table enough] at complete
    have sums := ByteReciprocalLimit.geometric_tends complete repetitions
    have sums' : Filter.Tendsto
        (fun n => ByteReciprocalLimit.geometricSum
          (Pr{let result ← ByteLookupPairSampler.program basis table n n n}[result.value.elim False (fun _ => True)]) repetitions)
        Filter.atTop (nhds (repetitions : ENNReal)) := by
      simpa only [ByteReciprocalLimit.geometricSum, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using sums
    have total := ENNReal.Tendsto.mul (ByteLookupPairDiagonal.work_tends valid basis table) (Or.inr (by simp))
      sums' (Or.inl (by exact_mod_cast zero))
    apply tendsto_nhds_unique (tendsto_atTop_iSup (work_monotone valid basis table repetitions))
    simpa only [expectedBytes_formula] using total

theorem totalExpectedBytes_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    totalExpectedBytes basis table repetitions ≤
      (ByteReciprocalLimit.fieldCost p degree *
        (1 + (Fintype.card K : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal))) * (repetitions : ENNReal) := by
  rw [totalExpectedBytes_eq valid basis table enough]
  exact mul_le_mul_left (ByteLookupPairWork.totalExpectedBytes_bound valid basis table) _

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Each completed coordinate is an actual successful pair with nonzero
offset; no fallback value is needed to inhabit the typed verifier interface. -/
theorem returned_nonzero (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ)
    (result : ObservedOptionalVector.Result (K × K) (ByteLookupPairSampler.Result p degree K) repetitions)
    (supported : result ∈ support (program basis table hashDepth inner outer repetitions))
    (values : Fin repetitions → K × K) (returned : result.values = some values) :
    ∀ index, (values index).2 ≠ 0 := by
  apply ObservedOptionalVector.returned_property _ _ (fun pair : K × K => pair.2 ≠ 0) _ repetitions result supported values returned
  intro first reached pair value
  exact (ByteLookupPairSampler.returned_allowed basis table hashDepth inner outer first reached pair.1 pair.2 value).2.1

section SharedRuntime

variable {Cfg Input Digest Payload Later : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Later shared execution may inspect every completed and partial trace.
Its actual hashes remain, while a fixed earlier all-pass event stays bounded. -/
theorem retained_bound {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (hashDepth inner outer repetitions : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (next : ObservedOptionalVector.Result (K × K) (ByteLookupPairSampler.Result p degree K) repetitions →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PrivateSampling.embed Cfg Input Digest (program basis table hashDepth inner outer repetitions)) next)).run state}[
        outcome.1.1.values.elim False (ObservedOptionalVector.All (TupleLookupPair.Passes sources table multiplicities))] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (program basis table hashDepth inner outer repetitions)) next state
    (fun earlier => earlier.values.elim False (ObservedOptionalVector.All (TupleLookupPair.Passes sources table multiplicities)))
  have sampled := finite_bound valid basis sources table multiplicities enough bad small hashDepth inner outer repetitions
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_map] using sampled)

end SharedRuntime

end

end FormalProof4FHE.HasteBoots.ByteLookupPairVector
