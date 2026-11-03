module

public import FormalProof4FHE.HasteBoots.ByteReciprocalLimit
public import FormalProof4FHE.HasteBoots.TupleLookupPair

@[expose] public section

/-!
# Raw-byte tuple-hash/reciprocal pairs with their challenge-dependent domain

The first completed field value fixes the hashed public table. Only then is
the reciprocal loop run for that exact table. Both observations remain in
the result; unfinished hash sampling starts no reciprocal trial. The two
coordinates are not assumed independent, and finite completion need not have
a single challenge-independent normalization factor.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.ByteLookupPairSampler

noncomputable section

structure Result (p degree : ℕ) (K : Type) where
  value : Option (K × K)
  hashTrial : ByteReciprocalSampler.Trial p degree K
  offsetTrials : Option (OptionalRejectionLoop.Result K (ByteReciprocalSampler.Trial p degree K))

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width count size : ℕ} [Module (ZMod p) K] [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

def hashes (table : Fin size → Fin width → F) (y : K) : Fin size → K := fun index => TupleHash.hash y (table index)

def finish (first : ByteReciprocalSampler.Trial p degree K) (y : K)
    (last : OptionalRejectionLoop.Result K (ByteReciprocalSampler.Trial p degree K)) : Result p degree K :=
  ⟨last.value.map (fun r => (y, r)), first, some last⟩

def program (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ) : ProbComp (Result p degree K) := do
  let first ← ByteReciprocalSampler.step basis hashDepth
  match ByteReciprocalSampler.candidate first with
  | none => pure ⟨none, first, none⟩
  | some y => finish first y <$> ByteReciprocalSampler.program basis (hashes table y) inner outer

def valueProgram (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ) : ProbComp (Option (K × K)) :=
  OptionalUniformSequence.bindProgram
    (ByteReciprocalSampler.candidate <$> ByteReciprocalSampler.step basis hashDepth)
    (fun y => (fun result => result.value.map (fun r => (y, r))) <$>
      ByteReciprocalSampler.program basis (hashes table y) inner outer)

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Metadata erasure preserves all raw-byte queries and the suspension gate,
including the fact that the reciprocal loop is chosen after the actual y. -/
theorem value_erasure (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ) :
    (fun result => result.value) <$> program basis table hashDepth inner outer = valueProgram basis table hashDepth inner outer := by
  rw [program, valueProgram, OptionalUniformSequence.bindProgram, map_bind, bind_map_left]
  congr 1
  funext first
  cases ByteReciprocalSampler.candidate first with
  | none => simp
  | some y => simp only [finish, Functor.map_map]

def conditional (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (inner outer : ℕ) (event : K × K → Prop) (y : K) : ENNReal :=
  Pr{let result ← ByteReciprocalSampler.program basis (hashes table y) inner outer}[result.value.elim False (fun r => event (y, r))]

/-- The exact pair probability averages the true y-dependent reciprocal
prefix; no independence or uniform-completion shortcut is inserted. -/
theorem probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ) (event : K × K → Prop) :
    Pr{let result ← program basis table hashDepth inner outer}[result.value.elim False event] =
      ByteReciprocalSampler.completion p degree hashDepth *
        ∑ y : K, Pr{let value ← $ᵗ K}[value = y] * conditional basis table inner outer event y := by
  have kernel : ∀ event : K → Prop,
      Pr{let candidate ← ByteReciprocalSampler.candidate <$> ByteReciprocalSampler.step basis hashDepth}[candidate.elim False event] =
      ByteReciprocalSampler.completion p degree hashDepth * Pr{let value ← $ᵗ K}[event value] := by
    intro event
    simpa only [prEvent_map] using ByteReciprocalSampler.candidate_law valid basis hashDepth event
  have bound := OptionalUniformSequence.bind_probability
    (ByteReciprocalSampler.candidate <$> ByteReciprocalSampler.step basis hashDepth)
    (ByteReciprocalSampler.completion p degree hashDepth) kernel
    (fun y => (fun result => result.value.map (fun r => (y, r))) <$>
      ByteReciprocalSampler.program basis (hashes table y) inner outer) event
  change Pr{let result ← valueProgram basis table hashDepth inner outer}[result.elim False event] = _ at bound
  rw [← value_erasure, prEvent_map] at bound
  rw [prEvent_bind_eq_tsum, tsum_fintype] at bound
  refine bound.trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [prEvent_map]
  exact prEvent_congr _ _ _ (fun result => by cases result.value <;> rfl)

/-- The old ideal pair law has the same conditional public-table hashes. -/
theorem ideal_probability (table : Fin size → Fin width → F) (event : K × K → Prop) :
    Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] =
      ∑ y : K, Pr{let value ← $ᵗ K}[value = y] *
        Pr{let r ← ReciprocalDetection.sample (hashes table y)}[event (y, r)] := by
  rw [OptionT.prEvent_eq_run]
  have execution : (TupleLookupPair.sample (K := K) table).run =
      ($ᵗ K >>= fun y => (fun result => result.map (fun r => (y, r))) <$> (ReciprocalDetection.sample (hashes table y)).run) := by
    simp only [TupleLookupPair.sample, OptionT.run_bind, OptionT.run_lift]
    simp only [Option.elimM, bind_assoc, pure_bind, OptionT.run_map]
    rfl
  rw [execution, prEvent_bind_eq_tsum, tsum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [prEvent_map, OptionT.prEvent_eq_run]
  exact prEvent_congr _ _ _ (fun result => by cases result <;> rfl)

/-- Every finite raw-byte pair approximation is dominated by the original
joint pair law, with the same challenge-dependent reciprocal domain. -/
theorem event_le_ideal (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (enough : size + 1 < Fintype.card K) (hashDepth inner outer : ℕ) (event : K × K → Prop) :
    Pr{let result ← program basis table hashDepth inner outer}[result.value.elim False event] ≤
      Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] := by
  rw [probability valid basis, ideal_probability]
  have completion : ByteReciprocalSampler.completion p degree hashDepth ≤ 1 :=
    pow_le_one₀ zero_le (CanonicalCoefficientVector.completion_le_one p hashDepth)
  calc _ ≤ 1 * (∑ y : K, Pr{let value ← $ᵗ K}[value = y] *
          Pr{let r ← ReciprocalDetection.sample (hashes table y)}[event (y, r)]) := by
            apply mul_le_mul'
            · exact completion
            · apply Finset.sum_le_sum
              intro y _
              exact mul_le_mul_right (ByteReciprocalSampler.event_le_ideal valid basis (hashes table y) enough inner outer _) _
       _ = _ := one_mul _

/-- Both original lookup losses remain in the byte-backed single-pair bound. -/
theorem single_bound {char : ℕ} [CharP K char] (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (hashDepth inner outer : ℕ) :
    Pr{let result ← program basis table hashDepth inner outer}[result.value.elim False (TupleLookupPair.Passes sources table multiplicities)] ≤
      TupleLookupPair.error (Fintype.card K) width count size :=
  (event_le_ideal valid basis table enough hashDepth inner outer _).trans
    (TupleLookupPair.single_bound sources table multiplicities bad small)

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- A returned pair passed the reciprocal checks for its own sampled hash
challenge. The first challenge and both raw observations remain consistent. -/
theorem returned_allowed (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (hashDepth inner outer : ℕ)
    (result : Result p degree K) (supported : result ∈ support (program basis table hashDepth inner outer))
    (y r : K) (returned : result.value = some (y, r)) :
    ByteReciprocalSampler.candidate result.hashTrial = some y ∧
      r ≠ 0 ∧ ∀ index, r + hashes table y index ≠ 0 := by
  simp only [program, support_bind, Set.mem_iUnion] at supported
  obtain ⟨first, _, branch⟩ := supported
  cases tag : ByteReciprocalSampler.candidate first with
  | none =>
    simp only [tag, support_pure, Set.mem_singleton_iff] at branch
    subst result
    simp at returned
  | some head =>
    simp only [tag, support_map, Set.mem_image] at branch
    obtain ⟨last, reached, equal⟩ := branch
    subst result
    cases lastTag : last.value with
    | none => simp [finish, lastTag] at returned
    | some value =>
      have equalPair : (head, value) = (y, r) := by
        simpa only [finish, lastTag, Option.map_some, Option.some.injEq] using returned
      cases equalPair
      exact ⟨tag, ByteReciprocalSampler.returned_allowed basis (hashes table y) inner outer last reached r lastTag⟩

section SharedRuntime

variable {Cfg Input Digest Payload Later : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Later shared work may inspect both sampling traces. It cannot increase a
fixed earlier successful pair event; its own hash work remains in execution. -/
theorem retained_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (hashDepth inner outer : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (next : Result p degree K → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (event : K × K → Prop) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PrivateSampling.embed Cfg Input Digest (program basis table hashDepth inner outer)) next)).run state}[
        outcome.1.1.value.elim False event] ≤ Pr{let pair ← TupleLookupPair.sample (K := K) table}[event pair] := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (program basis table hashDepth inner outer)) next state (fun earlier => earlier.value.elim False event)
  have sampled := event_le_ideal valid basis table enough hashDepth inner outer event
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_map] using sampled)

end SharedRuntime

end

end FormalProof4FHE.HasteBoots.ByteLookupPairSampler
