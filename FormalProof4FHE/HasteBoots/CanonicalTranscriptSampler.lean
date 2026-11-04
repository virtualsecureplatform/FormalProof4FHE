module

public import FormalProof4FHE.HasteBoots.NativeTranscriptProgram
public import FormalProof4FHE.HasteBoots.CanonicalByteSampler
public import FormalProof4FHE.HasteBoots.RejectionTraceWork

@[expose] public section

/-!
# Canonical byte rejection as an online transcript program

Each attempt uses the existing field reader, the native little-endian
decode/mask/below-modulus test, and retains its entire raw chunk. Exhaustion
is analysis suspension with the updated field phase; it emits no receipt.
Rust correspondence still requires the frontend gate. Native callers must
establish `1 < p` and the u128 modulus bound.
-/

namespace FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler

open InputIndexedOracle (Byte Input World bytes)
open NativeTranscript (FieldPhase Observation Execution)
open OracleProgram (Program bind run)
open scoped BigOperators
open OracleSpec OracleComp

theorem fromLittleEndian_ofFn {width : ℕ} (raw : Fin width → Byte) :
    TranscriptFrame.fromLittleEndian (List.ofFn raw) = CanonicalByteMask.decode raw := by
  rw [CanonicalByteMask.decode_eq_sum]
  induction width with
  | zero => simp [TranscriptFrame.fromLittleEndian]
  | succ width ih =>
    rw [List.ofFn_succ, TranscriptFrame.fromLittleEndian, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    ac_rfl

def candidate (p : ℕ) (raw : Input) : ℕ :=
  TranscriptFrame.fromLittleEndian raw &&& CanonicalByteSampler.nativeMask p

/-- The list-byte operational test is exactly the finite-vector test used
by the existing canonical sampler probability and completed-trace proofs. -/
theorem candidate_ofFn (p : ℕ) (raw : CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p)) :
    candidate p (List.ofFn raw) = CanonicalByteMask.masked (CanonicalByteSampler.bits p) raw := by
  rw [candidate, fromLittleEndian_ofFn, CanonicalByteSampler.nativeMask_eq]
  rfl

/-- The unread part of the native 16-byte scratch array is zero initialized. -/
theorem scratch_decode {width : ℕ} (fits : width ≤ 16) (raw : CanonicalByteMask.Bytes width) :
    TranscriptFrame.fromLittleEndian (List.ofFn (CanonicalByteMask.pad fits raw)) =
      TranscriptFrame.fromLittleEndian (List.ofFn raw) := by
  rw [fromLittleEndian_ofFn, fromLittleEndian_ofFn, CanonicalByteMask.decode_pad]

theorem scratch_fits_u128 {width : ℕ} (fits : width ≤ 16) (raw : CanonicalByteMask.Bytes width) :
    TranscriptFrame.fromLittleEndian (List.ofFn (CanonicalByteMask.pad fits raw)) < 2 ^ 128 := by
  rw [fromLittleEndian_ofFn]
  exact CanonicalByteMask.decode_pad_lt_u128 fits raw

def vector (width : ℕ) (raw : Input) : CanonicalByteMask.Bytes width :=
  fun index => raw[index.val]?.getD 0

theorem vector_ofFn {width : ℕ} (raw : CanonicalByteMask.Bytes width) :
    vector width (List.ofFn raw) = raw := by
  funext index
  simp [vector]

theorem ofFn_vector {width : ℕ} (raw : Input) (length : raw.length = width) :
    List.ofFn (vector width raw) = raw := by
  subst width
  have same : vector raw.length raw = raw.get := by
    funext index
    simp [vector]
  rw [same, List.ofFn_get]

theorem candidate_vector (p : ℕ) (raw : Input) (length : raw.length = CanonicalByteSampler.byteCount p) :
    candidate p raw = CanonicalByteMask.masked (CanonicalByteSampler.bits p)
      (vector (CanonicalByteSampler.byteCount p) raw) := by
  have same := candidate_ofFn p (vector (CanonicalByteSampler.byteCount p) raw)
  rwa [ofFn_vector raw length] at same

structure Outcome where
  accepted : Option Input
  chunks : List Input
  phase : FieldPhase

def paused (phase : FieldPhase) : Outcome := ⟨none, [], phase⟩
def completed (raw : Input) (phase : FieldPhase) : Outcome := ⟨some raw, [raw], phase⟩
def prepend (raw : Input) (tail : Outcome) : Outcome := { tail with chunks := raw :: tail.chunks }

def value (p : ℕ) (outcome : Outcome) : Option ℕ := outcome.accepted.map (candidate p)

def samplePrefix (p : ℕ) : ℕ → FieldPhase → Program Outcome
  | 0, phase => .pure (paused phase)
  | fuel + 1, phase =>
      bind (NativeTranscriptProgram.drawField phase (CanonicalByteSampler.byteCount p))
        (fun (raw, next) =>
          if candidate p raw < p then .pure (completed raw next)
          else bind (samplePrefix p fuel next) (fun tail => .pure (prepend raw tail)))

/-- A direct finite observation of the native loop, driven by the same
field-reader model as `samplePrefix`. No fresh private draws are inserted. -/
def executePrefix (p : ℕ) : ℕ → FieldPhase → World → Outcome × List Observation
  | 0, phase, _ => (paused phase, [])
  | fuel + 1, phase, world =>
      let step := (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run
      let (raw, next) := step.1
      if candidate p raw < p then (completed raw next, step.2)
      else
        let tail := executePrefix p fuel next world
        (prepend raw tail.1, step.2 ++ tail.2)

theorem run_pure {A : Type} (value : A) : (pure value : Execution A).run = (value, []) := rfl

theorem run_samplePrefix (p fuel : ℕ) (phase : FieldPhase) (world : World) :
    (run (samplePrefix p fuel phase) world).run = executePrefix p fuel phase world := by
  induction fuel generalizing phase with
  | zero => rfl
  | succ fuel ih =>
    simp only [samplePrefix, OracleProgram.run_bind, NativeTranscriptProgram.run_drawField,
      ObservationReplay.run_bind, executePrefix]
    split
    · rfl
    · simp only [OracleProgram.run_bind, OracleProgram.run, ObservationReplay.run_bind, ih,
        run_pure, List.append_nil]

/-- Full raw retention, including every rejected candidate, exactly determines
the final field phase. Earlier coefficients' consumed bytes remain intact. -/
theorem phase_retains_chunks (p fuel : ℕ) (phase : FieldPhase) (world : World) :
    (executePrefix p fuel phase world).1.phase =
      { phase with consumed := phase.consumed ++ (executePrefix p fuel phase world).1.chunks.flatten } := by
  induction fuel generalizing phase with
  | zero => simp [executePrefix, paused]
  | succ fuel ih =>
    simp only [executePrefix, NativeTranscript.drawField, WriterT.run_mk]
    by_cases good : candidate p (bytes world phase.pending.input phase.consumed.length
      (CanonicalByteSampler.byteCount p)) < p
    · simp [good, completed]
    · simp only [good, ite_false, prepend, ih, List.flatten_cons, List.append_assoc]

theorem chunks_width (p fuel : ℕ) (phase : FieldPhase) (world : World) :
    ∀ raw ∈ (executePrefix p fuel phase world).1.chunks, raw.length = CanonicalByteSampler.byteCount p := by
  induction fuel generalizing phase with
  | zero => simp [executePrefix, paused]
  | succ fuel ih =>
    simp only [executePrefix, NativeTranscript.drawField, WriterT.run_mk]
    by_cases good : candidate p (bytes world phase.pending.input phase.consumed.length
      (CanonicalByteSampler.byteCount p)) < p
    · simp [good, completed, InputIndexedOracle.bytes_length]
    · simp only [good, ite_false, prepend]
      intro raw member
      rcases List.mem_cons.mp member with equal | tail
      · subst raw
        exact InputIndexedOracle.bytes_length _ _ _ _
      · exact ih _ raw tail

theorem accepted_below (p fuel : ℕ) (phase : FieldPhase) (world : World) (raw : Input)
    (found : (executePrefix p fuel phase world).1.accepted = some raw) : candidate p raw < p := by
  induction fuel generalizing phase with
  | zero => simp [executePrefix, paused] at found
  | succ fuel ih =>
    let step := (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run
    by_cases good : candidate p (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run.1.1 < p
    · have same : step.1.1 = raw := Option.some.inj (by
        simpa only [executePrefix, good, ite_true, completed] using found)
      dsimp only [step] at same
      simpa only [same] using good
    · apply ih step.1.2
      simpa only [executePrefix, good, ite_false, prepend] using found

theorem final_coherent (p fuel : ℕ) (phase : FieldPhase) (world : World)
    (coherent : NativeTranscript.Coherent world phase) :
    NativeTranscript.Coherent world (executePrefix p fuel phase world).1.phase := by
  induction fuel generalizing phase with
  | zero => exact coherent
  | succ fuel ih =>
    let step := (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run
    have nextCoherent := NativeTranscript.draw_coherent world phase coherent (CanonicalByteSampler.byteCount p)
    by_cases good : candidate p (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run.1.1 < p
    · simpa only [executePrefix, good, ite_true, completed] using nextCoherent
    · simpa only [executePrefix, good, ite_false, prepend] using ih step.1.2 nextCoherent

/-- Increasing the analysis depth cannot change any completed native
observation, including its rejected chunks, field state, or output log. -/
theorem completed_stable (p first extra : ℕ) (phase : FieldPhase) (world : World)
    (finished : (executePrefix p first phase world).1.accepted ≠ none) :
    executePrefix p (first + extra) phase world = executePrefix p first phase world := by
  induction first generalizing phase with
  | zero => simp [executePrefix, paused] at finished
  | succ first ih =>
    rw [Nat.succ_add]
    let step := (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run
    by_cases good : candidate p (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run.1.1 < p
    · simp only [executePrefix, good, ite_true]
    · have tailFinished : (executePrefix p first step.1.2 world).1.accepted ≠ none := by
        simpa only [executePrefix, good, ite_false, prepend] using finished
      have sameTail := ih step.1.2 tailFinished
      dsimp only [step] at sameTail
      simp only [executePrefix, good, ite_false, sameTail]

/-- Suspended prefixes are prefixes of the same execution, without dropping
rejected reads or finalizing a premature receipt. -/
theorem log_refines (p first extra : ℕ) (phase : FieldPhase) (world : World) :
    List.IsPrefix (executePrefix p first phase world).2 (executePrefix p (first + extra) phase world).2 := by
  induction first generalizing phase with
  | zero => simp [executePrefix, paused]
  | succ first ih =>
    rw [Nat.succ_add]
    let step := (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run
    by_cases good : candidate p (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run.1.1 < p
    · simp only [executePrefix, good, ite_true]
      exact ⟨[], by simp⟩
    · simp only [executePrefix, good, ite_false]
      obtain ⟨suffix, same⟩ := ih step.1.2
      refine ⟨suffix, ?_⟩
      simpa only [List.append_assoc] using congrArg (fun tail => step.2 ++ tail) same

def continuePrefix (p extra : ℕ) (earlier : Outcome × List Observation) (world : World) :
    Outcome × List Observation :=
  if earlier.1.accepted = none then
    let later := executePrefix p extra earlier.1.phase world
    ({ later.1 with chunks := earlier.1.chunks ++ later.1.chunks }, earlier.2 ++ later.2)
  else earlier

theorem continue_prepend (p extra : ℕ) (raw : Input) (headLog : List Observation)
    (earlier : Outcome × List Observation) (world : World) :
    continuePrefix p extra (prepend raw earlier.1, headLog ++ earlier.2) world =
      (prepend raw (continuePrefix p extra earlier world).1,
        headLog ++ (continuePrefix p extra earlier world).2) := by
  by_cases finished : earlier.1.accepted = none <;>
    simp [continuePrefix, prepend, finished, List.append_assoc]

/-- Resuming a suspended native prefix is exactly the larger observation,
with prior rejected chunks and logs concatenated, not reconstructed. -/
theorem resume_exact (p first extra : ℕ) (phase : FieldPhase) (world : World) :
    executePrefix p (first + extra) phase world =
      continuePrefix p extra (executePrefix p first phase world) world := by
  induction first generalizing phase with
  | zero => simp [executePrefix, paused, continuePrefix]
  | succ first ih =>
    rw [Nat.succ_add]
    let step := (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run
    by_cases good : candidate p (NativeTranscript.drawField world phase (CanonicalByteSampler.byteCount p)).run.1.1 < p
    · simp [executePrefix, good, completed, continuePrefix]
    · have tailSame := ih step.1.2
      dsimp only [step] at tailSame
      simp only [executePrefix, good, ite_false, tailSame]
      exact (continue_prepend p extra step.1.1 step.2
        (executePrefix p first step.1.2 world) world).symm

def typedObservation (p : ℕ) (outcome : Outcome) :
    RejectionSampling.Result (CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p)) :=
  (outcome.accepted.map (vector (CanonicalByteSampler.byteCount p)),
    outcome.chunks.map (vector (CanonicalByteSampler.byteCount p)))

/-- Reachability is transferred to the existing private sampler without
asserting equality of distributions under adversarial prequeries. -/
theorem typed_supported (p fuel : ℕ) (phase : FieldPhase) (world : World) :
    typedObservation p (executePrefix p fuel phase world).1 ∈
      support (CanonicalByteSampler.runPrefix p fuel) := by
  classical
  induction fuel generalizing phase with
  | zero => simp [executePrefix, paused, typedObservation, CanonicalByteSampler.runPrefix]
  | succ fuel ih =>
    let raw := bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)
    let next : FieldPhase := { phase with consumed := phase.consumed ++ raw }
    simp only [executePrefix, NativeTranscript.drawField, WriterT.run_mk,
      CanonicalByteSampler.runPrefix, support_bind, Set.mem_iUnion]
    refine ⟨vector (CanonicalByteSampler.byteCount p) raw, mem_support_uniformSample _, ?_⟩
    rw [← candidate_vector p raw (InputIndexedOracle.bytes_length _ _ _ _)]
    dsimp only [raw, next]
    by_cases good : candidate p (bytes world phase.pending.input phase.consumed.length
      (CanonicalByteSampler.byteCount p)) < p
    · simp [good, typedObservation, completed]
    · simp only [good, ite_false, support_map]
      exact Set.mem_image_of_mem _ (ih next)

theorem attempts_le (p fuel : ℕ) (phase : FieldPhase) (world : World) :
    (executePrefix p fuel phase world).1.chunks.length ≤ fuel := by
  have supported := typed_supported p fuel phase world
  rw [CanonicalByteSampler.runPrefix_eq] at supported
  simpa only [typedObservation, List.length_map] using
    RejectionTraceWork.length_le (CanonicalByteSampler.accepted p) fuel _ supported

theorem suspended_attempts (p fuel : ℕ) (phase : FieldPhase) (world : World)
    (suspended : (executePrefix p fuel phase world).1.accepted = none) :
    (executePrefix p fuel phase world).1.chunks.length = fuel := by
  have supported := typed_supported p fuel phase world
  rw [CanonicalByteSampler.runPrefix_eq] at supported
  have incomplete : (typedObservation p (executePrefix p fuel phase world).1).1 = none := by
    simp only [typedObservation, suspended, Option.map_none]
  simpa only [typedObservation, List.length_map] using
    RejectionTraceWork.suspended_length (CanonicalByteSampler.accepted p) fuel _ supported incomplete

private theorem flatten_length (width : ℕ) (chunks : List Input)
    (same : ∀ raw ∈ chunks, raw.length = width) : chunks.flatten.length = width * chunks.length := by
  induction chunks with
  | nil => simp
  | cons raw tail ih =>
    have head := same raw (by simp)
    have rest := ih (fun entry member => same entry (by simp [member]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, head, rest, Nat.mul_succ]
    omega

/-- Actual added field-reader bytes equal the old trace cost pointwise.
This is not a primitive-to-machine-work conversion or an expected-work law. -/
theorem added_bytes (p fuel : ℕ) (phase : FieldPhase) (world : World) :
    (executePrefix p fuel phase world).1.phase.consumed.length = phase.consumed.length +
      CanonicalByteSampler.consumedBytes p (typedObservation p (executePrefix p fuel phase world).1) := by
  rw [phase_retains_chunks]
  simp only [List.length_append, CanonicalByteSampler.consumedBytes, typedObservation, List.length_map]
  exact congrArg (phase.consumed.length + ·)
    (flatten_length _ _ (chunks_width p fuel phase world))

theorem sample_replay (p fuel : ℕ) (phase : FieldPhase) :
    ObservationReplay.Replayable (run (samplePrefix p fuel phase)) := OracleProgram.run_replay _

end FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler
