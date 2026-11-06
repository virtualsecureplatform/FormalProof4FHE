module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRandomLaw
public import FormalProof4FHE.HasteBoots.NativeFieldReceipt
@[expose] public section

/-! Native completion consumes a whole raw oracle prefix, including rejected
candidates. Length lower bounds follow from actual accepted coefficient count,
not a guessed retry bound. Receipt-length wrapping and Rust memory/abort
refinement are separate; no nonwrapping length assumption is introduced here. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldConsumedPrefix
open InputIndexedOracle (Input World bytes block)
open NativeTranscript (FieldPhase Transcript)
open NativeFieldVector (State execute advance initial)
open OracleProgram (run)

theorem trial_phase (p : ℕ) (phase : FieldPhase) (world : World) :
    (CanonicalTranscriptSampler.executePrefix p 1 phase world).1.phase =
      {phase with consumed := phase.consumed ++ bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)} := by
  simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk]
  by_cases good : CanonicalTranscriptSampler.candidate p
      (bytes world phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)) < p
  · simp only [good,ite_true,CanonicalTranscriptSampler.completed]
  · simp only [good,ite_false,CanonicalTranscriptSampler.prepend,CanonicalTranscriptSampler.paused]

theorem advance_length (p : ℕ) (state : State) (world : World) :
    (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1).phase.consumed.length =
      state.phase.consumed.length + CanonicalByteSampler.byteCount p := by
  cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted <;>
    simp only [advance,found,trial_phase,List.length_append,InputIndexedOracle.bytes_length]

theorem advance_values (p : ℕ) (state : State) (world : World) :
    (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1).values.length ≤ state.values.length+1 := by
  cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted <;> simp [advance,found]

def Enough (p : ℕ) (state : State) : Prop := CanonicalByteSampler.byteCount p * state.values.length ≤ state.phase.consumed.length

theorem advance_enough (p : ℕ) (state : State) (world : World) (enough : Enough p state) :
    Enough p (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1) := by
  unfold Enough at *
  rw [advance_length]
  calc _ ≤ CanonicalByteSampler.byteCount p * (state.values.length+1) := Nat.mul_le_mul_left _ (advance_values p state world)
       _ = CanonicalByteSampler.byteCount p * state.values.length + CanonicalByteSampler.byteCount p := by rw [Nat.mul_add,Nat.mul_one]
       _ ≤ _ := Nat.add_le_add_right enough _

theorem execute_enough (p fuel : ℕ) (state : State) (world : World) (enough : Enough p state) :
    Enough p (execute p fuel state world).1 := by
  induction fuel generalizing state with
  | zero => exact enough
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simpa only [execute,complete,ite_true] using enough
    · simpa only [execute,complete,ite_false] using ih _ (advance_enough p state world enough)

theorem completed_length (p fuel count : ℕ) (phase : FieldPhase) (world : World)
    (complete : (execute p fuel (initial phase count) world).1.remaining = 0) :
    CanonicalByteSampler.byteCount p * count ≤ (execute p fuel (initial phase count) world).1.phase.consumed.length := by
  have enough := execute_enough p fuel (initial phase count) world (by simp [Enough,initial])
  unfold Enough at enough
  rw [NativeFieldVector.completed_length p fuel count phase world complete] at enough
  exact enough

/-- A completed native state contains the actual initial oracle block as a
literal byte prefix. A shorter caller-selected block does not replace it. -/
theorem completed_prefix (p fuel count : ℕ) (phase : FieldPhase) (world : World)
    (coherent : NativeTranscript.Coherent world phase)
    (complete : (execute p fuel (initial phase count) world).1.remaining = 0)
    (length : ℕ) (bounded : length ≤ CanonicalByteSampler.byteCount p * count) :
    ∃ tail, (execute p fuel (initial phase count) world).1.phase.consumed = List.ofFn (block world phase.pending.input 0 length) ++ tail := by
  have enough := bounded.trans (completed_length p fuel count phase world complete)
  have same := NativeFieldVector.coherent p fuel (initial phase count) world coherent
  have header := (NativeFieldVector.header_preserved p fuel (initial phase count) world).1
  change (execute p fuel (initial phase count) world).1.phase.pending = phase.pending at header
  change (execute p fuel (initial phase count) world).1.phase.consumed =
    bytes world (execute p fuel (initial phase count) world).1.phase.pending.input 0
      (execute p fuel (initial phase count) world).1.phase.consumed.length at same
  rw [header] at same
  refine ⟨bytes world phase.pending.input length ((execute p fuel (initial phase count) world).1.phase.consumed.length-length),?_⟩
  have split := InputIndexedOracle.bytes_append world phase.pending.input 0 length
    ((execute p fuel (initial phase count) world).1.phase.consumed.length-length)
  rw [Nat.add_sub_of_le enough] at split
  simpa only [Nat.zero_add,InputIndexedOracle.bytes] using same.trans split

theorem finished_prefix (p fuel count : ℕ) (parent : Transcript) (label : Input) (world : World)
    (state : State) (result : Transcript)
    (finished : (run (NativeFieldVector.request p fuel parent label count) world).run.1 = .finished state result)
    (length : ℕ) (bounded : length ≤ CanonicalByteSampler.byteCount p * count) :
    ∃ tail, state.phase.consumed = List.ofFn (block world (NativeTranscript.beginField parent label p count).run.1.pending.input 0 length) ++ tail := by
  obtain ⟨log,executed,_,_⟩ := NativeFieldReceipt.finished_origin p fuel count parent label world state result finished
  have complete := NativeFieldVector.request_status p fuel parent label count world
  rw [finished] at complete
  have stateEq := congrArg Prod.fst executed
  have ready : (execute p fuel (initial (NativeTranscript.beginField parent label p count).run.1 count) world).1.remaining = 0 := by
    rw [stateEq]
    exact complete
  have prefixBytes := completed_prefix p fuel count (NativeTranscript.beginField parent label p count).run.1 world
    (NativeTranscript.begin_coherent world parent label p count) ready length bounded
  rw [stateEq] at prefixBytes
  exact prefixBytes

/-- For the target Goldilocks test width (at least three), completion names
at least72 raw bytes. The code packing width is not substituted for test width. -/
theorem gold_prepared_72 (ctx : NativeGoldBatchPcsProgram.Context) (world : World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (width : 3 ≤ ctx.parameters.width.val) :
    ∃ tail, work.state.phase.consumed = List.ofFn (block world (NativeGoldBatchRandomLaw.phase work).pending.input 0 72) ++ tail := by
  obtain ⟨next,finished⟩ := NativeGoldBatchRandomLaw.prepared_request ctx world work prepared
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  have count : 9 ≤ work.geometry.randomCount.val := by
    rw [geometry.computed]
    change 9 ≤ 2^ctx.parameters.leftVariables.val * ctx.parameters.width.val * ctx.parameters.width.val
    have lower : 1 ≤ 2^ctx.parameters.leftVariables.val := Nat.one_le_pow _ _ (by decide)
    have product := Nat.mul_le_mul (Nat.mul_le_mul lower width) width
    norm_num at product
    exact product
  have bytes : CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 := by decide +kernel
  exact finished_prefix NativeFields.goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val
    (NativePrimeRequest.prepare work.binding.parent .vector) NativeGoldBatchPrelude.randomLabel world work.state next finished 72 (by rw [bytes]; omega)
end FormalProof4FHE.HasteBoots.NativeFieldConsumedPrefix
