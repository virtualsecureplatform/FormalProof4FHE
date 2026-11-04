module

public import FormalProof4FHE.HasteBoots.TypedFieldRequest
public import FormalProof4FHE.HasteBoots.NativeFieldRepresentation

@[expose] public section

/-! The classical typed prime-field request used by Brakedown's base-field
random test. Scalar/vector kind and prime kind are both bound. Rejection,
resumption and receipts use the original collector; fuel is analysis only. -/
namespace FormalProof4FHE.HasteBoots.NativePrimeRequest

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript utf8)
open NativeUsizeMessage (Usize)
open TypedFieldRequest (Kind)
open OracleProgram (Program bind run)

def prepare (transcript : Transcript) (kind : Kind) : Transcript :=
  NativeTranscript.appendBytes (TypedFieldRequest.prepare transcript kind) (utf8 "field challenge kind") (utf8 "prime vector")

def phase (p : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) : NativeTranscript.FieldPhase :=
  (NativeTranscript.beginField (prepare transcript kind) label p count.val).run.1

def beginRequest (p : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) : Program NativeFieldVector.State :=
  bind (NativeTranscriptProgram.beginField (prepare transcript kind) label p count.val)
    (fun started => .pure (NativeFieldVector.initial started count.val))

def request (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) : Program NativeFieldVector.Status :=
  NativeFieldVector.primeRequest p fuel (TypedFieldRequest.prepare transcript kind) label count.val

theorem prepare_input (transcript : Transcript) (kind : Kind) :
    (prepare transcript kind).input = transcript.input ++ TranscriptFrame.encodeMany
      [⟨1,utf8 "typed request kind",TypedFieldRequest.kindBytes kind⟩,
       ⟨1,utf8 "field challenge kind",utf8 "prime vector"⟩] := by
  simp only [prepare,TypedFieldRequest.prepare,NativeTranscript.appendBytes,NativeTranscript.absorb,
    TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]

theorem request_eq_collector (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) :
    request p fuel transcript kind label count = NativeFieldVector.request p fuel (prepare transcript kind) label count.val := rfl

theorem run_beginRequest (p : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World) :
    (run (beginRequest p transcript kind label count) world).run =
      (NativeFieldVector.initial (phase p transcript kind label count) count.val,[.start (phase p transcript kind label count).pending.input]) := rfl

theorem drive_request (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World) :
    (run (bind (beginRequest p transcript kind label count) (NativeFieldVector.drive p fuel)) world).run =
      (run (request p fuel transcript kind label count) world).run := by
  rw [request_eq_collector,NativeFieldVector.run_request]
  simp only [OracleProgram.run_bind,ObservationReplay.run_bind,run_beginRequest,NativeFieldVector.run_drive]
  rfl

theorem request_count (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World) :
    let state := NativeFieldVector.stateOf (run (request p fuel transcript kind label count) world).run.1
    state.remaining + state.values.length = count.val :=
  NativeFieldVector.request_count p fuel (prepare transcript kind) label count.val world

theorem request_values_valid (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World) :
    NativeFieldVector.ValuesValid p (NativeFieldVector.stateOf (run (request p fuel transcript kind label count) world).run.1) :=
  NativeFieldVector.request_values_valid p fuel (prepare transcript kind) label count.val world

theorem finished_length (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World)
    (state : NativeFieldVector.State) (result : Transcript)
    (finished : (run (request p fuel transcript kind label count) world).run.1 = .finished state result) : state.values.length = count.val :=
  NativeFieldVector.request_finished_length p fuel (prepare transcript kind) label count.val world state result finished

theorem request_add (p first extra : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World) :
    (run (request p (first+extra) transcript kind label count) world).run =
      let earlier := (run (request p first transcript kind label count) world).run
      let later := (run (NativeFieldVector.resume p extra earlier.1) world).run
      (later.1,earlier.2 ++ later.2) :=
  NativeFieldVector.request_add p first extra (prepare transcript kind) label count.val world

/-- Even an empty prime vector binds its field phase and receipt. -/
theorem request_zero (p fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (world : World) :
    (run (request p fuel transcript kind label ⟨0,by decide⟩) world).run =
      let started := phase p transcript kind label ⟨0,by decide⟩
      let receipt := (NativeTranscript.finishField world started).run
      (.finished (NativeFieldVector.initial started 0) receipt.1,[.start started.pending.input] ++ receipt.2) :=
  NativeFieldVector.request_zero p fuel (prepare transcript kind) label world

/-- Canonical prime samples convert to native Goldilocks words without any
change to the sampled integer. This conversion is used only on finished draws. -/
def goldWord (value : ℕ) : NativeFieldRepresentation.GoldWord :=
  ⟨value % (2^64),Nat.mod_lt _ (by decide)⟩

theorem goldWord_exact (value : ℕ) (valid : value < NativeFields.goldilocksModulus) : (goldWord value).val = value :=
  Nat.mod_eq_of_lt (valid.trans (by decide : NativeFields.goldilocksModulus < 2^64))

theorem finished_gold_exact (fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : Usize) (world : World)
    (state : NativeFieldVector.State) (result : Transcript)
    (finished : (run (request NativeFields.goldilocksModulus fuel transcript kind label count) world).run.1 = .finished state result) :
    state.values.length = count.val ∧ ∀ value ∈ state.values,
      (goldWord value).val = value ∧ (goldWord value).val < NativeFields.goldilocksModulus := by
  have valid := request_values_valid NativeFields.goldilocksModulus fuel transcript kind label count world
  rw [finished] at valid
  refine ⟨finished_length _ _ _ _ _ _ _ _ _ finished,?_⟩
  intro value member
  have bound := valid value member
  exact ⟨goldWord_exact value bound,by rw [goldWord_exact value bound]; exact bound⟩

end FormalProof4FHE.HasteBoots.NativePrimeRequest
