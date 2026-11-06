module

public import FormalProof4FHE.HasteBoots.NativeTranscriptFraming
public import FormalProof4FHE.HasteBoots.NativePrimeRequest
public import FormalProof4FHE.HasteBoots.NativeIndexRequest
import all Init.Data.String.Defs
@[expose] public section

/-! Prime-field collection, rejection/resumption receipts and successful atomic index sampling retain valid append-only transcript ancestry. Native index byte-count gates supply the response-size bound. -/
namespace FormalProof4FHE.HasteBoots.NativePrimeIndexExtension
open NativeTranscript (Transcript utf8)
open NativeUsizeMessage (Usize)
open InputIndexedOracle (Input World)
open OracleProgram (run)
open NativeTranscriptExtension (Extends StatusExtends)
noncomputable section

theorem prime_prepare (state : Transcript) (kind : TypedFieldRequest.Kind) :
    Extends state (NativePrimeRequest.prepare state kind) := by
  apply (NativeTranscriptExtension.typed_prepare state kind).trans
  apply NativeTranscriptExtension.absorb _ 1 (utf8 "field challenge kind") (utf8 "prime vector")
  unfold TranscriptFrame.Valid
  decide +kernel

theorem prime_status (p fuel : ℕ) (state : Transcript) (kind : TypedFieldRequest.Kind) (label : Input) (count : Usize)
    (world : World) (labelFits : label.length < TranscriptFrame.lengthLimit) :
    StatusExtends state (run (NativePrimeRequest.request p fuel state kind label count) world).run.1 := by
  rw [NativePrimeRequest.request_eq_collector]
  exact NativeTranscriptExtension.StatusExtends.trans (prime_prepare state kind)
    (NativeTranscriptExtension.request_status p fuel (NativePrimeRequest.prepare state kind) label count.val world labelFits)

theorem prime_finished (p fuel : ℕ) (state : Transcript) (kind : TypedFieldRequest.Kind) (label : Input) (count : Usize)
    (world : World) (labelFits : label.length < TranscriptFrame.lengthLimit) (collected : NativeFieldVector.State) (next : Transcript)
    (finished : (run (NativePrimeRequest.request p fuel state kind label count) world).run.1 = .finished collected next) :
    Extends state next := by
  have preserved := prime_status p fuel state kind label count world labelFits
  rw [finished] at preserved
  exact preserved.2

theorem index_prepare (state : Transcript) (domain : Usize) : Extends state (NativeIndexRequest.prepare state domain) := by
  apply NativeTranscriptExtension.absorb state 1 (utf8 "index domain") _
  constructor
  · change (utf8 "index domain").length < TranscriptFrame.lengthLimit
    decide +kernel
  · rw [TranscriptFrame.littleEndian_length]
    decide +kernel

theorem index_accepted (state : Transcript) (label : Input) (domain count : Usize) (world : World)
    (result : NativeIndexRequest.Result) (labelFits : label.length < TranscriptFrame.lengthLimit)
    (accepted : (run (NativeIndexRequest.request state label domain count) world).run.1 = some result) :
    Extends state result.transcript := by
  have valid := NativeIndexRequest.accepted_check state label domain count world result accepted
  have countFits : count.val*8 < TranscriptFrame.lengthLimit := by
    change count.val*8 < 256^8
    exact (NativeIndexRequest.check_iff domain count).mp valid |>.2
  rw [NativeIndexRequest.run_request state label domain count world valid] at accepted
  have same := Option.some.inj accepted
  subst result
  exact (index_prepare state domain).trans (NativeTranscriptFraming.challenge_bytes _ label _ world labelFits countFits)
end
end FormalProof4FHE.HasteBoots.NativePrimeIndexExtension
