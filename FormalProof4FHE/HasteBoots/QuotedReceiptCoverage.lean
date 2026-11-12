module
public import FormalProof4FHE.HasteBoots.ProgramReceiptCoverage
@[expose] public section

/-! The existing lifetime fresh-receipt event covers any actual receipt
quoted by an earlier stream read, including reciprocal lookup streams before
helper roots or outer scalar-verification inputs exist. -/
namespace FormalProof4FHE.HasteBoots.QuotedReceiptCoverage
open InputIndexedOracle (Input World)
open NativeTranscript (Observation FieldPhase)
open OracleProgram (Program run runPrefix)
noncomputable section

theorem named {A : Type} (program : Program A) (world : World) (input : Input) (phase : FieldPhase)
    (outer : ProgramFirstStreamRead.First program world input)
    (member : ReceiptFrameView.frame world phase ∈ ReceiptFrameView.frames input)
    (receipt : Observation.output (NativeReceiptPrefixView.key phase.consumed) 0
      (InputIndexedOracle.bytes world (NativeReceiptPrefixView.key phase.consumed) 0 64) ∈ (run program world).run.2)
    (safe : ¬ProgramReceiptCoverage.Bad program world) :
    phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix outer.position program world).run.2 := by
  by_contra unnamed
  have unseen : CausalStreamExposure.seen (runPrefix outer.position program world).run.2
      (NativeReceiptPrefixView.key phase.consumed) = false := by
    cases seen : CausalStreamExposure.seen (runPrefix outer.position program world).run.2
        (NativeReceiptPrefixView.key phase.consumed) with
    | false => rfl
    | true => exact False.elim (unnamed (ReceiptPayloadView.seen _ _ seen))
  have apart : input ≠ NativeReceiptPrefixView.key phase.consumed := by
    intro same
    rw [same] at member
    simp only [ReceiptFrameView.frames,
      show NativeReceiptPrefixView.key phase.consumed = NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ phase.consumed from rfl,
      NativeTranscript.receipt_decode_rejected,Option.getD_none,List.filter_nil,List.not_mem_nil] at member
  obtain ⟨first⟩ := ProgramFirstStreamRead.of_output program world _ 0 _
    (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; contradiction) receipt
  have ordered := ReceiptFirstReadCoverage.before_of_unseen outer first apart unseen
  have target := ReceiptDigestTargets.observed input (InputIndexedOracle.bytes world input outer.offset outer.count)
    outer.offset world phase (runPrefix first.position program world).run.2
    (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; have positive := outer.positive; omega)
    (ReceiptFirstReadCoverage.output_before outer first ordered) member
  apply safe
  refine ⟨first.position,?_⟩
  simpa only [FreshReceiptTargetRisk.event,FreshReceiptTargetRisk.select,first.selected,Option.bind_some,ReceiptPayloadView.read_key] using target

end
end FormalProof4FHE.HasteBoots.QuotedReceiptCoverage
