module
public import FormalProof4FHE.HasteBoots.OriginalLookupFactorSamples
public import FormalProof4FHE.HasteBoots.FreshReceiptTargetRisk
@[expose] public section

/-! An original-position lookup/EQ sample's receipt digest is named by any
earlier positive query of its completed outer scalar input. Actual native
reader ancestry supplies frame membership; no digest target is supplied. -/
namespace FormalProof4FHE.HasteBoots.LookupSampleReceiptTargets
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open LookupFactorFixation (Sample)
noncomputable section

theorem in_prelude (sample : Sample) :
    ReceiptFrameView.frame sample.view.reader.world sample.state.phase ∈ ReceiptFrameView.frames sample.view.prelude.transcript.input := by
  have body : ReceiptFrameView.frame sample.view.reader.world sample.state.phase ∈
      sample.view.prelude.groups.flatten ++ sample.view.prelude.equality := by
    have named := sample.atReceipt
    cases position : sample.position with
    | compression job =>
      simp only [ScalarReceiptMatching.receiptAt,position] at named
      obtain ⟨group,groupAt,headAt⟩ := Option.bind_eq_some_iff.mp named
      exact List.mem_append_left _ (List.mem_flatten.mpr ⟨group,List.mem_of_getElem? groupAt,List.mem_of_mem_head? (by rw [headAt]; rfl)⟩)
    | offset job =>
      simp only [ScalarReceiptMatching.receiptAt,position] at named
      obtain ⟨group,groupAt,lastAt⟩ := Option.bind_eq_some_iff.mp named
      exact List.mem_append_left _ (List.mem_flatten.mpr ⟨group,List.mem_of_getElem? groupAt,List.mem_of_mem_getLast? (by rw [lastAt]; rfl)⟩)
    | draw job index =>
      simp only [ScalarReceiptMatching.receiptAt,position] at named
      obtain ⟨group,groupAt,drawAt⟩ := Option.bind_eq_some_iff.mp named
      exact List.mem_append_left _ (List.mem_flatten.mpr ⟨group,List.mem_of_getElem? groupAt,List.mem_of_getElem? drawAt⟩)
    | equalityPoint index =>
      simp only [ScalarReceiptMatching.receiptAt,position] at named
      exact List.mem_append_right _ (List.mem_of_getElem? named)
  rw [sample.view.prelude.sequence,List.append_assoc]
  exact List.mem_append_right _ body

theorem in_reader (sample : Sample) :
    ReceiptFrameView.frame sample.view.reader.world sample.state.phase ∈
      ReceiptFrameView.frames sample.view.reader.entry.coefficients.phase.pending.input := by
  have parent := in_prelude sample
  rw [← sample.view.linked] at parent
  have scalar := NativeScalarTranscriptExtension.execute sample.view.reader.transcript sample.view.reader.statement sample.view.reader.proof
    sample.view.reader.fuel _ sample.view.reader.world sample.view.reader.domain
    (NativeScalarTranscriptExtension.initial sample.view.reader.transcript sample.view.reader.statement sample.view.reader.proof sample.view.reader.statementFits)
  obtain ⟨suffix,valid,bytes,_⟩ := (scalar.2.2 sample.view.reader.entry sample.view.reader.member).1
  have projected := ReceiptSequence.append _ _ suffix sample.view.reader.framed valid bytes
  rw [projected.2]
  exact List.mem_append_left _ parent

theorem observed (sample : Sample) (history : List Observation) (offset : ℕ) (values : Input)
    (positive : values ≠ [])
    (present : .output sample.view.reader.entry.coefficients.phase.pending.input offset values ∈ history) :
    InputIndexedOracle.block sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64 ∈
      ReceiptDigestTargets.targets history :=
  ReceiptDigestTargets.observed _ values offset sample.view.reader.world sample.state.phase history positive present (in_reader sample)

theorem event {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A)
    (sample : Sample) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (present : .output sample.view.reader.entry.coefficients.phase.pending.input offset values ∈ packet.2)
    (selected : FreshReceiptTargetRisk.select step packet = some sample.state.phase.consumed) :
    FreshReceiptTargetRisk.event step packet sample.view.reader.world := by
  simp only [FreshReceiptTargetRisk.event,selected]
  exact observed sample packet.2 offset values positive present

end
end FormalProof4FHE.HasteBoots.LookupSampleReceiptTargets
