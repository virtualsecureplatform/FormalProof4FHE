module
public import FormalProof4FHE.HasteBoots.OriginalEqualityLookupFactors
@[expose] public section

/-! Actual earlier lookup receipts at equality inputs share the existing
whole-program coverage and collision exceptions. Payload naming follows from
observations at the exact first read, rather than an independent certificate. -/
namespace FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ProgramFirstStreamRead (First)
open EqualityLookupFactorFixation (Scalar)
noncomputable section

def Observed {A : Type} (program : Program A) (sample : Scalar) : Prop :=
  Observation.output (NativeReceiptPrefixView.key sample.field.phase.consumed) 0
    (InputIndexedOracle.bytes sample.world (NativeReceiptPrefixView.key sample.field.phase.consumed) 0 64) ∈
      (run program sample.world).run.2

theorem in_prelude (sample : Scalar) : ReceiptFrameView.frame sample.world sample.field.phase ∈
    ReceiptFrameView.frames sample.view.prelude.transcript.input := by
  have named := sample.atReceipt
  have member : ReceiptFrameView.frame sample.world sample.field.phase ∈ sample.view.prelude.groups.flatten := by
    cases side : sample.side with
    | compression =>
      simp only [EqualityLookupFactorFixation.receiptAt,side] at named
      obtain ⟨group,atGroup,atHead⟩ := Option.bind_eq_some_iff.mp named
      exact List.mem_flatten.mpr ⟨group,List.mem_of_getElem? atGroup,List.mem_of_mem_head? (by rw [atHead]; rfl)⟩
    | offset =>
      simp only [EqualityLookupFactorFixation.receiptAt,side] at named
      obtain ⟨group,atGroup,atLast⟩ := Option.bind_eq_some_iff.mp named
      exact List.mem_flatten.mpr ⟨group,List.mem_of_getElem? atGroup,List.mem_of_mem_getLast? (by rw [atLast]; rfl)⟩
  rw [sample.view.prelude.sequence]
  exact List.mem_append_left _ (List.mem_append_right _ member)

theorem in_reader (sample : Scalar) : ReceiptFrameView.frame sample.world sample.field.phase ∈
    ReceiptFrameView.frames sample.view.input := by
  obtain ⟨after,bytes,valid⟩ := HelperRootsBoundary.sound sample.view.input sample.view.roots sample.view.before sample.view.parsed
  have beforeValid : ∀ frame ∈ sample.view.before, TranscriptFrame.Valid frame :=
    fun frame member => valid frame (List.mem_append_left _ member)
  have beforeDecoded : TranscriptFrame.decodeAll sample.view.prelude.transcript.input = some sample.view.before := by
    rw [sample.view.bytes]
    exact TranscriptFrame.decodeAll_encodeMany _ beforeValid
  have member := in_prelude sample
  simp only [ReceiptFrameView.frames,beforeDecoded,Option.getD_some] at member
  have frameMember := List.mem_of_mem_filter member
  simp only [ReceiptFrameView.frames,bytes,TranscriptFrame.decodeAll_encodeMany _ valid,Option.getD_some]
  exact List.mem_filter.mpr ⟨List.mem_append_left _ frameMember,by rfl⟩

theorem input_apart (sample : Scalar) : sample.view.input ≠ NativeReceiptPrefixView.key sample.field.phase.consumed := by
  intro same
  have member := in_reader sample
  rw [same] at member
  simp only [ReceiptFrameView.frames,
    show NativeReceiptPrefixView.key sample.field.phase.consumed = NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ sample.field.phase.consumed from rfl,
    NativeTranscript.receipt_decode_rejected,Option.getD_none,List.filter_nil,List.not_mem_nil] at member

theorem named {A : Type} (program : Program A) (sample : Scalar)
    (outer : First program sample.world sample.view.input) (observed : Observed program sample)
    (safe : ¬ProgramReceiptCoverage.Bad program sample.world) :
    sample.field.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix outer.position program sample.world).run.2 := by
  by_contra unnamed
  have unseen : CausalStreamExposure.seen (runPrefix outer.position program sample.world).run.2
      (NativeReceiptPrefixView.key sample.field.phase.consumed) = false := by
    cases seen : CausalStreamExposure.seen (runPrefix outer.position program sample.world).run.2
        (NativeReceiptPrefixView.key sample.field.phase.consumed) with
    | false => rfl
    | true => exact False.elim (unnamed (ReceiptPayloadView.seen _ _ seen))
  obtain ⟨first⟩ := ProgramFirstStreamRead.of_output program sample.world _ 0 _
    (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; contradiction) observed
  have ordered := ReceiptFirstReadCoverage.before_of_unseen outer first (input_apart sample) unseen
  apply safe
  refine ⟨first.position,?_⟩
  simp only [FreshReceiptTargetRisk.event,FreshReceiptTargetRisk.select,first.selected,Option.bind_some,ReceiptPayloadView.read_key]
  exact ReceiptDigestTargets.observed _ _ outer.offset sample.world sample.field.phase _
    (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; have positive := outer.positive; omega)
    (ReceiptFirstReadCoverage.output_before outer first ordered) (in_reader sample)

theorem scalar_on_fiber {A : Type} (program : Program A) (left right : Scalar)
    (input : left.view.input = right.view.input) (ordinal : left.ordinal = right.ordinal) (side : left.side = right.side)
    (first : First program left.world left.view.input) (leftObserved : Observed program left) (rightObserved : Observed program right)
    (fiber : (ReceiptCandidateCompletion.extend (runPrefix first.position program) right.world).run =
      (ReceiptCandidateCompletion.extend (runPrefix first.position program) left.world).run) :
    right.word = left.word ∨ ProgramReceiptCoverage.Bad program left.world ∨
      ProgramReceiptCoverage.Bad program right.world ∨ ProgramReceiptCollision.Bad program left.world := by
  by_cases leftBad : ProgramReceiptCoverage.Bad program left.world
  · exact Or.inr (Or.inl leftBad)
  by_cases rightBad : ProgramReceiptCoverage.Bad program right.world
  · exact Or.inr (Or.inr (Or.inl rightBad))
  have packet := ReceiptCandidateCompletion.old_packet (runPrefix first.position program) left.world right.world fiber
  let transported := FirstReadFiber.transport first right.world packet
  let other := PositionedFactorSamples.reindex transported right.world right.view.input rfl input.symm
  have leftNamed := named program left first leftObserved leftBad
  have rightNamed := named program right other rightObserved rightBad
  rcases EqualityLookupFactorFixation.scalar_on_fiber (OracleProgram.prefix_replay first.position program) left right input ordinal side
      leftNamed rightNamed fiber with fixed | collision
  · exact Or.inl fixed
  · exact Or.inr (Or.inr (Or.inr (ProgramReceiptCollision.prefix_covers program left.world first.position collision)))

end
end FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors
