module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeLink
import all FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
import all FormalProof4FHETest.HasteBootsBatchOrderedSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law bytes)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsFieldInputSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx work world prepared)
open HasteBootsBatchMeaningSmoke (usize root)

def fieldInput := (NativeGoldBatchRandomLaw.phase work).pending.input
def parsed := NativeGoldBatchFieldInputView.parse fieldInput
theorem present : parsed.isSome = true := by decide +kernel
def view := parsed.get present
theorem decoded : NativeGoldBatchFieldInputView.parse fieldInput = some view := (Option.some_get present).symm
example : view.count.val = 18 ∧ view.data.root = ctx.root ∧ view.data.queries = ctx.queries ∧ view.data.values = ctx.values := by decide +kernel
example : (view.phase root).pending.input = fieldInput ∧ (view.phase root).consumed = [] := by
  exact ⟨(NativeGoldBatchFieldInputView.parse_sound fieldInput view decoded root).1,rfl⟩
example : ((NativeFieldVectorLaw.values NativeFields.goldilocksModulus 18 view.count.val (view.phase root) world).map
    (fun values => (values ⟨0,by decide +kernel⟩).val)) = some 0 := by decide +kernel

def past (oracle : World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← ObservationReplay.read oracle [99] 200 1
  pure (.inl ())
theorem replay : ObservationReplay.Replayable past :=
  ObservationReplay.bind_replay (ObservationReplay.read_replay [99] 200 1) (fun _ => ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit))
def step (_ : Unit) : OracleMachine.Command Unit Unit := .read fieldInput 999 1 (fun _ => ())
theorem first : CausalStreamExposure.firstRead step (past world).run = some fieldInput := by decide +kernel
theorem selected : NativeGoldBatchFieldExposure.select step (past world).run = some view := by
  simp only [NativeGoldBatchFieldExposure.select,first,Option.bind_some,decoded]
example (event : (Fin view.count.val → NativeFields.Goldilocks) → Prop) :
    (law[|{oracle | (past oracle).run = (past world).run}])
      {oracle | (NativeFieldVectorLaw.values NativeFields.goldilocksModulus 18 view.count.val (view.phase root) oracle).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar NativeFields.goldilocksModulus 1) 18 view.count.val *
        Pr{let value ← $ᵗ (Fin view.count.val → NativeFields.Goldilocks)}[event value] :=
  NativeGoldBatchFieldExposure.conditional_uniform root step replay world view selected 18 event
example (event : (Fin view.count.val → NativeFields.Goldilocks) → Prop) :
    (law[|{oracle | (past oracle).run = (past world).run}])
      {oracle | ∃ fuel, (NativeFieldVectorLaw.values NativeFields.goldilocksModulus fuel view.count.val (view.phase root) oracle).elim False event} ≤
        Pr{let value ← $ᵗ (Fin view.count.val → NativeFields.Goldilocks)}[event value] :=
  NativeGoldBatchFieldExposure.eventual_le_uniform root step replay world view selected event

-- The key is resolved from the same input, not supplied from later work.
example (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache) :
    (view.data.context,view.data.root) ∈ NativeParentLedger.resolve ledger cache fieldInput :=
  NativeGoldBatchFieldExposure.parsed_resolved fieldInput view decoded ledger cache
example : ∃ log : MerkleTreeExtractor.QueryLog Input NativeRootMessage.Digest, ∀ index : NativeMerkleShapeFamily.Height,
    ⟨(view.data.context,index),⟨view.data.root,log⟩⟩ ∈
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root
        [NativeTranscript.Observation.output fieldInput 999 [0]]).2.checkpoints.checkpoints := by
  exact NativeGoldBatchFieldExposure.parsed_history_snapshot fieldInput view decoded root _ 999 [0] (by decide) (by simp)

-- An earlier decoy batch frame is not accepted in place of the immediate bind.
def frames := [NativeGoldBatchFieldInputView.batchFrame view.data,NativeGoldBatchFieldInputView.typedFrame,
  NativeGoldBatchFieldInputView.primeFrame,NativeGoldBatchFieldInputView.fieldFrame view.count]
example : (NativeGoldBatchFieldInputView.parse (TranscriptFrame.encodeMany frames)).isSome = true := by decide +kernel
example : (NativeGoldBatchFieldInputView.parse (TranscriptFrame.encodeMany
    [NativeGoldBatchFieldInputView.batchFrame view.data,⟨1,[],[]⟩,NativeGoldBatchFieldInputView.typedFrame,
      NativeGoldBatchFieldInputView.primeFrame,NativeGoldBatchFieldInputView.fieldFrame view.count])).isNone = true := by decide +kernel
example : (NativeGoldBatchFieldInputView.readCount (NativeGoldBatchFieldInputView.fieldFrame (usize 0))).isNone = true := by decide +kernel
example : (NativeGoldBatchFieldInputView.readCount ⟨4,NativeGoldBatchPrelude.randomLabel,
    TranscriptFrame.littleEndian 16 NativeFields.babyBearModulus ++ TranscriptFrame.littleEndian 8 18⟩).isNone = true := by decide +kernel
example : (NativeGoldBatchFieldInputView.readCount ⟨4,NativeGoldBatchPrelude.randomLabel,
    TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus ++ TranscriptFrame.littleEndian 7 18⟩).isNone = true := by decide +kernel
example : (NativeGoldBatchFieldInputView.parse (TranscriptFrame.encodeMany frames ++ [255])).isNone = true := by decide +kernel
example : (NativeGoldBatchFieldExposure.select step (.inl (),[NativeTranscript.Observation.output fieldInput 500 [0]])).isNone = true := by decide +kernel

-- The actual native parent encoder supplies the explicit framing obligations.
def parentParsed := TranscriptFrame.decodeAll ctx.parent.input
theorem parentPresent : parentParsed.isSome = true := by decide +kernel
def parentFrames := parentParsed.get parentPresent
theorem parentDecoded : TranscriptFrame.decodeAll ctx.parent.input = some parentFrames := (Option.some_get parentPresent).symm
example : ∃ context : NativeRootMessage.Digest,
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      let nativeView : NativeGoldBatchFieldInputView.View := ⟨parentFrames,⟨context,ctx.root,ctx.queries,ctx.values⟩,work.geometry.randomCount⟩
      nativeView.phase ctx.parent.profile = NativeGoldBatchRandomLaw.phase work ∧
        NativeGoldBatchFieldInputView.parse fieldInput = some nativeView := by
  have sound := TranscriptFrame.decodeAll_sound ctx.parent.input parentFrames parentDecoded
  exact NativeGoldBatchFieldExposure.prepared_phase ctx world work prepared parentFrames sound.2 sound.1 (by decide +kernel)

-- The column nonce exposes exactly its field prefix and raw receipt quote.
def columnInput := NativeGoldBatchColumnRequestLaw.input ctx work world
def linkParsed := NativeGoldBatchChallengeLink.parse columnInput
theorem linkPresent : linkParsed.isSome = true := by decide +kernel
def link := linkParsed.get linkPresent
example : link.field.count.val = 18 ∧ link.field.data.root = ctx.root ∧ link.column.opening.evaluations = ctx.opening.evaluations ∧ link.receipt.length = 80 := by decide +kernel
example : (link.field.phase root).pending.input = fieldInput := by decide +kernel
example : link.receipt.take 16 = TranscriptFrame.littleEndian 16 work.state.phase.consumed.length ∧
    link.receipt.drop 16 = bytes world (NativeFieldReceipt.input work.state.phase) 0 64 := by decide +kernel

-- A syntactically valid quote is not assumed to be a genuine receipt.
def fakeReceipt : Input := List.replicate 80 255
def fakeColumn : NativeIndexInputView.View := ⟨view.frames ++ [NativeGoldBatchChallengeLink.receiptFrame fakeReceipt,
  NativeGoldBatchColumnInputView.responseFrame ctx.opening],NativeGoldBatchColumns.label,ctx.parameters.code.blocks,ctx.parameters.queries⟩
example : (NativeGoldBatchChallengeLink.parse (TranscriptFrame.encodeMany fakeColumn.frames)).isSome = true := by decide +kernel
example : fakeReceipt ≠ (NativeTranscript.receipt world work.state.phase.consumed).run.1 := by decide +kernel
example : (NativeGoldBatchChallengeLink.readColumn ⟨{fakeColumn with before := view.frames ++
    [NativeGoldBatchChallengeLink.receiptFrame (List.replicate 79 255),NativeGoldBatchColumnInputView.responseFrame ctx.opening]},ctx.opening⟩).isNone = true := by decide +kernel

-- Both machine time and candidate budgets remain unbounded in the charge.
example (prelude : World → NativeTranscript.Execution Unit) (rp : ObservationReplay.Replayable prelude)
    (bad : (packet : NativeIndexExposureRisk.Packet Unit Unit) → (view : NativeGoldBatchFieldInputView.View) →
      (Fin view.count.val → NativeFields.Goldilocks) → Prop) :
    law {oracle | ∃ fuel, NativeGoldBatchFieldExposure.event root step bad
      (CausalExposureLifetime.history prelude id step fuel oracle).run oracle} ≤
        ∫⁻ oracle, NativeGoldBatchFieldExposure.totalCharge prelude id step bad oracle ∂law := by
  simpa only [Set.empty_union,measure_empty,zero_add] using
    NativeGoldBatchFieldExposure.lifetime_le rp id root step bad ∅
end
end HasteBootsFieldInputSmoke
