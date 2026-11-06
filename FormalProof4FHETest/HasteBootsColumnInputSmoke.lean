module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchColumnExposure
import all FormalProof4FHETest.HasteBootsBatchOrderedSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law bytes)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsColumnInputSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx work world prepared)
open HasteBootsBatchMeaningSmoke (usize root)

def input := NativeGoldBatchColumnRequestLaw.input ctx work world
def parsed := NativeGoldBatchColumnInputView.parse input
theorem present : parsed.isSome = true := by decide +kernel
def view := parsed.get present
theorem decoded : NativeGoldBatchColumnInputView.parse input = some view := (Option.some_get present).symm
example : view.index.domain = ctx.parameters.code.blocks ∧ view.index.count.val = 3 := by decide +kernel
example : view.opening.test = ctx.opening.test ∧ view.opening.evaluations = ctx.opening.evaluations ∧ view.opening.columns.val = [] := by decide +kernel
example : NativePrequeryIndexLaw.requestInput (view.index.request root).transcript view.index.label view.index.domain view.index.count = input :=
  (NativeGoldBatchColumnInputView.parse_sound input view decoded root).1
example : ((run (view.index.request root).program world).run.1).map (fun sample => (sample.draws,sample.indices)) = some ([7,1,7],[1,7]) := by decide +kernel

-- Receipt knowledge is deliberately incomplete when the pending nonce is selected.
def receiptInput := NativeFieldReceipt.input work.state.phase
def past (oracle : World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← ObservationReplay.read oracle receiptInput 0 32
  pure (.inl ())
theorem replay : ObservationReplay.Replayable past :=
  ObservationReplay.bind_replay (ObservationReplay.read_replay receiptInput 0 32) (fun _ => ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit))
example : ¬ NativeFieldReceipt.Known (past world).run.2 work.state.phase := by
  intro complete
  have member := complete ⟨63,by decide⟩
  obtain ⟨entry,inLog,coordinate⟩ := Finset.mem_biUnion.mp member
  have same := List.mem_toFinset.mp inLog
  change entry ∈ [NativeTranscript.Observation.output receiptInput 0 (bytes world receiptInput 0 32)] at same
  simp only [List.mem_singleton] at same
  subst entry
  have bound := (NativeShakeProjection.output_coordinate _ _ _ _).mp coordinate
  rw [InputIndexedOracle.bytes_length] at bound
  have impossible : (63 : ℕ) < 32 := bound.2.2
  omega

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read input 999 1 (fun _ => ())
theorem first : CausalStreamExposure.firstRead step (past world).run = some input := by decide +kernel
theorem selected : NativeGoldBatchColumnExposure.selectView step (past world).run = some view := by
  simp only [NativeGoldBatchColumnExposure.selectView,first,Option.bind_eq_bind,Option.bind_some,decoded]
  have label : view.index.label = NativeGoldBatchColumns.label := by decide +kernel
  have positive : 0 < view.index.count.val := by decide +kernel
  simp only [label,positive,and_true,ite_true]
example : NativeIndexExposureRisk.eligible step (past world).run (view.index.request root) :=
  NativeGoldBatchColumnExposure.selected_eligible root step (past world).run _
    (by simp only [NativeGoldBatchColumnExposure.select,selected,Option.map_some])

def bad (_ : NativeIndexExposureRisk.Packet Unit Unit) (_ : NativeGoldBatchColumnInputView.View) (result : NativeIndexExposureRisk.Result) : Prop :=
  result.1.map (fun sample => (sample.draws,sample.indices)) = some ([7,1,7],[1,7])
example : NativeGoldBatchColumnExposure.event root step bad (past world).run world := by
  apply (NativeGoldBatchColumnExposure.event_selected root step bad (past world).run world view selected).mpr
  change ((run (view.index.request root).program world).run.1).map (fun sample => (sample.draws,sample.indices)) = some ([7,1,7],[1,7])
  decide +kernel
example : (law[|{oracle | (past oracle).run = (past world).run}])
    {oracle | NativeGoldBatchColumnExposure.event root step bad (past oracle).run oracle} =
      NativeGoldBatchColumnExposure.risk root step bad (past world).run :=
  NativeGoldBatchColumnExposure.conditional_event root step bad replay world

-- A wider integer alias, trailing payload and a truncated fixed integer are rejected.
example : (NativeIndexInputView.readU64 [0,0,0,0,0,0,0]).isNone = true := by decide +kernel
example : (NativeIndexInputView.readU64 [0,0,0,0,0,0,0,0,0]).isNone = true := by decide +kernel
example : (NativeGoldBatchColumnInputView.readResponse
    ⟨1,NativeTranscript.utf8 "mw batch linear responses",[251,0,0,0]⟩).isNone = true := by decide +kernel
example : (NativeGoldBatchColumnInputView.readResponse
    ⟨1,NativeTranscript.utf8 "mw batch linear responses",[0,0,0]⟩).isNone = true := by decide +kernel

def suffix (domain byteCount : ℕ) : List TranscriptFrame.Frame :=
  [⟨1,NativeTranscript.utf8 "index domain",TranscriptFrame.littleEndian 8 domain⟩,
   ⟨2,NativeGoldBatchColumns.label,TranscriptFrame.littleEndian 8 byteCount⟩]
example : (NativeIndexInputView.parse (TranscriptFrame.encodeMany (suffix 32 24))).isSome = true := by decide +kernel
example : (NativeIndexInputView.parse (TranscriptFrame.encodeMany (suffix 32 9))).isNone = true := by decide +kernel
example : (NativeIndexInputView.parse (TranscriptFrame.encodeMany (suffix 3 24))).isNone = true := by decide +kernel
example : (NativeIndexInputView.parse (TranscriptFrame.encodeMany (suffix 32 24) ++ [255])).isNone = true := by decide +kernel

-- Correct suffix framing does not suffice when the response frame is absent.
example : (NativeGoldBatchColumnInputView.parse (TranscriptFrame.encodeMany (suffix 32 24))).isNone = true := by decide +kernel

-- The native label is checked by the causal selector.
def wrongInput := NativeGoldBatchResponseBinding.input (NativeGoldBatchColumnRequestLaw.parent work world) [] ctx.parameters.code.blocks ctx.parameters.queries ctx.opening
def wrongStep (_ : Unit) : OracleMachine.Command Unit Unit := .read wrongInput 0 1 (fun _ => ())
example : (NativeGoldBatchColumnExposure.selectView wrongStep (.inl (),[])).isNone = true := by decide +kernel

-- Prior exposure to this exact stream prevents selection even at a different offset.
def repeated : NativeIndexExposureRisk.Packet Unit Unit := (.inl (),[NativeTranscript.Observation.output input 17 (bytes world input 17 1)])
example : (NativeGoldBatchColumnExposure.selectView step repeated).isNone = true := by decide +kernel

abbrev Position := Fin (2^5)
def raw (_ : NativeIndexExposureRisk.Packet Unit Unit) (_ : NativeGoldBatchColumnInputView.View) (_ : Fin 6) (_ : Position) : ℕ := 0
def claimed (_ : NativeIndexExposureRisk.Packet Unit Unit) (_ : NativeGoldBatchColumnInputView.View) (test : Fin 6) (position : Position) : ℕ := if test.val = 5 ∧ position.val = 0 then 1 else 0
example : NativeGoldBatchColumnExposure.risk root step (fun current decoded result => (result.1.bind (fun sample =>
      NativeGoldPcsDraws.typed 5 decoded.index.count.val sample.draws)).elim False
        (fun draw => ∀ test, ColumnOpening.Agrees (raw current decoded test) (claimed current decoded test) draw)) (past world).run ≤
      ColumnOpening.missBound Position 3 1 := by
  have quota : view.index.count.val = 3 := by decide +kernel
  have bound := NativeGoldBatchColumnExposure.shared_risk_bound root step (past world).run view selected 5
    (by decide +kernel) raw claimed 1 ⟨5,by decide +kernel⟩
  simpa only [quota] using bound
-- Every raw group is recovered, including a field-equal lazy word in group two.
def lazyRow : NativeLookupRequestWire.Row := ⟨[usize NativeFields.goldilocksModulus,0,0,0,0,0],by decide⟩
def groups : NativeGoldBatchOpening.Opening := {ctx.opening with evaluations := ⟨[ctx.opening.test,lazyRow],by decide⟩}
def groupInput := NativeGoldBatchResponseBinding.input (NativeGoldBatchColumnRequestLaw.parent work world)
  NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries groups
example : (NativeGoldBatchColumnInputView.parse groupInput).map (fun decoded =>
    decoded.opening.evaluations.val.map (fun row => (row.val[0]?.getD 0).val)) = some [0,NativeFields.goldilocksModulus] := by decide +kernel
example : lazyRow.val.map NativeFieldRepresentation.goldValue = ctx.opening.test.val.map NativeFieldRepresentation.goldValue := by decide +kernel

-- The lifetime theorem uses this concrete parser, with no supplied request selector.
example (prelude : World → NativeTranscript.Execution Unit) (replay : ObservationReplay.Replayable prelude) :
    law {oracle | ∃ fuel, NativeGoldBatchColumnExposure.event root step bad
      (CausalExposureLifetime.history prelude id step fuel oracle).run oracle} ≤
        ∫⁻ oracle, NativeIndexExposureRisk.totalCharge prelude id step (NativeGoldBatchColumnExposure.select root step)
          (NativeGoldBatchColumnExposure.predicate step bad) oracle ∂law := by
  simpa only [Set.empty_union,measure_empty,zero_add] using
    NativeGoldBatchColumnExposure.lifetime_le replay id root step bad ∅

-- Native batch parameter validation rules out a zero column quota.
def emptyOpening : NativeGoldBatchOpening.Opening := ⟨⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩⟩
def zeroInput := NativeGoldBatchResponseBinding.input ⟨[],root⟩ NativeGoldBatchColumns.label (usize 32) (usize 0) emptyOpening
def zeroStep (_ : Unit) : OracleMachine.Command Unit Unit := .read zeroInput 0 1 (fun _ => ())
example : (NativeGoldBatchColumnExposure.selectView zeroStep (.inl (),[])).isNone = true := by decide +kernel

end
end HasteBootsColumnInputSmoke
