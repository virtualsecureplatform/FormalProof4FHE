module
import all FormalProof4FHE.HasteBoots.NativeEarlyReceiptPrefixRisk
import all FormalProof4FHETest.HasteBootsFieldInputSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law bytes block)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsEarlyReceiptSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx work world prepared)
open HasteBootsBatchMeaningSmoke (root)

def columnInput := NativeGoldBatchColumnRequestLaw.input ctx work world
def receiptKey := NativeReceiptPrefixView.key work.state.phase.consumed
-- Just the last digest byte was read, not the complete receipt.
def past (oracle : World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← ObservationReplay.read oracle receiptKey 63 1
  pure (.inl ())
theorem replay : ObservationReplay.Replayable past :=
  ObservationReplay.bind_replay (ObservationReplay.read_replay receiptKey 63 1) (fun _ => ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit))
def step (_ : Unit) : OracleMachine.Command Unit Unit := .read columnInput 999 1 (fun _ => ())
def selectedOption := NativeEarlyReceiptPrefixRisk.select step (past world).run
theorem present : selectedOption.isSome = true := by decide +kernel
def view := selectedOption.get present
theorem selected : NativeEarlyReceiptPrefixRisk.select step (past world).run = some view := (Option.some_get present).symm

theorem fieldInput : NativeEarlyReceiptPrefixRisk.fieldInput view = (NativeGoldBatchRandomLaw.phase work).pending.input := by decide +kernel
example (consumed : Input) : NativeEarlyReceiptPrefixRisk.fieldInput view ≠ NativeReceiptPrefixView.key consumed :=
  NativeEarlyReceiptPrefixRisk.selected_not_receipt step (past world).run view selected consumed
example : view.field.count.val = 18 := by decide +kernel
example : CausalStreamExposure.seen (past world).run.2 (NativeEarlyReceiptPrefixRisk.fieldInput view) = false :=
  NativeEarlyReceiptPrefixRisk.selected_unseen step (past world).run view selected
example : ¬ NativeFieldReceipt.Known (past world).run.2 work.state.phase := by
  intro complete
  have member := complete ⟨0,by decide⟩
  obtain ⟨entry,inLog,coordinate⟩ := Finset.mem_biUnion.mp member
  have same := List.mem_toFinset.mp inLog
  change entry ∈ [NativeTranscript.Observation.output receiptKey 63 (bytes world receiptKey 63 1)] at same
  simp only [List.mem_singleton] at same
  subst entry
  have bound := (NativeShakeProjection.output_coordinate _ _ _ _).mp coordinate
  have impossible : (63 : ℕ) ≤ 0 := bound.2.1
  omega

theorem known : (.inl (receiptKey,63) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.footprint (past world).run.2 := by
  apply Finset.mem_biUnion.mpr
  refine ⟨NativeTranscript.Observation.output receiptKey 63 (bytes world receiptKey 63 1),?_,?_⟩
  · apply List.mem_toFinset.mpr
    change _ ∈ [NativeTranscript.Observation.output receiptKey 63 (bytes world receiptKey 63 1)]
    exact List.mem_singleton_self _
  · apply (NativeShakeProjection.output_coordinate _ _ _ _).mpr
    simp only [InputIndexedOracle.bytes_length]
    exact ⟨True.intro,by omega,by omega⟩

-- Actual native completion supplies the72-byte prefix, not a guessed success floor.
theorem retained : ∃ tail, work.state.phase.consumed =
    List.ofFn (block world (NativeEarlyReceiptPrefixRisk.fieldInput view) 0 72) ++ tail := by
  rw [fieldInput]
  exact NativeFieldConsumedPrefix.gold_prepared_72 ctx world work prepared (by decide +kernel)

theorem event : NativeEarlyReceiptPrefixRisk.event 72 step (past world).run world := by
  obtain ⟨tail,same⟩ := retained
  have observed := known
  change (.inl (NativeReceiptPrefixView.key work.state.phase.consumed,63) : InputIndexedOracle.Coordinate) ∈ _ at observed
  rw [same] at observed
  exact NativeEarlyReceiptPrefixRisk.known_receipt_event 72 step (past world).run world view selected tail 63 observed

-- Coverage can also use the recovered collector's completion directly.
example : NativeEarlyReceiptPrefixRisk.event 72 step (past world).run world := by
  apply NativeEarlyReceiptPrefixRisk.completed_receipt_event 72 step (past world).run world view selected root 18 63
  · decide +kernel
  · decide +kernel
  · have same : (NativeFieldVector.execute NativeFields.goldilocksModulus 18
        (NativeFieldVector.initial (view.field.phase root) view.field.count.val) world).1.phase.consumed = work.state.phase.consumed := by decide +kernel
    rw [same]
    exact known

theorem singleGuess : (NativeReceiptPrefixView.guesses 72 (past world).run.2).card = 1 := by
  obtain ⟨tail,same⟩ := retained
  have positive : bytes world receiptKey 63 1 ≠ [] := by
    intro empty
    have length := InputIndexedOracle.bytes_length world receiptKey 63 1
    rw [empty] at length
    contradiction
  change (([NativeTranscript.Observation.output receiptKey 63 (bytes world receiptKey 63 1)].filterMap
    (NativeReceiptPrefixView.candidate 72)).toFinset).card = 1
  have parsed : NativeReceiptPrefixView.candidate 72 (NativeTranscript.Observation.output receiptKey 63 (bytes world receiptKey 63 1)) =
      some (block world (NativeEarlyReceiptPrefixRisk.fieldInput view) 0 72) := by
    change NativeReceiptPrefixView.candidate 72 (NativeTranscript.Observation.output (NativeReceiptPrefixView.key work.state.phase.consumed) 63 (bytes world receiptKey 63 1)) = _
    rw [same]
    exact NativeReceiptPrefixView.read_candidate 72 _ tail _ 63 positive
  simp only [List.filterMap_cons,parsed,List.filterMap_nil,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.card_singleton]
example : NativeEarlyReceiptPrefixRisk.risk 72 step (past world).run = 1/(2 : ENNReal)^576 := by
  rw [NativeEarlyReceiptPrefixRisk.gold_risk step (past world).run view selected,singleGuess]
  simp only [Nat.cast_one]
example : (law[|{oracle | (past oracle).run = (past world).run}])
    {oracle | NativeEarlyReceiptPrefixRisk.event 72 step (past oracle).run oracle} = 1/(2 : ENNReal)^576 := by
  rw [NativeEarlyReceiptPrefixRisk.conditional_event 72 step replay world,
    NativeEarlyReceiptPrefixRisk.gold_risk step (past world).run view selected,singleGuess]
  simp only [Nat.cast_one]

-- Prior field exposure moves this input out of the early-field case.
def late : NativeIndexExposureRisk.Packet Unit Unit := ((past world).run.1,
  (past world).run.2 ++ [NativeTranscript.Observation.output (NativeEarlyReceiptPrefixRisk.fieldInput view) 1000 [0]])
example : (NativeEarlyReceiptPrefixRisk.select step late).isNone = true := by decide +kernel
example : (NativeReceiptPrefixView.read 72 (NativeReceiptPrefixView.domain ++ List.replicate 71 0)).isNone = true := by decide +kernel
example : (NativeReceiptPrefixView.read 72 [1,2,3]).isNone = true := by decide +kernel
example : NativeReceiptPrefixView.guesses 72 [NativeTranscript.Observation.start receiptKey,NativeTranscript.Observation.output receiptKey 0 []] = ∅ := by
  simp only [NativeReceiptPrefixView.guesses,NativeReceiptPrefixView.candidate,ite_true,List.filterMap_cons,List.filterMap_nil,List.toFinset_nil]

-- A rejected candidate is retained in the consumed prefix.
def tinyParent := NativeTranscript.new [] root
def tinyPhase := (NativeTranscript.beginField tinyParent [] 3 2).run.1
def tinyWorld : World
  | .inr _ => 0
  | .inl (_,offset) => if offset = 0 then 3 else if offset = 1 then 1 else 2
example : (NativeFieldVector.execute 3 3 (NativeFieldVector.initial tinyPhase 2) tinyWorld).1.phase.consumed = [3,1,2] := by decide +kernel
example : ∃ tail, (NativeFieldVector.execute 3 3 (NativeFieldVector.initial tinyPhase 2) tinyWorld).1.phase.consumed =
    List.ofFn (block tinyWorld tinyPhase.pending.input 0 2) ++ tail :=
  NativeFieldConsumedPrefix.completed_prefix 3 3 2 tinyPhase tinyWorld
    (NativeTranscript.begin_coherent tinyWorld tinyParent [] 3 2) (by decide +kernel) 2 (by decide +kernel)
example (prelude : World → NativeTranscript.Execution Unit) (rp : ObservationReplay.Replayable prelude) :
    law {oracle | ∃ fuel, NativeEarlyReceiptPrefixRisk.event 72 step (CausalExposureLifetime.history prelude id step fuel oracle).run oracle} ≤
      ∫⁻ oracle, NativeEarlyReceiptPrefixRisk.totalCharge 72 prelude id step oracle ∂law := by
  simpa only [Set.empty_union,measure_empty,zero_add] using NativeEarlyReceiptPrefixRisk.lifetime_le 72 rp id step ∅
end
end HasteBootsEarlyReceiptSmoke
