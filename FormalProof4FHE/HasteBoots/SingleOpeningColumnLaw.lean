module
public import FormalProof4FHE.HasteBoots.SingleOpeningRandomLaw
public import FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
public import FormalProof4FHE.HasteBoots.NativeGoldBatchResponseBinding
@[expose] public section

/-! Actual single-opening response binding and conditional ordered-column
laws. Native receipt replay pins the parent on the posterior fiber. Cached
coordinates are retained for partial prequeries; first positive read gives the
joint uniform special case. Global early-receipt/first-exposure coverage remains
separate. The single response frame is never replaced with a batch frame. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningColumnLaw
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsOpening (Opening)
open NativeGoldBlockCode (logSize)
open NativeTranscript (Transcript)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input World law)
open SingleOpeningSamplingReceipt (Receipt)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def payload (opening : Opening) : Input := NativeGoldPcsWire.responses opening.test opening.evaluation

def boundInput (parent : Transcript) (label : Input) (domain count : Usize) (opening : Opening) : Input :=
  NativePrequeryIndexLaw.requestInput (NativeGoldPcsWire.bindResponses parent opening.test opening.evaluation) label domain count

theorem boundInput_eq (parent : Transcript) (label : Input) (domain count : Usize) (opening : Opening) :
    boundInput parent label domain count opening = parent.input ++
      TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "mw linear responses",payload opening⟩ ++
      TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "index domain",TranscriptFrame.littleEndian 8 domain.val⟩ ++
      TranscriptFrame.encode ⟨2,label,TranscriptFrame.littleEndian 8 (count.val*8)⟩ := rfl

theorem payload_eq_iff (first second : Opening) : payload first = payload second ↔
    first.test = second.test ∧ first.evaluation = second.evaluation := by
  constructor
  · intro same
    have paired := NativeGoldPcsWire.responseCodec.encode_injective same
    exact Prod.mk.inj paired
  · rintro ⟨test,evaluation⟩
    simp only [payload,test,evaluation]

/-- Complete SHAKE input equality binds the two original raw response rows.
Field equality is insufficient to rewrite this input. -/
theorem boundInput_eq_iff (parent : Transcript) (label : Input) (domain count : Usize) (first second : Opening) :
    boundInput parent label domain count first = boundInput parent label domain count second ↔
      first.test = second.test ∧ first.evaluation = second.evaluation := by
  constructor
  · intro same
    rw [boundInput_eq,boundInput_eq] at same
    have frames := List.append_cancel_left (List.append_cancel_right (List.append_cancel_right same))
    exact (payload_eq_iff first second).mp (NativeGoldBatchResponseBinding.frame_message 1 _ _ _ frames)
  · intro same
    rw [boundInput_eq,boundInput_eq,(payload_eq_iff first second).mpr same]

variable {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}

def transcript (receipt : Receipt ctx world work sample) (other : World) : Transcript :=
  NativeGoldPcsWire.bindResponses (receipt.parent other) ctx.opening.test ctx.opening.evaluation

def input (receipt : Receipt ctx world work sample) (other : World) : Input :=
  NativePrequeryIndexLaw.requestInput (transcript receipt other) NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries

def values (receipt : Receipt ctx world work sample) (other : World) :=
  NativeIndexFirstReadLaw.values (logSize ctx.parameters.code) (transcript receipt other)
    NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries other

theorem prepared_request (receipt : Receipt ctx world work sample) :
    (run (NativeIndexRequest.request (transcript receipt world) NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries) world).run.1 = some sample :=
  receipt.column_request

theorem prepared_check (receipt : Receipt ctx world work sample) :
    NativeIndexRequest.check ctx.parameters.code.blocks ctx.parameters.queries = true :=
  NativeIndexRequest.accepted_check _ _ _ _ world sample (prepared_request receipt)

theorem values_original (receipt : Receipt ctx world work sample) :
    values receipt world = NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val sample.draws := by
  unfold values NativeIndexFirstReadLaw.values
  rw [prepared_request receipt]
  rfl

/-- The law's vector is the same full ordered result retained by the native
rectangular view, not merely a vector with the same distinct worker indices. -/
theorem values_typed (receipt : Receipt ctx world work sample)
    (draw : Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code))
    (typed : NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val sample.draws = some draw) :
    values receipt world = some draw := by rw [values_original receipt,typed]

theorem response_bound (receipt : Receipt ctx world work sample) (other : World) (opening : Opening) :
    boundInput (receipt.parent other) NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries opening = input receipt other ↔
      opening.test = ctx.opening.test ∧ opening.evaluation = ctx.opening.evaluation :=
  boundInput_eq_iff _ _ _ _ opening ctx.opening

/-- Exact posterior law after arbitrary partial prequeries. Known byte
coordinates retain their original answers through the common cache mask. -/
theorem conditional_cached {P : Type} (receipt : Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past)
    (known : NativeFieldReceipt.Known (past world).run.2 receipt.state.phase)
    (event : (Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code)) → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | (values receipt other).elim False event} =
      Pr{let raw ← $ᵗ (Fin (ctx.parameters.queries.val*8) → InputIndexedOracle.Byte)}[
        event (NativeIndexRequest.typedDraws (logSize ctx.parameters.code) ctx.parameters.queries.val
          (CachedOracleResponse.mask (ObservationReplay.footprint (past world).run.2) world
            (CachedOracleResponse.shakeCoordinates (input receipt world) 0 (ctx.parameters.queries.val*8)) raw))] := by
  have power := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  have fixed := NativePrequeryIndexLaw.conditional_event replay world (input receipt world) 0 (logSize ctx.parameters.code)
    ctx.parameters.queries.val event
  refine Eq.trans ?_ fixed
  apply NativeShakeProjection.conditional_event_congr replay world
  intro other same
  have parentEq := receipt.parent_on_fiber replay other known same
  change (NativeIndexFirstReadLaw.values _ (transcript receipt other) _ _ _ other).elim False event ↔ _
  rw [show transcript receipt other = transcript receipt world from congrArg
    (fun parent => NativeGoldPcsWire.bindResponses parent ctx.opening.test ctx.opening.evaluation) parentEq,
    NativeIndexFirstReadLaw.values_run _ _ _ _ _ (prepared_check receipt) power other]
  rfl

/-- At the actual next first positive read, all native ordered columns are
jointly uniform. The completed native receipt fixes its world-dependent parent. -/
theorem conditional_uniform {S A : Type} (receipt : Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (known : NativeFieldReceipt.Known (past world).run.2 receipt.state.phase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (input receipt world))
    (event : (Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code)) → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | (values receipt other).elim False event} =
      Pr{let draw ← $ᵗ (Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code))}[event draw] := by
  have power := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  have fixed := NativeIndexFirstReadLaw.conditional_uniform step replay world (logSize ctx.parameters.code)
    (transcript receipt world) NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries (prepared_check receipt) power selected event
  refine Eq.trans ?_ fixed
  apply NativeShakeProjection.conditional_event_congr replay world
  intro other same
  have parentEq := receipt.parent_on_fiber replay other known same
  change (NativeIndexFirstReadLaw.values _ (transcript receipt other) _ _ _ other).elim False event ↔ _
  simp only [transcript,parentEq]

/-- Every test/lane uses this one column vector. A single disagreement witness
suffices for the miss bound; no number-of-lanes factor is added. -/
theorem shared_bound {S A Test Symbol : Type} [DecidableEq Symbol] (receipt : Receipt ctx world work sample)
    (origin : CacheBackedSingleOpening.Origin ctx) (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (known : NativeFieldReceipt.Known (past world).run.2 receipt.state.phase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (input receipt world))
    (raw claimed : Test → Fin (2^logSize ctx.parameters.code) → Symbol) (distance : ℕ)
    (witness : ∃ test, distance ≤ hammingDist (raw test) (claimed test)) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values receipt other).elim False (fun draw => ∀ test, ColumnOpening.Agrees (raw test) (claimed test) draw)} ≤
        ColumnOpening.missBound (Fin (2^logSize ctx.parameters.code)) ctx.parameters.queries.val distance := by
  rw [conditional_uniform receipt origin step replay known selected]
  exact ColumnOpening.shared_bound raw claimed ctx.parameters.queries.val distance witness

end
end FormalProof4FHE.HasteBoots.SingleOpeningColumnLaw
