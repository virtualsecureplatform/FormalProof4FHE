module
public import FormalProof4FHE.HasteBoots.SharedOpeningAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldWeightLayout
public import FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
@[expose] public section

/-! One rectangular interpretation of the actual single-opening helper call.
Source rows are reindexed by original left cell and packing lane. Native test
and response encodings retain their own independent code-symbol width. These
are deterministic analysis projections, not new verifier inputs or transcripts. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningRectangularData
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (logSize description)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

abbrev Row (ctx : Context) := Fin (2^ctx.parameters.leftVariables.val) × Fin ctx.parameters.width.val

theorem geometry (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    NativeBrakedownParameters.build description ctx.parameters = some work.geometry :=
  (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work prepared).1

theorem dimensions (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    ctx.parameters.width.val ≠ 0 ∧ ctx.parameters.width.val*ctx.parameters.width.val < 2^64 ∧
      work.geometry.rows = 2^ctx.parameters.leftVariables.val*ctx.parameters.width.val := by
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters work.geometry (geometry ctx world work prepared)
  refine ⟨spec.basic.1,?_,?_⟩
  · have bound := spec.allocations.2.2.2.2.1
    have positive : 0 < 2^ctx.parameters.leftVariables.val := pow_pos (by decide) _
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ positive)) bound
  · rw [spec.computed]
    rfl

theorem width (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : work.width = ctx.parameters.width.val :=
  (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work prepared).2.1

theorem query_length (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : ctx.query.models.length = ctx.parameters.numVariables.val := by
  obtain ⟨data⟩ := SingleOpeningFinishing.prepared_encoding ctx world work prepared
  exact data.size

theorem message_length (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    ctx.parameters.code.messageLength.val = 2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val) :=
  (NativeBrakedownParameters.build_spec description ctx.parameters work.geometry (geometry ctx world work prepared)).code.1

theorem prefix_length (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    ((ctx.query.models.take ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val)).length =
      ctx.parameters.leftVariables.val := by
  have bound := (NativeBrakedownParameters.build_spec description ctx.parameters work.geometry (geometry ctx world work prepared)).basic.2.1
  rw [List.length_map,List.length_take,query_length ctx world work prepared,Nat.min_eq_left bound]

def rowEquiv (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : Row ctx ≃ Fin work.geometry.rows :=
  finProdFinEquiv.trans (finCongr (dimensions ctx world work prepared).2.2.symm)

theorem rowEquiv_val (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (row : Row ctx) :
    (rowEquiv ctx world work prepared row).val = row.1.val*ctx.parameters.width.val+row.2.val := by
  change row.2.val+ctx.parameters.width.val*row.1.val = _
  ring

def left (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (cell : Fin (2^ctx.parameters.leftVariables.val)) :=
  FlatMatrixFold.weights ((ctx.query.models.take ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val))
    (Fin.cast (congrArg (fun n => 2^n) (prefix_length ctx world work prepared).symm) cell)

def right (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (index : Fin ctx.parameters.code.messageLength.val) :=
  NativeGoldSuffixFinishing.right ctx.parameters ctx.query
    (Fin.cast ((message_length ctx world work prepared).trans
      (congrArg (fun n => 2^n) (NativeGoldSuffixFinishing.suffix_length ctx.parameters ctx.query (query_length ctx world work prepared)).symm)) index)

def messages (ctx : Context) (words : List GoldWord) (lane : Fin ctx.parameters.width.val) :
    Fin ctx.parameters.code.messageLength.val → Goldilocks :=
  fun index => goldValue (words[lane.val*ctx.parameters.code.messageLength.val+index.val]?.getD 0)

def claimed (ctx : Context) (lane : Fin ctx.parameters.width.val) : Goldilocks :=
  goldValue (ctx.claimed.val[lane.val]?.getD 0)

def Lane (ctx : Context) (words : List GoldWord) (lane : ℕ) :
    Fin (2^logSize ctx.parameters.code) → Fin ctx.parameters.code.blockWidth.val → Goldilocks :=
  fun symbol component => goldValue (words[lane*(2^logSize ctx.parameters.code*ctx.parameters.code.blockWidth.val)+
    symbol.val*ctx.parameters.code.blockWidth.val+component.val]?.getD 0)

theorem lane_word (ctx : Context) (planRoot : NativeGoldSolinas.Word) (words : List GoldWord) (lane : ℕ) :
    Lane ctx words lane = NativeGoldResponseMeaning.laneWord (NativeGoldBlockCode.encoding ctx.parameters.code planRoot) words lane := by
  funext symbol component
  change goldValue (words[lane*(2^logSize ctx.parameters.code*ctx.parameters.code.blockWidth.val)+
      symbol.val*ctx.parameters.code.blockWidth.val+component.val]?.getD 0) =
    goldValue (words[lane*(2^logSize ctx.parameters.code*ctx.parameters.code.blockWidth.val)+
      (finProdFinEquiv (symbol,component)).val]?.getD 0)
  rw [finProdFinEquiv_apply_val]
  congr 3
  ring

/-- The single prepared structured vector is the ordered original left query. -/
theorem structured (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    NativeGoldPcsArithmetic.structured ctx.parameters.width.val ctx.parameters.leftVariables.val ctx.query.models = some work.structured := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world work prepared
  have original := (NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry state weights sample planRoot test evaluation encoded).1
  exact (NativeGoldPcsColumns.columns_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry state weights sample original).choose_spec.2.1

def Weights (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (words : List GoldWord)
    (lane : Fin ctx.parameters.width.val) (row : Row ctx) : Goldilocks :=
  NativeGoldColumnChecks.view words (lane.val*work.geometry.rows+(rowEquiv ctx world work prepared row).val)

theorem structured_weights (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    Weights ctx world work prepared work.structured = RectangularMatrixResponse.weights (left ctx world work prepared) := by
  obtain ⟨data⟩ := SingleOpeningFinishing.prepared_encoding ctx world work prepared
  have dims := dimensions ctx world work prepared
  have prefixSize : (ctx.query.models.take ctx.parameters.leftVariables.val).length = ctx.parameters.leftVariables.val := by
    simpa only [List.length_map] using prefix_length ctx world work prepared
  funext lane row
  have value := NativeGoldWeightLayout.structured_get ctx.parameters.width.val ctx.parameters.leftVariables.val ctx.query.models work.structured
    dims.1 dims.2.1 (fun pair member => data.valid pair (List.mem_of_mem_take member)) (structured ctx world work prepared)
    lane (Fin.cast (congrArg (fun n => 2^n) (prefix_length ctx world work prepared).symm) row.1) row.2
  simpa only [Weights,rowEquiv_val,NativeGoldColumnChecks.view,dims.2.2,prefixSize,Fin.val_cast,
    RectangularMatrixResponse.weights,left,Nat.add_assoc] using value

/-- Both original computed responses encode the native padded messages, with
packing and code widths kept independent. -/
theorem encoded_messages (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx) :
    (fun lane : Fin ctx.parameters.width.val => Lane ctx work.test lane.val) =
      (fun lane => BlockEncoder.encode (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx ctx.opening.test.val lane))) ∧
    (fun lane : Fin ctx.parameters.width.val => Lane ctx work.evaluation lane.val) =
      (fun lane => BlockEncoder.encode (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx ctx.opening.evaluation.val lane))) := by
  obtain ⟨data⟩ := SingleOpeningFinishing.prepared_encoding ctx world work prepared
  have dims := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  constructor
  · funext lane
    rw [lane_word ctx data.planRoot]
    exact NativeGoldResponseMessages.lanes_padded _ ctx.parameters.code.messageBlocks.val ctx.parameters.width.val _ _ data.test
      (Nat.le_of_lt dims.2.1) dims.2.2.1 origin.primitive lane
  · funext lane
    rw [lane_word ctx data.planRoot]
    exact NativeGoldResponseMessages.lanes_padded _ ctx.parameters.code.messageBlocks.val ctx.parameters.width.val _ _ data.evaluation
      (Nat.le_of_lt dims.2.1) dims.2.2.1 origin.primitive lane

theorem accepted_claim {Memory : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent) :
    claimed ctx = RectangularMatrixResponse.finishMessage (right ctx world work prepared) (messages ctx ctx.opening.evaluation.val) := by
  have verified := (NativeGoldPcsProgram.accepted_flags ctx choose fuel memory world work completion executed parent accepted).2.1
  obtain ⟨data⟩ := SingleOpeningFinishing.prepared_encoding ctx world work prepared
  have native := NativeGoldSuffixFinishing.claim_message ctx.parameters ctx.query ctx.opening.evaluation.val ctx.claimed data.valid verified
  have transfer := NativeGoldSuffixFinishing.transport_message ctx.parameters ctx.query
    (NativeGoldBlockCode.encoding ctx.parameters.code data.planRoot) ctx.opening.evaluation.val data.size data.shape
  rw [← transfer] at native
  have rightEq : NativeGoldSuffixFinishing.encodedRight ctx.parameters ctx.query
      (NativeGoldBlockCode.encoding ctx.parameters.code data.planRoot) data.size data.shape = right ctx world work prepared := by
    rfl
  have messagesEq : (fun lane : Fin ctx.parameters.width.val => NativeGoldResponseMessages.message
      (NativeGoldBlockCode.encoding ctx.parameters.code data.planRoot) ctx.opening.evaluation.val lane.val) =
      messages ctx ctx.opening.evaluation.val := by
    rfl
  rw [rightEq,messagesEq] at native
  change ctx.claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishMessage
    (right ctx world work prepared) (messages ctx ctx.opening.evaluation.val)) at native
  funext lane
  rcases lane with ⟨lane,laneBound⟩
  have entry := congrArg (fun words => (words[lane]?).getD (goldValue 0)) native
  simpa only [claimed,List.getElem?_map,Option.getD_map,List.getElem?_ofFn,laneBound,reduceDIte,Option.getD_some] using entry

end
end FormalProof4FHE.HasteBoots.SingleOpeningRectangularData
