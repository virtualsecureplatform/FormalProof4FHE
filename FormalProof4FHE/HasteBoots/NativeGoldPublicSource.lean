module
public import FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
public import FormalProof4FHE.HasteBoots.RawGoldColumnCost
public import FormalProof4FHE.HasteBoots.CompactSourceHistory
public import FormalProof4FHE.HasteBoots.NativeGoldExecutableExtraction
@[expose] public section

/-! Materialize the selected raw source from a frozen public hash log before
running matrix extraction. No future work, secret key, oracle-world argument or
hash callback is used. Selecting the correct original snapshot is a separate
interface; the complete-history entry point below computes that selection. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPublicSource
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize)
open NativeGoldBatchRectangularWeights (Row)
open NativeFields (Goldilocks)
open NativeFieldRepresentation (goldValue)
open ExecutableMerkleAvailability (Log)

/-- Measured reconstruction and field-row conversion after the incoming digest,
root and dummy adapters. Those function-to-storage adapters are not charged here. -/
def materializeWithCost (dummy root : Digest) (ctx : Context) (sourceLog : Log) :=
  let height := (Fin.ofNat 64 (logSize ctx.parameters.code)).val
  let storedLog := sourceLog.map (fun entry => (entry.1,PreparedMerklePayloads.store entry.2))
  let raw := CostedMerkleWord.prepareWord height (Vector.ofFn dummy) storedLog
    (PreparedMerklePayloads.store root)
  let result := RawGoldColumnCost.columns (2^(logSize ctx.parameters.code))
    (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)
    ctx.parameters.code.blockWidth.val raw.value
  SolverOperationCost.Run.mk result.value (raw.cost+result.cost+2)

def materialize (dummy root : Digest) (ctx : Context) (sourceLog : Log) :=
  (materializeWithCost dummy root ctx sourceLog).value

theorem materialize_get (dummy root : Digest) (ctx : Context) (sourceLog : Log)
    (pos : Fin (2^(logSize ctx.parameters.code)))
    (row : Fin (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val))
    (lane : Fin ctx.parameters.code.blockWidth.val) :
    (((materialize dummy root ctx sourceLog).get pos).get row).get lane =
      goldValue (((ExecutableMerkleAvailability.reconstruct
        (Fin.ofNat 64 (logSize ctx.parameters.code)).val dummy sourceLog root).get
        (Fin.ofNat (2^((Fin.ofNat 64 (logSize ctx.parameters.code)).val)) pos.val)).val[
          row.val*ctx.parameters.code.blockWidth.val+lane.val]?.getD 0) := by
  simp only [materialize,materializeWithCost,RawGoldColumnCost.columns_get,
    ExecutableMerkleAvailability.reconstruct]

def materializeBound (ctx : Context) (sourceLog : Log) : ℕ :=
  let height := (Fin.ofNat 64 (logSize ctx.parameters.code)).val
  let storedLog := sourceLog.map (fun entry => (entry.1,PreparedMerklePayloads.store entry.2))
  let n := 2^(logSize ctx.parameters.code)
  let rows := 2^ctx.parameters.leftVariables.val*ctx.parameters.width.val
  let lanes := ctx.parameters.code.blockWidth.val
  208*(PreparedMerklePayloads.storedInputBytes storedLog+storedLog.length)+
    (9*NativeFieldWire.columnDomain.length+944)*storedLog.length+
    2^height*CostedMerkleWord.perLeaf height storedLog.length storedLog.length+3*height+8+
    n*(RawGoldColumnCost.columnBound rows lanes+4)+3

theorem materializeWithCost_cost (dummy root : Digest) (ctx : Context) (sourceLog : Log) :
    (materializeWithCost dummy root ctx sourceLog).cost ≤ materializeBound ctx sourceLog := by
  let height := (Fin.ofNat 64 (logSize ctx.parameters.code)).val
  let storedLog := sourceLog.map (fun entry => (entry.1,PreparedMerklePayloads.store entry.2))
  have raw := CostedMerkleWord.prepareWord_cost height (Vector.ofFn dummy) storedLog
    (PreparedMerklePayloads.store root)
  have converted := RawGoldColumnCost.columns_cost (2^(logSize ctx.parameters.code))
    (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)
    ctx.parameters.code.blockWidth.val
    (CostedMerkleWord.prepareWord height (Vector.ofFn dummy) storedLog
      (PreparedMerklePayloads.store root)).value
  dsimp only [materializeWithCost,materializeBound]
  change _ ≤ _ at raw converted
  dsimp only [height,storedLog] at raw converted
  omega

def word (dummy root : Digest) (ctx : Context) (sourceLog : Log) :
    Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks :=
  let values := materialize dummy root ctx sourceLog
  fun pos row lane => (((values.get pos).get (finProdFinEquiv row)).get lane)

theorem word_eq_analysis (dummy context root : Digest) (ctx : Context) (sourceLog : Log) :
    word dummy root ctx sourceLog = NativeGoldBatchSelectedWord.word dummy context root ctx sourceLog := by
  funext pos row lane
  simp only [word,materialize_get,ExecutableMerkleAvailability.reconstruct_get,
    NativeGoldBatchSelectedWord.word,NativeGoldBatchSelectedWord.values,NativeGoldBatchSelectedWord.atTag,
    NativeGoldRawAvailability.frozenValue,NativeGoldRawAvailability.frozenRaw,NativeGoldColumnChecks.view,
    NativeMerkleShapeFamily.height,finProdFinEquiv_apply_val]
  have stride : row.2.val + ctx.parameters.width.val * row.1.val = row.1.val * ctx.parameters.width.val + row.2.val := by ring
  rw [stride]

/-- Compose measured public reconstruction, field-row conversion, domain
construction and extraction. Incoming adapters and backend refinement remain open. -/
def extractWithCost (dummy root : Digest) (ctx : Context) (sourceLog : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  let prepared := materializeWithCost dummy root ctx sourceLog
  let result := NativeGoldExecutableExtraction.extractPreparedWithCost ctx radius capacity prepared.value
  SolverOperationCost.Run.mk result.value (prepared.cost+result.cost+1)

def extract (dummy root : Digest) (ctx : Context) (sourceLog : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  (extractWithCost dummy root ctx sourceLog radius capacity).value

theorem extractWithCost_cost (dummy root : Digest) (ctx : Context) (sourceLog : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    let n := 2^(logSize ctx.parameters.code)
    let left := 2^ctx.parameters.leftVariables.val
    let packing := ctx.parameters.width.val
    let m := ctx.parameters.code.messageBlocks.val
    let b := ctx.parameters.code.blockWidth.val
    let size := ctx.parameters.code.messageLength.val
    (extractWithCost dummy root ctx sourceLog radius capacity).cost ≤ materializeBound ctx sourceLog+
      DenseCommonSource.operationBound n (left*packing) m b radius+
      (left*packing)*(7*size+2)+left*(size*(5*packing+2)+2)+
      n*(2*logSize ctx.parameters.code+9)+6 := by
  have prepared := materializeWithCost_cost dummy root ctx sourceLog
  have extracted := NativeGoldExecutableExtraction.extractPreparedWithCost_cost ctx radius capacity
    (materialize dummy root ctx sourceLog)
  dsimp only [extractWithCost]
  dsimp only [materialize] at extracted
  omega

theorem extract_eq_executable (dummy root : Digest) (ctx : Context) (sourceLog : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    extract dummy root ctx sourceLog radius capacity =
      NativeGoldExecutableExtraction.extract ctx radius capacity (word dummy root ctx sourceLog) := by
  unfold extract extractWithCost
  dsimp only
  rw [NativeGoldExecutableExtraction.extractPreparedWithCost_eq]
  rfl

def table (dummy root : Digest) (ctx : Context) (sourceLog : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    Fin (2^ctx.parameters.leftVariables.val) → Fin ctx.parameters.code.messageLength.val → Fin ctx.parameters.width.val → Goldilocks :=
  let values := extract dummy root ctx sourceLog radius capacity
  fun left right channel => ((values.get left).get right).get channel

theorem table_eq_executable (dummy context root : Digest) (ctx : Context) (sourceLog : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    table dummy root ctx sourceLog radius capacity = NativeGoldExecutableExtraction.table ctx radius capacity
      (NativeGoldBatchSelectedWord.word dummy context root ctx sourceLog) := by
  unfold table
  rw [extract_eq_executable]
  rw [word_eq_analysis dummy context root ctx sourceLog]
  rfl

theorem extract_eq_analysis (dummy context root : Digest) (ctx : Context) (sourceLog : Log)
    (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (uniqueRadius : 2*radius < 2^(logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (left : Fin (2^ctx.parameters.leftVariables.val)) (right : Fin ctx.parameters.code.messageLength.val)
    (channel : Fin ctx.parameters.width.val) :
    (((extract dummy root ctx sourceLog radius capacity).get left).get right).get channel =
      RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius
        (NativeGoldBatchSelectedWord.word dummy context root ctx sourceLog) left right channel := by
  rw [extract_eq_executable]
  rw [NativeGoldExecutableExtraction.extract_eq_analysis ctx tables message block blowup constructed primitive radius uniqueRadius]
  rw [word_eq_analysis dummy context root ctx sourceLog]

/-- Recover the original source snapshot and extract from the complete public
mixed history. No first positive field read means explicit extraction failure. -/
def tableFromHistory (dummy : Digest) (ctx : Context) (history : List NativeTranscript.Observation)
    (field : NativeGoldBatchFieldInputView.View) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  (CompactSourceHistory.recover history field).map (fun sourceLog =>
    table dummy field.data.root ctx sourceLog radius capacity)

theorem tableFromHistory_eq_analysis (dummy : Digest) (ctx : Context) (history : List NativeTranscript.Observation)
    (field : NativeGoldBatchFieldInputView.View)
    (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (uniqueRadius : 2*radius < 2^(logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    tableFromHistory dummy ctx history field radius capacity =
      (NativeGoldBatchFirstFieldSource.recover dummy history field).map (fun sourceLog =>
        RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius
          (NativeGoldBatchSelectedWord.word dummy field.data.context field.data.root ctx sourceLog)) := by
  unfold tableFromHistory
  rw [CompactSourceHistory.recover_eq dummy]
  congr 1
  funext sourceLog left right channel
  exact extract_eq_analysis dummy field.data.context field.data.root ctx sourceLog tables message block blowup
    constructed primitive radius uniqueRadius capacity left right channel

theorem tableFromHistory_none_iff (dummy : Digest) (ctx : Context) (history : List NativeTranscript.Observation)
    (field : NativeGoldBatchFieldInputView.View) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    tableFromHistory dummy ctx history field radius capacity = none ↔
      CausalStreamExposure.seen history (NativeGoldBatchFirstFieldSource.input field) = false := by
  simp only [tableFromHistory,Option.map_eq_none_iff,CompactSourceHistory.recover_eq dummy,
    NativeGoldBatchFirstFieldSource.recover_none]

def FalseClaim (dummy : Digest) (ctx : Context) (work : NativeGoldBatchPcsProgram.Prepared)
    (decoded : NativeGoldBatchChallengeLink.View) (history : List NativeTranscript.Observation)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) : Prop :=
  ∀ coefficients, tableFromHistory dummy ctx history decoded.field radius capacity = some coefficients →
    ∃ query : NativeGoldBatchRectangularData.Query work,
      (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
          (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val) coefficients

theorem falseClaim_iff_executable (dummy : Digest) (ctx : Context) (work : NativeGoldBatchPcsProgram.Prepared)
    (decoded : NativeGoldBatchChallengeLink.View) (history : List NativeTranscript.Observation)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) :
    FalseClaim dummy ctx work decoded history capacity radius ↔
      NativeGoldExecutableExtraction.FalseClaim dummy ctx work decoded history capacity radius := by
  unfold FalseClaim NativeGoldExecutableExtraction.FalseClaim
  rw [← CompactSourceHistory.recover_eq dummy history decoded.field]
  constructor
  · intro falseClaim sourceLog found
    have extracted : tableFromHistory dummy ctx history decoded.field radius capacity =
        some (table dummy decoded.field.data.root ctx sourceLog radius capacity) := by
      simp only [tableFromHistory,found,Option.map_some]
    have claim := falseClaim _ extracted
    rwa [table_eq_executable dummy decoded.field.data.context decoded.field.data.root ctx,
      ← NativeGoldBatchConcreteColumnFamily.source] at claim
  · intro falseClaim coefficients extracted
    obtain ⟨sourceLog,found,equal⟩ := Option.map_eq_some_iff.mp extracted
    subst coefficients
    rw [table_eq_executable dummy decoded.field.data.context decoded.field.data.root ctx,
      ← NativeGoldBatchConcreteColumnFamily.source]
    exact falseClaim sourceLog found
end FormalProof4FHE.HasteBoots.NativeGoldPublicSource
