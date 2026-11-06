module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedSource
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredMatrix
@[expose] public section

/-! The common source word uses fixed public dimensions, context/root and
an earlier-history-selected log. Its definition has no future Prepared work
or oracle-world argument. This remains an analysis word, not the required
efficient independent public application extractor. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedWord
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeMerkleShapeFamily (height)
open NativeGoldBatchRectangularWeights (Row)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def atTag (dummy : Digest) (sourceTag : NativeMerkleShapeFamily.Tag) (root : Digest) (sourceLog : Log) : ℕ → ℕ → Goldilocks :=
  fun symbol => NativeGoldRawAvailability.frozenValue dummy height sourceTag ⟨root,sourceLog⟩
    (Fin.ofNat (2^(height sourceTag)) symbol)

def values (dummy context root : Digest) (code : NativeGoldBlockCode.Stored) (sourceLog : Log) : ℕ → ℕ → Goldilocks :=
  atTag dummy (context,Fin.ofNat 64 (NativeGoldBlockCode.logSize code)) root sourceLog

def word (dummy context root : Digest) (ctx : Context) (sourceLog : Log) :
    Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks :=
  fun symbol row component => values dummy context root ctx.parameters.code sourceLog symbol.val
    ((row.1.val*ctx.parameters.width.val+row.2.val)*ctx.parameters.code.blockWidth.val+component.val)

theorem prepared_tag (context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code) :
    NativeMerkleShapeFamily.tag context work = (context,Fin.ofNat 64 (NativeGoldBlockCode.logSize ctx.parameters.code)) := by
  have layout := NativeGoldBatchResponseMeaning.prepared_layout ctx world work prepared tables message block blowup constructed
  unfold NativeMerkleShapeFamily.tag
  rw [layout.2.2.2]

theorem prepared_values (dummy context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code) (sourceLog : Log) :
    NativeGoldBatchLinearEquations.Frozen dummy context work sourceLog = values dummy context ctx.root ctx.parameters.code sourceLog := by
  change atTag dummy (NativeMerkleShapeFamily.tag context work) work.root sourceLog =
    atTag dummy (context,Fin.ofNat 64 (NativeGoldBlockCode.logSize ctx.parameters.code)) ctx.root sourceLog
  rw [prepared_tag context ctx world work prepared tables message block blowup constructed,
    (NativeGoldBatchPcsProgram.prepared_binding ctx world work prepared).1]

theorem prepared_word (dummy context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : NativeGoldBlockCode.Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code) (sourceLog : Log) :
    NativeGoldBatchRectangularWeights.source ctx world work prepared
      (NativeGoldBatchLinearEquations.Frozen dummy context work sourceLog) = word dummy context ctx.root ctx sourceLog := by
  rw [prepared_values dummy context ctx world work prepared tables message block blowup constructed sourceLog]
  funext symbol row component
  simp only [NativeGoldBatchRectangularWeights.source,NativeGoldBatchLinearEquations.Word,word,
    NativeGoldBatchRectangularWeights.rowEquiv_val]

/-- The source's only variable data are the parsed binding and old history. -/
def selected (dummy : Digest) (before : List NativeTranscript.Observation) (field : NativeGoldBatchFieldInputView.View) (ctx : Context) :=
  word dummy field.data.context field.data.root ctx (NativeGoldBatchSelectedSource.log dummy before field)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedWord
