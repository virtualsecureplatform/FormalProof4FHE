module
public import FormalProof4FHE.HasteBoots.SingleOpeningFirstFieldSource
public import FormalProof4FHE.HasteBoots.SingleOpeningRecoveredMatrix
@[expose] public section

/-! One single-opening analysis source from fixed original parameters and
the pre-field-read checkpoint log. No future Prepared work or oracle world
is an argument to this word; efficient public extraction remains separate. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningSelectedWord
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeMerkleShapeFamily (height)
open SingleOpeningRectangularData (Row)
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
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx) :
    SingleOpeningAvailability.tag context work = (context,Fin.ofNat 64 (NativeGoldBlockCode.logSize ctx.parameters.code)) := by
  have layout := SingleOpeningRectangularChecks.layout ctx world work prepared origin
  unfold SingleOpeningAvailability.tag
  rw [layout.2.2]

theorem prepared_values (dummy context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx) (sourceLog : Log) :
    SingleOpeningRectangularChecks.Frozen dummy context work sourceLog = values dummy context ctx.root ctx.parameters.code sourceLog := by
  have root := (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work prepared).2.2
  change atTag dummy (SingleOpeningAvailability.tag context work) work.root sourceLog =
    atTag dummy (context,Fin.ofNat 64 (NativeGoldBlockCode.logSize ctx.parameters.code)) ctx.root sourceLog
  rw [prepared_tag context ctx world work prepared origin,root]

theorem prepared_word (dummy context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx) (sourceLog : Log) :
    SingleOpeningRectangularChecks.source ctx world work prepared
      (SingleOpeningRectangularChecks.Frozen dummy context work sourceLog) = word dummy context ctx.root ctx sourceLog := by
  rw [prepared_values dummy context ctx world work prepared origin sourceLog]
  funext symbol row component
  simp only [SingleOpeningRectangularChecks.source,word,SingleOpeningRectangularData.rowEquiv_val]

def selected (dummy : Digest) (before : List NativeTranscript.Observation) (field : SingleOpeningFieldInputView.View) (ctx : Context) :=
  word dummy field.data.context field.data.root ctx (SingleOpeningFirstFieldSource.selectedLog dummy before field)
end
end FormalProof4FHE.HasteBoots.SingleOpeningSelectedWord
