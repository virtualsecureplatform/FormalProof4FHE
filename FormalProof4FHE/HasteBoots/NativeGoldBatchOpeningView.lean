module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchOrderedChecks
public import FormalProof4FHE.HasteBoots.RectangularOpening
@[expose] public section

/-! The deterministic rectangular opening interface of a native batch:
computed coded response lanes, finite group/lane tests and original ordered
column draws on one frozen matrix. Production challenge freshness and false
claim/extraction probability composition remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchOpeningView
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize description)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open NativeGoldBatchResponseMeaning (Lane Domain)
open NativeGoldBatchLinearEquations (Weights Word Frozen)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev Test (work : Prepared) := Fin work.groups.length × Fin work.width

def weights (work : Prepared) (test : Test work) := Weights work (work.groups.get test.1).1 test.2

def claim (ctx : Context) (work : Prepared) (test : Test work) := Lane ctx work (work.groups.get test.1).2 test.2.val

theorem responses_coded (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    (∀ lane : Fin work.width, Lane ctx work work.test lane.val ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) ∧
      ∀ test : Test work, claim ctx work test ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val := by
  constructor
  · intro lane
    exact (NativeGoldBatchResponseMeaning.prepared_test ctx world work executed constructorTables message block blowup constructed primitive lane.val lane.isLt).2
  · intro test
    exact NativeGoldBatchResponseMeaning.prepared_groups ctx world work executed constructorTables message block blowup constructed primitive
      (work.groups.get test.1) (List.get_mem _ _) test.2.val test.2.isLt

/-- The native response checks have exactly the common-word/shared-draw shape
used by the rectangular opening bound. No random/structured event independence
or extra authentication is introduced by indexing the response families. -/
theorem source_checks (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (history : List Observation) (source : NativeGoldBatchAnySourceRisk.HasSource dummy ctx work history world) :
    ∃ (context : Digest) (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
      (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))),
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      (∀ lane : Fin work.width, ColumnOpening.Agrees
        (StructuredOpening.combine (Weights work work.random lane) (Word ctx work (Frozen dummy context work log))) (Lane ctx work work.test lane.val) draw) ∧
      ∀ test : Test work, ColumnOpening.Agrees
        (StructuredOpening.combine (weights work test) (Word ctx work (Frozen dummy context work log))) (claim ctx work test) draw := by
  obtain ⟨context,log,draw,hashed,snapshots,typed,ordered,random,structured⟩ :=
    NativeGoldBatchOrderedChecks.source_agrees dummy ctx world work executed constructorTables message block blowup constructed history source
  exact ⟨context,log,draw,hashed,snapshots,typed,ordered,random,
    fun test => structured (work.groups.get test.1) (List.get_mem _ _) test.2⟩

/-- Acceptance supplies the native run and frozen source; backend constructor
and root correctness remain explicit. All codeword and column-check premises
are derived for the retained code, with independent test and symbol widths. -/
theorem accepted_checks {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (history : List Observation) (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history)) :
    (∀ lane : Fin work.width, Lane ctx work work.test lane.val ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) ∧
    (∀ test : Test work, claim ctx work test ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) ∧
    ∃ (context : Digest) (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
      (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))),
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      (∀ lane : Fin work.width, ColumnOpening.Agrees
        (StructuredOpening.combine (Weights work work.random lane) (Word ctx work (Frozen dummy context work log))) (Lane ctx work work.test lane.val) draw) ∧
      ∀ test : Test work, ColumnOpening.Agrees
        (StructuredOpening.combine (weights work test) (Word ctx work (Frozen dummy context work log))) (claim ctx work test) draw := by
  have source := NativeGoldBatchAnySourceRisk.accepted_has_source dummy world history truthful ctx choose fuel memory work accepted noDisagreement
  obtain ⟨_,completion,parent,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have coded := responses_coded ctx world work prepared constructorTables message block blowup constructed primitive
  exact ⟨coded.1,coded.2,source_checks dummy ctx world work prepared constructorTables message block blowup constructed history source⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchOpeningView
