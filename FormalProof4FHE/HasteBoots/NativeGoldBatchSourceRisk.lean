module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchNativeAvailability
@[expose] public section

/-! One global hash charge for an accepted native batch lacking a consistent frozen raw source, including arbitrary causal prequeries and epilogue. Parent framing and message allocation bounds remain an explicit domain obligation. This is not PCS/application soundness or physical attacker-work security. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchSourceRisk
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler Outcome)
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Tag Height height shape)
open NativeGoldBatchRawAvailability (Equations view)
open NativeGoldBatchFamilyAvailability (reconstructed)
open OracleProgram (Program bind run)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance digestDecisions : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- Arbitrary causal prequeries and a causal epilogue share the selected native verifier history. -/
def program {Memory : Type} (prelude : Program Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (epilogue : Context → Outcome Memory → Program Unit) :
    Program (Context × Outcome Memory) :=
  bind prelude (fun ctx => bind (NativeGoldBatchPcsProgram.program ctx choose fuel memory)
    (fun result => bind (epilogue ctx result) (fun _ => .pure (ctx,result))))

def Framed (ctx : Context) : Prop := ∃ before : List TranscriptFrame.Frame,
  ctx.parent.input = TranscriptFrame.encodeMany before ∧ (∀ frame ∈ before, TranscriptFrame.Valid frame) ∧
    128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit

def HasSource (dummy : Digest) (work : Prepared) (history : List Observation) : Prop :=
  ∃ (context : Digest) (requests : List (NativeGoldColumnWorker.Job × Request height))
    (log : MerkleTreeExtractor.QueryLog Input Digest),
    NativeGoldBatchFamilyRequests.prepare context work = some requests ∧
    (∀ index : Height, ⟨(context,index),⟨work.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) ∧
    ∀ entry ∈ requests,
      entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position ∧
      Equations (view work requests)
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val

def Failure {Memory : Type} (dummy : Digest) (packet : Context × Outcome Memory) (history : List Observation) : Prop :=
  ∃ (work : Prepared) (completion : Completion Memory work.jobs.length) (parent : NativeTranscript.Transcript),
    packet.2 = .completed work completion ∧ completion.status = .accepted parent ∧ ¬HasSource dummy work history

theorem failure_implies_disagreement {Memory : Type} (dummy : Digest) (prelude : Program Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (epilogue : Context → Outcome Memory → Program Unit) (world : World)
    (framed : Framed (run prelude world).run.1)
    (failure : Failure dummy (run (program prelude choose fuel memory epilogue) world).run.1
      (run (program prelude choose fuel memory epilogue) world).run.2) :
    CheckpointAvailability.Disagreement encoding dummy shape
      (reconstructed dummy (run (program prelude choose fuel memory epilogue) world).run.2) := by
  let ctx := (run prelude world).run.1
  have evaluated : (run (program prelude choose fuel memory epilogue) world).run =
      ((ctx,(run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1),
        ((run prelude world).run.2 ++ (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2) ++
          (run (epilogue ctx (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1) world).run.2) := by
    simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil,List.append_assoc,ctx]
  obtain ⟨work,completion,parent,executed,accepted,missing⟩ := failure
  rw [evaluated] at executed
  by_contra noDisagreement
  obtain ⟨before,bytes,valid,fits⟩ := framed
  obtain ⟨context,requests,log,_,computed,snapshots,checks⟩ := NativeGoldBatchNativeAvailability.accepted_native_source
    dummy ctx choose fuel memory world work completion executed parent accepted
    (run (program prelude choose fuel memory epilogue) world).run.2 ((OracleProgram.run_replay _).truthful world)
    (by rw [evaluated]; exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)) before bytes valid fits noDisagreement
  exact missing ⟨context,requests,log,computed,snapshots,checks⟩

/-- The same causal prelude, byte cache and SHA512 cache are charged once.
This is raw-source availability, not application soundness or physical work. -/
theorem failure_le_charge {Memory : Type} (dummy : Digest) (prelude : Program Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (epilogue : Context → Outcome Memory → Program Unit)
    (framed : ∀ world, Framed (run prelude world).run.1) :
    InputIndexedOracle.law {world | Failure dummy (run (program prelude choose fuel memory epilogue) world).run.1
      (run (program prelude choose fuel memory epilogue) world).run.2} ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (CheckpointCollision.loss unifSpec shape)
      ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program prelude choose fuel memory epilogue)).run NativeShakeCache.empty)
      (CheckpointExecution.empty shape) := by
  have included : {world | Failure dummy (run (program prelude choose fuel memory epilogue) world).run.1
      (run (program prelude choose fuel memory epilogue) world).run.2} ⊆
      {world | CheckpointAvailability.Disagreement encoding dummy shape
        (reconstructed dummy (run (program prelude choose fuel memory epilogue) world).run.2)} :=
    fun world failed => failure_implies_disagreement dummy prelude choose fuel memory epilogue world (framed world) failed
  apply le_trans (measure_mono included)
  have law := NativeRootFamilyState.from_empty (program prelude choose fuel memory epilogue) encoding dummy
    (fun result => CheckpointAvailability.Disagreement encoding dummy shape result.2)
  change InputIndexedOracle.law {world | CheckpointAvailability.Disagreement encoding dummy shape
      (reconstructed dummy (run (program prelude choose fuel memory epilogue) world).run.2)} = _ at law
  rw [law]
  unfold NativeRootFamilyFreeze.execute
  have decisions : (fun left right : Digest => Fintype.decidablePiFintype left right) = digestDecisions := Subsingleton.elim _ _
  rw [decisions]
  exact CheckpointAvailability.disagreement_le_charge (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape
    ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program prelude choose fuel memory epilogue)).run NativeShakeCache.empty)
    (CheckpointExecution.empty shape) (CheckpointCollision.safe_empty encoding dummy shape)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchSourceRisk
