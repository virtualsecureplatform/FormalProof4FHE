module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchSourceRisk
public import FormalProof4FHE.HasteBoots.NativeRootFamilyAudit
public import FormalProof4FHE.HasteBoots.NativeGoldBatchContextHistory
@[expose] public section

/-! Any accepted native batch witnessed in one complete mixed history has the same global raw-source availability charge. Native framing remains explicit in acceptance witnesses. This is not application soundness, first-exposure lineage, or physical work. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape height Height)
open NativeGoldRawRequests (Request)
open NativeGoldBatchRawAvailability (Equations view)
open NativeGoldBatchSourceRisk (Framed)
open OracleProgram (Program run)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance digestDecisions : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- A native acceptance witnessed in the same complete mixed observation history.
This is an analysis predicate; no verifier call or oracle response is inserted. -/
def Accepted {Memory : Type} (world : World) (history : List Observation) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (work : Prepared) : Prop :=
  Framed ctx ∧ ∃ (completion : Completion Memory work.jobs.length) (parent : NativeTranscript.Transcript),
    (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion ∧
    completion.status = .accepted parent ∧
    (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history

/-- The source is keyed by this verifier's actual context-hash result, not
an arbitrary context digest with the same root and column data. -/
def HasSource (dummy : Digest) (ctx : Context) (work : Prepared) (history : List Observation) (world : World) : Prop :=
  ∃ (context : Digest) (requests : List (NativeGoldColumnWorker.Job × Request height))
    (log : MerkleTreeExtractor.QueryLog Input Digest),
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
    NativeGoldBatchFamilyRequests.prepare context work = some requests ∧
    (∀ index : Height, ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
    ∀ entry ∈ requests,
      entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position ∧
      Equations (view work requests)
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val

/-- Any witnessed batch may fail availability: no preselected verifier, trial
bound, or union over batches, response groups or columns is used. -/
def Failure (Memory : Type) (dummy : Digest) (history : List Observation) (world : World) : Prop :=
  ∃ (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (work : Prepared),
    Accepted world history ctx choose fuel memory work ∧ ¬HasSource dummy ctx work history world

/-- The same observations replay every witnessed native acceptance in any
other oracle world agreeing with the complete history. -/
theorem accepted_replay {Memory : Type} (world other : World) (history : List Observation)
    (agrees : ObservationReplay.Agrees other history) (ctx : Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (work : Prepared) (accepted : Accepted world history ctx choose fuel memory work) :
    Accepted other history ctx choose fuel memory work := by
  obtain ⟨framed,completion,parent,executed,status,observed⟩ := accepted
  have same := (OracleProgram.run_replay (NativeGoldBatchPcsProgram.program ctx choose fuel memory)).replay world other
    (fun entry member => agrees entry (observed.subset member))
  exact ⟨framed,completion,parent,by rw [same]; exact executed,status,by rw [same]; exact observed⟩

theorem accepted_context_replay {Memory : Type} (world other : World) (history : List Observation)
    (agrees : ObservationReplay.Agrees other history) (ctx : Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (work : Prepared) (accepted : Accepted world history ctx choose fuel memory work) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) other).run =
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run := by
  obtain ⟨_,completion,_,executed,_,observed⟩ := accepted
  exact NativeGoldBatchContextHistory.context_replay ctx choose fuel memory world other work completion executed history observed agrees

theorem failure_replay (Memory : Type) (dummy : Digest) (world other : World) (history : List Observation)
    (agrees : ObservationReplay.Agrees other history) (failed : Failure Memory dummy history world) :
    Failure Memory dummy history other := by
  obtain ⟨ctx,choose,fuel,memory,work,accepted,missing⟩ := failed
  refine ⟨ctx,choose,fuel,memory,work,accepted_replay world other history agrees ctx choose fuel memory work accepted,?_⟩
  rintro ⟨context,requests,log,hashed,computed,snapshots,checks⟩
  have same := accepted_context_replay world other history agrees ctx choose fuel memory work accepted
  exact missing ⟨context,requests,log,by rw [← same]; exact hashed,computed,snapshots,checks⟩

/-- This history-only analysis predicate inserts no oracle query or verifier call. -/
def HistoryFailure (Memory : Type) (dummy : Digest) (history : List Observation) : Prop :=
  ∃ world, Failure Memory dummy history world

theorem failure_iff_history (Memory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) :
    Failure Memory dummy history world ↔ HistoryFailure Memory dummy history := by
  constructor
  · exact fun failed => ⟨world,failed⟩
  · rintro ⟨other,failed⟩
    exact failure_replay Memory dummy other world history truthful failed

theorem failure_measurable {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    MeasurableSet {world | Failure Memory dummy (run program world).run.2 world} := by
  have same : {world | Failure Memory dummy (run program world).run.2 world} =
      {world | HistoryFailure Memory dummy (run program world).run.2} := by
    ext world
    exact failure_iff_history Memory dummy world _ ((OracleProgram.run_replay program).truthful world)
  rw [same]
  exact OracleExecutionLaw.event_measurable (OracleProgram.run_replay program)
    (fun result => HistoryFailure Memory dummy result.2)

theorem accepted_has_source {Memory : Type} (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (ctx : Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (work : Prepared) (accepted : Accepted world history ctx choose fuel memory work)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history)) : HasSource dummy ctx work history world := by
  obtain ⟨⟨before,framed,valid,fits⟩,completion,parent,executed,status,observed⟩ := accepted
  obtain ⟨context,requests,log,hashed,computed,snapshots,checks⟩ := NativeGoldBatchNativeAvailability.accepted_native_source
    dummy ctx choose fuel memory world work completion executed parent status history truthful observed before framed valid fits noDisagreement
  exact ⟨context,requests,log,hashed,computed,snapshots,checks⟩

theorem failure_implies_disagreement (Memory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (failed : Failure Memory dummy history world) :
    CheckpointAvailability.Disagreement encoding dummy shape (NativeGoldBatchFamilyAvailability.reconstructed dummy history) := by
  obtain ⟨ctx,choose,fuel,memory,work,accepted,missing⟩ := failed
  by_contra noDisagreement
  exact missing (accepted_has_source dummy world history truthful ctx choose fuel memory work accepted noDisagreement)

theorem native_log_sublist {Memory : Type} (prelude : Program Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (epilogue : Context → NativeGoldBatchPcsProgram.Outcome Memory → Program Unit) (world : World) :
    (run (NativeGoldBatchPcsProgram.program (run prelude world).run.1 choose fuel memory) world).run.2.Sublist
      (run (NativeGoldBatchSourceRisk.program prelude choose fuel memory epilogue) world).run.2 := by
  simp only [NativeGoldBatchSourceRisk.program,OracleProgram.run_bind,ObservationReplay.run_bind,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)

/-- The former selected-verifier failure event is included in the new global
any-batch event, with its actual causal prelude and epilogue unchanged. -/
theorem selected_failure {Memory : Type} (dummy : Digest) (prelude : Program Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (epilogue : Context → NativeGoldBatchPcsProgram.Outcome Memory → Program Unit) (world : World)
    (framed : Framed (run prelude world).run.1)
    (failed : NativeGoldBatchSourceRisk.Failure dummy
      (run (NativeGoldBatchSourceRisk.program prelude choose fuel memory epilogue) world).run.1
      (run (NativeGoldBatchSourceRisk.program prelude choose fuel memory epilogue) world).run.2) :
    Failure Memory dummy (run (NativeGoldBatchSourceRisk.program prelude choose fuel memory epilogue) world).run.2 world := by
  obtain ⟨work,completion,parent,executed,status,missing⟩ := failed
  have same : (run (NativeGoldBatchSourceRisk.program prelude choose fuel memory epilogue) world).run.1.2 =
      (run (NativeGoldBatchPcsProgram.program (run prelude world).run.1 choose fuel memory) world).run.1 := by
    simp only [NativeGoldBatchSourceRisk.program,OracleProgram.run_bind,ObservationReplay.run_bind,
      OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  rw [same] at executed
  refine ⟨(run prelude world).run.1,choose,fuel,memory,work,
    ⟨framed,completion,parent,executed,status,native_log_sublist prelude choose fuel memory epilogue world⟩,?_⟩
  rintro ⟨context,requests,log,_,computed,snapshots,checks⟩
  exact missing ⟨context,requests,log,computed,snapshots,checks⟩

/-- The shared audit turns every missing-source acceptance into a persistent
collision/source-failure event, even if later queries add a new source witness. -/
theorem failure_implies_bad (Memory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (failed : Failure Memory dummy history world) :
    CheckpointCollision.Bad shape (NativeGoldBatchFamilyAvailability.reconstructed dummy history) :=
  by
    have different := failure_implies_disagreement Memory dummy world history truthful failed
    have decisions : digestDecisions = (fun left right : Digest => Fintype.decidablePiFintype left right) := Subsingleton.elim _ _
    rw [decisions] at different
    exact NativeRootFamilyAudit.disagreement_implies_bad dummy world history truthful different

/-- A single charge covers every accepted batch witnessed in the actual
native program log, including arbitrary raw/off-path prequeries and suffixes. -/
theorem failure_le_charge {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    InputIndexedOracle.law {world | Failure Memory dummy (run program world).run.2 world} ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (CheckpointCollision.loss unifSpec shape)
      ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
      (CheckpointExecution.empty shape) := by
  have included : {world | Failure Memory dummy (run program world).run.2 world} ⊆
      {world | CheckpointCollision.Bad shape
        (NativeGoldBatchFamilyAvailability.reconstructed dummy (run program world).run.2)} :=
    fun world failed => failure_implies_bad Memory dummy world _ ((OracleProgram.run_replay program).truthful world) failed
  exact (measure_mono included).trans (NativeRootFamilyAudit.bad_le_charge dummy program)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
