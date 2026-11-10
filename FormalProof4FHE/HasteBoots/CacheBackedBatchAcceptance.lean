module
public import FormalProof4FHE.HasteBoots.CacheBackedBatchFinishing
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
@[expose] public section

/-! Authenticated native acceptance derives the complete rectangular opening
view, or the existing shared history Bad occurs. Completed constructor facts
are derived. The missing-view event for any witnessed batch pays one hash
charge; no union over contexts, owners, schedulers, groups or columns is used. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedBatchAcceptance
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCodeProgram (Request Config Completed)
open NativeGoldBatchRectangularAcceptance (View)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (Program run)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- The computed acceptance's complete opening view is a conclusion, never a
prover-supplied security or replay certificate. -/
theorem view_or_bad {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code)
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history) :
    Nonempty (View dummy ctx world work history (CacheBackedBatchSoundness.primitive ctx request config reachable result finished retained)) ∨
      NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · left
    apply NativeGoldBatchRectangularAcceptance.accepted_view dummy ctx world work
      (CacheBackedBatchSoundness.constructorTables request config reachable) request.message request.block request.blowup
      (CacheBackedBatchSoundness.constructed ctx request config reachable result finished retained)
      (CacheBackedBatchSoundness.primitive ctx request config reachable result finished retained) history choose fuel memory accepted truthful
    intro different
    have decisions : NativeGoldBatchRectangularAcceptance.instDecidableEqDigest =
        (fun first second : Digest => Fintype.decidablePiFintype first second) := Subsingleton.elim _ _
    rw [decisions] at different
    exact bad (NativeRootFamilyAudit.disagreement_implies_bad dummy world history truthful different)

/-- A complete program supplies its own truthful observation replay. -/
theorem program_view_or_bad {A Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code)
    (program : Program A) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (run program world).run.2 ctx choose fuel memory work) :
    Nonempty (View dummy ctx world work (run program world).run.2 (CacheBackedBatchSoundness.primitive ctx request config reachable result finished retained)) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 :=
  view_or_bad dummy ctx world work request config reachable result finished retained (run program world).run.2
    choose fuel memory accepted ((OracleProgram.run_replay program).truthful world)

/-- Every possible accepted batch and completed-constructor witness in this
same history is covered. No analysis view is supplied to the native verifier. -/
def Failure (Memory : Type) (dummy : Digest) (history : List Observation) (world : World) : Prop :=
  ∃ (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (work : Prepared),
    NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work ∧
    ∃ (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
      (result : Completed) (finished : config.phase = .done result) (retained : result.code = ctx.parameters.code),
      ¬Nonempty (View dummy ctx world work history (CacheBackedBatchSoundness.primitive ctx request config reachable result finished retained))

theorem failure_implies_bad (Memory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (failed : Failure Memory dummy history world) :
    NativeRootFamilyLifetime.Bad dummy history := by
  obtain ⟨ctx,choose,fuel,memory,work,accepted,request,config,reachable,result,finished,retained,missing⟩ := failed
  exact (view_or_bad dummy ctx world work request config reachable result finished retained history choose fuel memory accepted truthful).resolve_left missing

/-- One complete-program hash charge covers every missing opening view in its
actual mixed history; truthful replay is derived from that program's run. -/
theorem failure_le_charge {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    InputIndexedOracle.law {world | Failure Memory dummy (run program world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape)
        (CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
        (CheckpointExecution.empty NativeMerkleShapeFamily.shape) := by
  have included : {world | Failure Memory dummy (run program world).run.2 world} ⊆
      {world | NativeRootFamilyLifetime.Bad dummy (run program world).run.2} := by
    intro world failed
    exact failure_implies_bad Memory dummy world _ ((OracleProgram.run_replay program).truthful world) failed
  exact (measure_mono included).trans (NativeRootFamilyAudit.bad_le_charge dummy program)

end
end FormalProof4FHE.HasteBoots.CacheBackedBatchAcceptance
