module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance

@[expose] public section

/-! Acceptance of the computed pool tail enforces the original suffix claim
and replays every original raw worker in the final shared cache. Native
mixed-prefix/cache coupling and full application soundness remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness

open NativeGoldBlockCode (Tables Stored)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (Input World)
open OracleSpec OracleComp

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

noncomputable section

/-- A real checked prefix cannot hit the defensive suffix-wrapper failure. -/
theorem prepared_no_finish_error (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (claimed : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (OracleProgram.run (NativeGoldPcsWorkers.protocol tables parameters transcript root query claimed opening fuel) world).run.1 = .prepared work) :
    NativeGoldPcsClaim.verify parameters query opening.evaluation.val claimed ≠ .error .finish := by
  obtain ⟨_,result,read⟩ := NativeGoldPcsFinishComplete.prepared_finish tables parameters transcript root query claimed opening fuel world work success
  simp only [NativeGoldPcsClaim.verify,read]
  split <;> intro impossible <;> cases impossible

variable {Cfg Memory : Type} [SampleableType Digest]

/-- The original checked query discharges the suffix semantics premise. The
claim being enforced is the original raw claimed row bound by that prefix. -/
theorem accepted_value (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (claimed : Row) (opening : Opening) (fieldFuel : ℕ) (world : World) (work : Prepared)
    (prepared : (OracleProgram.run (NativeGoldPcsWorkers.protocol tables parameters transcript root query claimed opening fieldFuel) world).run.1 = .prepared work)
    (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : NativeGoldPcsAcceptance.Completion Memory work.jobs.length × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (NativeGoldPcsAcceptance.program parameters query opening claimed work choose fuel memory)).run before))
    (next : Transcript) (accepted : outcome.1.status = .accepted next) :
    next = work.transcript ∧ claimed.val.map goldValue = List.ofFn (FlatMatrixFold.foldAll
      ((query.models.drop parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue parameters.width.val))
      (fun index lane => goldValue (opening.evaluation.val[lane.val*2^(parameters.numVariables.val-parameters.leftVariables.val)+index.val]?.getD 0))) := by
  obtain ⟨_,_,checked,receipt⟩ := NativeGoldPcsAcceptance.accepted_origin parameters query opening claimed work dummy shape choose fuel memory before outcome supported next accepted
  have valid := (NativeGoldPcsFinishComplete.prepared_finish tables parameters transcript root query claimed opening fieldFuel world work prepared).1
  exact ⟨receipt,NativeGoldPcsClaim.accepted_value parameters query opening.evaluation.val claimed valid checked⟩

/-- The final acceptance status cannot bypass any original raw worker. Its
payload/path replay and both computed coordinate checks hold in this cache. -/
theorem accepted_workers (parameters : Parameters Stored) (query : Query) (claimed : Row) (opening : Opening) (work : Prepared)
    (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : NativeGoldPcsAcceptance.Completion Memory work.jobs.length × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (NativeGoldPcsAcceptance.program parameters query opening claimed work choose fuel memory)).run before))
    (next : Transcript) (accepted : outcome.1.status = .accepted next) :
    ∀ job ∈ work.jobs, ∃ leaf siblings, NativeGoldColumnAuthentication.decodePath work.geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ outcome.2.hash.cache.toPartialImpl (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding work.geometry.height
        job.index job.column.values leaf work.root siblings) = some true ∧
      NativeGoldColumnChecks.check work.geometry work.width work.random work.structured work.test work.evaluation job.column.values.val job.index = true := by
  obtain ⟨poolSupported,allAccepted,_,_⟩ := NativeGoldPcsAcceptance.accepted_origin parameters query opening claimed work dummy shape choose fuel memory before outcome supported next accepted
  exact NativeGoldColumnWorker.accepted_jobs work.geometry work.width work.random work.structured work.test work.evaluation
    dummy work.root work.jobs shape choose fuel memory before (outcome.1.pool,outcome.2) poolSupported allAccepted

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness
