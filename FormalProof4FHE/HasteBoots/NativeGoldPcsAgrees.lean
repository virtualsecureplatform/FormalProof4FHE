module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldPcsDraws
public import FormalProof4FHE.HasteBoots.ColumnOpening
public import FormalProof4FHE.HasteBoots.StructuredOpening

@[expose] public section

/-! Transport actual raw pool checks to the existing semantic opening
interface on every original ordered draw, including repeated positions.
The checkpoint is fixed; its native placement/freshness is a later coupling
obligation. No semantic payload is hashed in this transport. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees

open NativeGoldPcsWorkers (Prepared)
open NativeGoldRawRequests (Request)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (GoldWord)
open NativeFields (Goldilocks)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

noncomputable section
variable {Cfg Memory : Type} [SampleableType Digest]

/-- Coverage by an original raw job suffices at a position; converting that
job does not change its position, root or checkpoint context. -/
theorem pool_position (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height))
    (prepared : NativeGoldPcsRawAvailability.prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (dummy : Digest)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) outcome.2)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (recorded : ⟨tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints) (root : checkpoint.root = work.root)
    (position : Fin (2^(height tag)))
    (covered : ∃ job ∈ work.jobs, job.index = position.val) :
    NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
      (NativeGoldRawAvailability.frozenValue dummy height tag checkpoint position) position.val := by
  have spec := NativeGoldRawRequests.entries_spec height tag work.root work.jobs result prepared
  obtain ⟨job,member,same⟩ := covered
  have present : job ∈ result.map Prod.fst := by rw [spec.1]; exact member
  obtain ⟨entry,entryMember,jobEq⟩ := List.mem_map.mp present
  have computed := spec.2 entry entryMember
  obtain ⟨bound,leaf,siblings,_,requestEq⟩ := NativeGoldRawRequests.fromJob_spec height tag work.root entry.1 entry.2 computed
  have equations := NativeGoldPcsRawAvailability.pool_equations height tag work result prepared matchesHeight dummy
    choose fuel memory before outcome supported accepted noFailure entry entryMember
  rw [requestEq] at equations
  have indexEq : entry.1.index = position.val := (congrArg NativeGoldColumnWorker.Job.index jobEq).trans same
  have point : (⟨entry.1.index,bound⟩ : Fin (2^(height tag))) = position := Fin.ext indexEq
  have checked := equations checkpoint recorded root
  change NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
    (NativeGoldRawAvailability.frozenValue dummy height tag checkpoint ⟨entry.1.index,bound⟩) entry.1.index at checked
  rw [point,indexEq] at checked
  exact checked

def weights (rows width : ℕ) (values : List GoldWord) (lane : Fin width) : Fin rows → Goldilocks :=
  fun row => NativeGoldColumnChecks.view values (lane.val*rows+row.val)

/-- Only trusted row/symbol dimensions and the fixed checkpoint determine
this source; no challenge weights or response vector is an argument. -/
def source (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (rows block : ℕ) : Fin (2^(height tag)) → Fin rows → Fin block → Goldilocks :=
  fun position row coordinate => NativeGoldRawAvailability.frozenValue dummy height tag checkpoint position (row.val*block+coordinate.val)

def response (geometry : NativeBrakedownParameters.Geometry) (width height : ℕ)
    (values : List GoldWord) (lane : Fin width) : Fin (2^height) → Fin geometry.blockWidth → Goldilocks :=
  fun position coordinate => NativeGoldColumnChecks.view values (lane.val*geometry.stride+position.val*geometry.blockWidth+coordinate.val)

omit [SampleableType Digest] in
/-- The exact native row sums give the existing semantic agreement predicate.
Both response families use the same original draw function and frozen word. -/
theorem agrees_of_equations (height : Cfg → ℕ) (tag : Cfg) (work : Prepared) (dummy : Digest)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (queries : ℕ) (draw : Fin queries → Fin (2^(height tag)))
    (equations : ∀ index, NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
      (NativeGoldRawAvailability.frozenValue dummy height tag checkpoint (draw index)) (draw index).val) :
    (∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (weights work.geometry.rows work.width work.random lane)
        (source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
      (response work.geometry work.width (height tag) work.test lane) draw) ∧
    (∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (weights work.geometry.rows work.width work.structured lane)
        (source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
      (response work.geometry work.width (height tag) work.evaluation lane) draw) := by
  classical
  constructor
  · intro lane index
    funext coordinate
    have facts := (equations index lane.val lane.isLt coordinate.val coordinate.isLt).1
    simpa only [StructuredOpening.combine,weights,source,response,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using facts
  · intro lane index
    funext coordinate
    have facts := (equations index lane.val lane.isLt coordinate.val coordinate.isLt).2
    simpa only [StructuredOpening.combine,weights,source,response,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using facts

/-- Accepted actual raw workers establish both semantic opening check families
on every covered ordered draw, with no additional deduplication loss. -/
theorem pool_agrees (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height))
    (prepared : NativeGoldPcsRawAvailability.prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (dummy : Digest)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) outcome.2)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (recorded : ⟨tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints) (root : checkpoint.root = work.root)
    (queries : ℕ) (draw : Fin queries → Fin (2^(height tag)))
    (covered : ∀ index, ∃ job ∈ work.jobs, job.index = (draw index).val) :
    (∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (weights work.geometry.rows work.width work.random lane)
        (source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
      (response work.geometry work.width (height tag) work.test lane) draw) ∧
    (∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (weights work.geometry.rows work.width work.structured lane)
        (source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
      (response work.geometry work.width (height tag) work.evaluation lane) draw) := by
  apply agrees_of_equations height tag work dummy checkpoint queries draw
  intro index
  exact pool_position height tag work result prepared matchesHeight dummy choose fuel memory before outcome supported accepted noFailure
    checkpoint recorded root (draw index) (covered index)

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees
