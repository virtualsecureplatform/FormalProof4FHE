module
public import FormalProof4FHE.HasteBoots.RecordedSourceCoherence
public import FormalProof4FHE.HasteBoots.AuthenticatedPublicZeroCheck
@[expose] public section

/-! Relate a private source at an original recorded owner checkpoint to the
fresh prefix source used by authenticated ZeroCheck. The same context/root,
field, code, decoder radius and layout are retained. Source predicates transfer
outside the common history exception; no equality of selected queries is used. -/
namespace FormalProof4FHE.HasteBoots.ReusedPrivateSource
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
open CommittedJointMatrixOpening
noncomputable section
variable {F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Digest]
  {b n front suffix m queries height : ℕ}

def atSnapshot
    (s : AuthenticatedPublicZeroCheck.Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ) (tag : Cfg)
    (checkpoint : RecordedSourceCoherence.Snapshot Input Digest Cfg height tag) : MatrixFold.Cube (n+1) → Fin b → F :=
  QueryReindex.source s.dimensions
    (RecordedSourceCoherence.source (front := front) s.encoding dummy s.domain capacity radius tag checkpoint)

theorem fresh_source_eq
    (s : AuthenticatedPublicZeroCheck.Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : AuthenticatedPublicZeroCheck.Prefix (Private := Private) (Digest := Digest) (CommitMemory := CommitMemory)
      (Input := Input) (Cfg := Cfg) (height := height)) (factor : Private) :
    atSnapshot s dummy capacity radius (s.tag factor) (snapshots s.tag first factor) =
      AuthenticatedPublicZeroCheck.privateSources s dummy capacity radius first factor := rfl

variable [DecidableEq Input] [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

/-- Source-level faults on an original immutable owner cannot disappear by
selecting a later snapshot of that same context/root, except in the existing
common history-failure event. Audit follows from the actual run's support. -/
theorem predicate_transfer_on_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (s : AuthenticatedPublicZeroCheck.Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)) program).run
      (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))))
    (first : AuthenticatedPublicZeroCheck.Prefix (Private := Private) (Digest := Digest) (CommitMemory := CommitMemory)
      (Input := Input) (Cfg := Cfg) (height := height)) (factor : Private)
    (original : RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor))
    (originalRecorded : ⟨s.tag factor,original⟩ ∈ result.2.checkpoints.checkpoints)
    (freshRecorded : ⟨s.tag factor,snapshots s.tag first factor⟩ ∈ result.2.checkpoints.checkpoints)
    (sameRoot : original.root = first.1.1 factor)
    (predicate : (MatrixFold.Cube (n+1) → Fin b → F) → Prop)
    (falseOriginal : ¬predicate (atSnapshot s dummy capacity radius (s.tag factor) original)) :
    ¬predicate (AuthenticatedPublicZeroCheck.privateSources s dummy capacity radius first factor) ∨
      CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) result.2 := by
  rw [←fresh_source_eq s dummy capacity radius first factor]
  exact RecordedSourceCoherence.predicate_transfer_on_run implBase s.encoding dummy s.domain capacity radius program result supported
    (s.tag factor) original (snapshots s.tag first factor) originalRecorded freshRecorded sameRoot
    (fun value => predicate (QueryReindex.source s.dimensions value)) falseOriginal

end
end FormalProof4FHE.HasteBoots.ReusedPrivateSource
