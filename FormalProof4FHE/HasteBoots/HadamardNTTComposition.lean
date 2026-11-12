module
public import FormalProof4FHE.HasteBoots.ShortCircuitStageHistory
public import FormalProof4FHE.HasteBoots.CallerBoundStageRoots
@[expose] public section

/-! Caller-bound authenticated Hadamard followed by NTT, in native caller
order with actual early return. This composes the existing child programs;
Rust byte/transcript correspondence and full PBS composition remain separate. -/
namespace FormalProof4FHE.HasteBoots.HadamardNTTComposition
open OracleSpec OracleComp
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k n count front suffix m queries height : ℕ}
  [SampleableType Digest]
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
variable (coefficient : Digest) (expected : Fin count → Digest)
  (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
  (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)

/-- A rejected Hadamard stage executes no NTT child calls or root annotations. -/
def program := do
  let first ← AuthenticatedZeroCheck.program (CallerBoundStageRoots.hadamard expected publicRoots hs)
  if AuthenticatedZeroCheck.accepted first.2 then
    let second ← AuthenticatedNTT.program
      (CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns)
    pure (first,some second)
  else pure (first,none)

/-- Both analysis prefixes are retained at their actual recording times;
the second stage starts at the first stage's final state and may be skipped. -/
def witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height)) :=
  let h := CallerBoundStageRoots.hadamard expected publicRoots hs
  let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns
  ShortCircuitStageHistory.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h)
    (fun first => AuthenticatedZeroCheck.accepted first.2)
    (fun _ => CommittedJointMatrixOpening.requests t.tag [false,true])
    (fun _ => t.commit) (fun _ => AuthenticatedNTT.continuation t) initial

/-- Erasing the two retained snapshots recovers exactly the existing child
programs, their short-circuit control flow, actual results and final history. -/
theorem project_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height)) :
    (fun outcome => match outcome.2 with
      | none => (((outcome.1.1.1,outcome.1.2.1),none),outcome.1.2.2)
      | some second => (((outcome.1.1.1,outcome.1.2.1),some (second.1.1,second.2.1)),second.2.2)) <$>
      witness coefficient expected publicRoots factor ns hs dummy initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (program coefficient expected publicRoots factor ns hs)).run initial := by
  simp only [witness,program,ShortCircuitStageHistory.witness,AuthenticatedZeroCheck.program,
    AuthenticatedNTT.program,MultiCommitmentPrefix.witness,MultiCommitmentPrefix.program,
    simulateQ_bind,StateT.run_bind,RecordRoots.run_program,map_bind,pure_bind,bind_assoc]
  congr 1
  funext first
  congr 1
  funext last
  split <;> simp only [map_bind,map_pure,simulateQ_bind,StateT.run_bind,
    simulateQ_pure,StateT.run_pure,RecordRoots.run_program,pure_bind]

end
end FormalProof4FHE.HasteBoots.HadamardNTTComposition
