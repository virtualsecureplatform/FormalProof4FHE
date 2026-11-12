module
public import FormalProof4FHE.HasteBoots.NTTConditionalSoundness
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence
@[expose] public section

/-! Ordered authenticated NTT children with actual early return and private
memory handoff. Analysis retains each original child prefix without resetting
the shared history; erasure recovers the existing child-program loop. -/
namespace FormalProof4FHE.HasteBoots.NTTSequence
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))] [SampleableType Digest]

abbrev ActualResult := ((Bool → Digest) × CommitMemory) ×
  AuthenticatedNTT.Packet F Memory c b r k ×
    ShortCircuitSequence.Outcome Bool (JointMatrixOpening.Data F Digest Response (2^front) b height queries) Memory

abbrev Child := AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
    (Cfg := Cfg) (height := height) ×
  AuthenticatedNTT.RunResult (F := F) (Memory := Memory) (Response := Response)
    (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
    (k := k) (front := front) (queries := queries) (height := height)

variable (factory : Index → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
  b c r k front suffix m queries height)

/-- The actual child returns the native batch loop's private memory. -/
def step (index : Index) (memory : Memory) := do
  let result ← AuthenticatedNTT.program (factory index memory)
  pure (⟨result,result.2.2.memory,AuthenticatedNTT.accepted result.2⟩ :
    ShortCircuitSequence.StepResult (ActualResult (F := F) (Digest := Digest)
      (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) Memory)

def program (indices : List Index) (memory : Memory) := ShortCircuitSequence.program (step factory) indices memory

/-- Each retained entry includes the incoming private memory that selected
its stage factory, as well as that child's actual prefix and final state. -/
def witness (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) :
    List Index → Memory →
    CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height) →
    ProbComp (ShortCircuitSequence.Outcome Index
      (Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
        (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
        (front := front) (queries := queries) (height := height)) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  | [], memory, initial => pure (⟨[],memory,true⟩,initial)
  | index::rest, memory, initial => do
    let s := factory index memory
    let child ← MultiCommitmentPrefix.witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests s.tag [false,true]) s.commit (AuthenticatedNTT.continuation s) initial
    let later ← if AuthenticatedNTT.accepted child.2.1 then
        witness enc dummy rest child.2.1.2.memory child.2.2
      else pure (⟨[],child.2.1.2.memory,false⟩,child.2.2)
    pure (⟨(index,(memory,child))::later.1.results,later.1.memory,later.1.accepted⟩,later.2)

/-- Erase only analysis data, preserving original stage results and memory. -/
def erase
    (trace : ShortCircuitSequence.Outcome Index
      (Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
        (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
        (front := front) (queries := queries) (height := height)) Memory) :
    ShortCircuitSequence.Outcome Index
      (ActualResult (F := F) (Digest := Digest) (Response := Response)
        (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
        (front := front) (queries := queries) (height := height)) Memory :=
  ⟨trace.results.map (fun entry => (entry.1,(entry.2.2.1.1,entry.2.2.2.1))),trace.memory,trace.accepted⟩

/-- All retained prefixes erase to the literal existing NTT child loop,
including skipped suffixes, failed results and the exact shared final state. -/
theorem project_witness (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun outcome => (erase outcome.1,outcome.2)) <$> witness factory enc dummy indices memory initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)).run initial := by
  induction indices generalizing memory initial with
  | nil => rfl
  | cons index rest ih =>
    simp only [witness,program,ShortCircuitSequence.program,step,AuthenticatedNTT.program,
      MultiCommitmentPrefix.witness,MultiCommitmentPrefix.program,simulateQ_bind,StateT.run_bind,
      RecordRoots.run_program,map_bind,pure_bind,bind_assoc]
    congr 1
    funext first
    congr 1
    funext last
    split
    · simp only [map_bind,map_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure]
      have tail := ih last.1.2.memory last.2
      unfold program at tail
      rw [←tail]
      simp only [bind_map_left,erase,List.map_cons]
    · simp only [map_pure,simulateQ_pure,StateT.run_pure,erase,List.map_cons,List.map_nil]

end
end FormalProof4FHE.HasteBoots.NTTSequence
