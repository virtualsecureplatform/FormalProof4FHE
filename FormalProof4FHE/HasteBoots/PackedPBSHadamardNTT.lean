module
public import FormalProof4FHE.HasteBoots.PackedPBSNTTLoop
@[expose] public section

/-! The original-root Hadamard stage precedes the complete fixed-slot NTT
loop. Private memory and shared history pass through exactly; rejection skips
the loop. Rust byte/transcript correspondence remains a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHadamardNTT
open OracleSpec OracleComp
open NativeRootMessage (Digest)
noncomputable section
variable {q log count b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev HadamardOutcome := HadamardNTTSourceAssociation.FirstOutcome (F := ZMod q) (Input := Input)
  (Digest := Digest) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
  (b := b) (n := n) (count := count) (front := front) (queries := queries) (height := height)

abbrev LoopOutcome := NTTSequenceSoundness.Trace (F := ZMod q) (Index := Fin (count+1)) (Input := Input)
    (Digest := Digest) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family count)
  (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)

def publicRoots (factor : PBSHadamard.Factor count) := (PackedPBSOriginalReferences.roleReference family factor).root

def hadamard := CallerBoundStageRoots.hadamard family.keys (publicRoots family) hs

/-- The NTT loop receives the Hadamard child's actual returned private memory. -/
def program := do
  let first ← AuthenticatedZeroCheck.program (hadamard family hs)
  if AuthenticatedZeroCheck.accepted first.2 then
    let later ← PackedPBSNTTLoop.program length psi primitive family base first.2.2.memory
    pure (first,some later)
  else pure (first,none)

/-- Analysis retains both actual recording histories without changing calls. -/
def witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let h := hadamard family hs
  let first ← MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h) initial
  if AuthenticatedZeroCheck.accepted first.2.1 then
    let later ← PackedPBSNTTLoop.witness length psi primitive family base hs.encoding dummy first.2.1.2.memory first.2.2
    pure (first,some later)
  else pure (first,none)

/-- Erasure preserves the Hadamard-before-loop order, actual private memory,
failed-path early return and the exact final shared state. -/
theorem project_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun outcome => match outcome.2 with
      | none => (((outcome.1.1.1,outcome.1.2.1),none),outcome.1.2.2)
      | some later => (((outcome.1.1.1,outcome.1.2.1),some (NTTSequence.erase later.1)),later.2)) <$>
      witness length psi primitive family base hs dummy initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (RecordedSourceCoherence.Shape Cfg height)) (program length psi primitive family base hs)).run initial := by
  simp only [witness,program,AuthenticatedZeroCheck.program,MultiCommitmentPrefix.witness,MultiCommitmentPrefix.program,
    simulateQ_bind,StateT.run_bind,RecordRoots.run_program,map_bind,pure_bind,bind_assoc]
  congr 1
  funext first
  congr 1
  funext last
  split
  · simp only [map_bind,map_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure]
    rw [←PackedPBSNTTLoop.project_witness length psi primitive family base hs.encoding dummy last.1.2.memory last.2]
    simp only [bind_map_left]
  · simp only [map_pure,simulateQ_pure,StateT.run_pure]


omit [DecidableEq Digest] [SampleableType Digest] in
/-- Setup-key overriding preserves the original reference family's root vector. -/
theorem public_roots_stable :
    OwnedHadamardSoundness.roots family.keys (publicRoots family) = publicRoots family := by
  funext factor
  cases factor with
  | inl pair => rcases pair with ⟨index,bit⟩; cases bit <;> rfl
  | inr tag => cases tag; rfl

variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (first : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
    (front := front) (queries := queries) (height := height))
  (later : LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := count)
    (front := front) (queries := queries) (height := height))
  (supported : (first,some later) ∈ support (witness length psi primitive family base hs dummy initial))

include supported in
/-- Reaching the loop derives Hadamard acceptance and both actual supports;
the loop starts at its predecessor's actual memory and final shared state. -/
theorem reached_loop :
    AuthenticatedZeroCheck.accepted first.2.1 = true ∧
    first ∈ support (MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests (hadamard family hs).tag (hadamard family hs).factors)
      (hadamard family hs).commit (AuthenticatedZeroCheck.continuation (hadamard family hs)) initial) ∧
    later ∈ support (PackedPBSNTTLoop.witness length psi primitive family base hs.encoding dummy
      first.2.1.2.memory first.2.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  by_cases passes : AuthenticatedZeroCheck.accepted selected.2.1 = true
  · simp only [passes,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
    obtain ⟨tail,tailSupported,equal⟩ := remainder
    have firstEq : first = selected := congrArg Prod.fst equal
    have laterEq : later = tail := Option.some.inj (congrArg Prod.snd equal)
    subst selected
    subst tail
    exact ⟨passes,selectedSupported,tailSupported⟩
  · simp [passes] at remainder

include supported in
/-- The Hadamard prefix roots come from the same original reference family
as the loop, regardless of the arbitrary child commitment callback. -/
theorem hadamard_roots : first.1.1.1 = publicRoots family := by
  have reached := reached_loop length psi primitive family base hs dummy initial first later supported
  have hcommit : (hadamard family hs).commit = (do
      let emission ← hs.commit
      pure (publicRoots family,emission.2)) := by
    simp only [hadamard,CallerBoundStageRoots.hadamard,OwnedHadamardSoundness.stage,PBSHadamard.stage,
      bind_assoc,pure_bind,public_roots_stable]
  apply HadamardNTTSourceAssociation.fixed_roots hs.encoding dummy (publicRoots family) hs.commit
    (CommittedJointMatrixOpening.requests (hadamard family hs).tag (hadamard family hs).factors)
    (AuthenticatedZeroCheck.continuation (hadamard family hs)) initial first
  rw [←hcommit]
  exact reached.2.1

include supported in
/-- Acceptance covers every original NTT slot and ties its retained evaluation
root to the selected original Hadamard prefix factor, with no root certificate. -/
theorem accepted_slots_bound (accepted : later.1.accepted = true) (slot : Fin (count+1)) :
    ∃ incoming child, (slot,(incoming,child)) ∈ later.1.results ∧
      child.1.1.1 false = family.coefficients slot ∧
      child.1.1.1 true = first.1.1.1 (PackedPBSOriginalReferences.evaluationFactor slot) := by
  have reached := reached_loop length psi primitive family base hs dummy initial first later supported
  have roots := hadamard_roots length psi primitive family base hs dummy initial first later supported
  obtain ⟨incoming,child,member,coefficient,evaluation⟩ := PackedPBSNTTLoop.all_slots_bound length psi primitive family base
    hs.encoding dummy first.2.1.2.memory first.2.2 later reached.2.2 accepted slot
  refine ⟨incoming,child,member,coefficient,?_⟩
  rw [roots]
  have original := congrArg NativeGoldParameterStore.Reference.root (PackedPBSOriginalReferences.evaluation_reference family slot)
  exact evaluation.trans original.symm

end
end FormalProof4FHE.HasteBoots.PackedPBSHadamardNTT
