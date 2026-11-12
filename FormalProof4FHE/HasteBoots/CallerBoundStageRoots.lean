module
public import FormalProof4FHE.HasteBoots.CrossStageSourceCoherence
@[expose] public section

/-! Child commitment factories retain their calls and private memory, while
public commitment roots come from the enclosing caller. This models fixed
public child statements; correspondence with Rust invocation remains separate. -/
namespace FormalProof4FHE.HasteBoots.CallerBoundStageRoots
open OracleSpec OracleComp
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k n count front suffix m queries height : ℕ}

/-- Retain the original commitment computation and memory; fix both public
NTT source roots to the enclosing statement. -/
def ntt (coefficient evaluation : Digest)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) :=
  { s with commit := do
      let original ← s.commit
      pure ((fun side => if side then evaluation else coefficient),original.2) }

/-- The caller supplies original digit/result roots; setup supplies key roots. -/
def hadamard (expected : Fin count → Digest) (publicRoots : PBSHadamard.Factor count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) :=
  OwnedHadamardSoundness.stage expected
    { s with commit := do
        let original ← s.commit
        pure (publicRoots,original.2) }

variable [SampleableType Digest]
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]

/-- Supported child executions retain exactly the caller's two public roots. -/
theorem ntt_witness_roots (coefficient evaluation : Digest)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest)
    (outcome : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := F) (Memory := Memory) (Response := Response)
        (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
        (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AuthenticatedNTT.witness (ntt coefficient evaluation s) dummy)) :
    outcome.1.1.1 = (fun side => if side then evaluation else coefficient) := by
  simp only [AuthenticatedNTT.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [ntt,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,equal⟩ := firstSupported
  subst first
  rfl

variable [SampleableType (PackedZeroReduction.Points F n b)]
  [SampleableType (Fin b → Fin b → F)]

/-- Every Hadamard slot uses its caller/setup root, including digit and result
slots; a child factory cannot replace an enclosing public commitment. -/
theorem hadamard_witness_roots
    (expected : Fin count → Digest) (publicRoots : PBSHadamard.Factor count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor count) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := F) (Factor := PBSHadamard.Factor count) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AuthenticatedZeroCheck.witness (hadamard expected publicRoots s) dummy)) :
    outcome.1.1.1 = OwnedHadamardSoundness.roots expected publicRoots := by
  simp only [AuthenticatedZeroCheck.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [hadamard,OwnedHadamardSoundness.stage,simulateQ_bind,StateT.run_bind,simulateQ_pure,
    StateT.run_pure,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨middle,middleSupported,equal⟩ := firstSupported
  subst first
  obtain ⟨emission,_,equal⟩ := middleSupported
  subst middle
  rfl


/-- Caller wiring derives the root association from supported executions;
no equality of independently chosen child roots is assumed. -/
theorem witness_root_association
    (coefficient : Digest) (expected : Fin count → Digest) (publicRoots : PBSHadamard.Factor count → Digest)
    (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (no : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := F) (Memory := Memory) (Response := Response)
        (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
        (k := k) (front := front) (queries := queries) (height := height))
    (ho : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor count) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := F) (Factor := PBSHadamard.Factor count) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (nttSupported : no ∈ support (AuthenticatedNTT.witness
      (ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns) dummy))
    (hadamardSupported : ho ∈ support (AuthenticatedZeroCheck.witness (hadamard expected publicRoots hs) dummy)) :
    no.1.1.1 true = ho.1.1.1 factor := by
  rw [ntt_witness_roots _ _ ns dummy no nttSupported,
    hadamard_witness_roots expected publicRoots hs dummy ho hadamardSupported]
  rfl

/-- Fresh original sources agree in a shared audited history, using the
root association derived from actual caller-bound child witness support. -/
theorem witness_source_association
    (coefficient : Digest) (expected : Fin count → Digest) (publicRoots : PBSHadamard.Factor count → Digest)
    (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (no : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := F) (Memory := Memory) (Response := Response)
        (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
        (k := k) (front := front) (queries := queries) (height := height))
    (ho : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor count) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := F) (Factor := PBSHadamard.Factor count) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (nttSupported : no ∈ support (AuthenticatedNTT.witness
      (ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns) dummy))
    (hadamardSupported : ho ∈ support (AuthenticatedZeroCheck.witness (hadamard expected publicRoots hs) dummy))
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited ns.encoding dummy (RecordedSourceCoherence.Shape Cfg height) state)
    (nttRecorded : ⟨ns.tag true, CommittedJointMatrixOpening.snapshots ns.tag no.1 true⟩ ∈ state.checkpoints.checkpoints)
    (hadamardRecorded : ⟨hs.tag factor, CommittedJointMatrixOpening.snapshots hs.tag ho.1 factor⟩ ∈ state.checkpoints.checkpoints)
    (encoding : hs.encoding = ns.encoding) (domain : hs.domain = ns.domain)
    (tags : ns.tag true = hs.tag factor) :
    AuthenticatedNTT.sources ns dummy capacity radius no.1 true =
      QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
        (AuthenticatedZeroCheck.sources hs dummy capacity radius ho.1 factor) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) state := by
  have roots := witness_root_association coefficient expected publicRoots factor ns hs dummy no ho
    nttSupported hadamardSupported
  exact CrossStageSourceCoherence.ntt_hadamard_eq_or_bad ns hs expected dummy capacity radius state audited
    (CommittedJointMatrixOpening.snapshots ns.tag no.1)
    (CommittedJointMatrixOpening.snapshots hs.tag ho.1) factor nttRecorded hadamardRecorded
    encoding domain tags roots

end
end FormalProof4FHE.HasteBoots.CallerBoundStageRoots
