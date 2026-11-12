module
public import FormalProof4FHE.HasteBoots.PackedPBSLoopFunctionBound
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionReferences
public import FormalProof4FHE.HasteBoots.DecompositionConditionalSoundness
@[expose] public section

/-! The Hadamard and complete NTT loop are followed by the first reconstruction
stage. The next Rust call is its comparison verifier, before the second half;
this prefix does not move either call across that boundary. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSFirstReconstruction
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev Before := HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := 2*d)
    (front := front) (queries := queries) (height := height) ×
  Option (LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := 2*d)
    (front := front) (queries := queries) (height := height))

abbrev LinearOutcome := AuthenticatedLinear.Prefix (Digest := Digest) (CommitMemory := CommitMemory)
    (Input := Input) (Cfg := Cfg) (count := 2*d+2) (height := height) ×
  AuthenticatedLinear.RunResult (F := ZMod q) (Memory := Memory) (Response := Response)
    (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (count := 2*d+2)
    (front := front) (suffix := suffix) (queries := queries) (height := height)

def eraseBefore (before : Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height)) :=
  ((before.1.1.1,before.1.2.1),before.2.map (fun later => NTTSequence.erase later.1))

def beforeState (before : Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height)) :=
  match before.2 with
  | none => before.1.2.2
  | some later => later.2

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

/-- Native reconstruction receives caller-fixed original input/digit roots;
only borrow roots remain supplied by its retained commitment callback. -/
def reconstruction (half : Bool) (memory : Memory) :=
  AuthenticatedLinear.nativeScheme q nodesEnough
    (OwnedDecompositionSoundness.stage (inputs.roots half)
      (fun level => family.coefficients (PackedPBSDecompositionReferences.digitSlot half level)) radix (linearBase memory))

def program := do
  let before ← PackedPBSHadamardNTT.program length psi primitive family base hs
  match before.2 with
  | none => pure (before,none)
  | some later =>
    if later.accepted then
      let result ← AuthenticatedLinear.program (reconstruction family inputs nodesEnough radix linearBase false later.memory)
      pure (before,some result)
    else pure (before,none)

def witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial
  match before.2 with
  | none => pure (before,none)
  | some later =>
    if later.1.accepted then
      let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
      let result ← MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
        (AuthenticatedLinear.continuation l) later.2
      pure (before,some result)
    else pure (before,none)

/-- The prefix erasure exposes its exact actual state before reconstruction. -/
theorem project_before (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun before => (eraseBefore before,beforeState before)) <$>
      PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (RecordedSourceCoherence.Shape Cfg height)) (PackedPBSHadamardNTT.program length psi primitive family base hs)).run initial := by
  convert PackedPBSHadamardNTT.project_witness length psi primitive family base hs dummy initial using 1
  congr 1
  funext before
  cases equal : before.2 <;> simp [eraseBefore,beforeState,equal]

/-- Erasure preserves failed paths, actual NTT-returned memory and the same
shared state; no reconstruction work is performed after a rejected loop. -/
theorem project_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun outcome => ((eraseBefore outcome.1,outcome.2.map (fun child => (child.1.1,child.2.1))),
      match outcome.2 with
      | none => beforeState outcome.1
      | some child => child.2.2)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (RecordedSourceCoherence.Shape Cfg height))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase)).run initial := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←project_before length psi primitive family base hs dummy initial]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  cases equal : before.2 with
  | none => simp [equal,eraseBefore,beforeState,map_pure,simulateQ_pure,StateT.run_pure]
  | some later =>
    simp only [equal,eraseBefore,Option.map_some,NTTSequence.erase]
    split
    · simp only [map_bind,map_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
        beforeState,equal,Option.map_some]
      let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
      have projected := MultiCommitmentPrefix.project_witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
        (AuthenticatedLinear.continuation l) later.2
      unfold AuthenticatedLinear.program
      rw [←projected]
      simp only [bind_map_left]
      rfl
    · simp [beforeState,equal,map_pure,simulateQ_pure,StateT.run_pure]

variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height))
  (child : LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (d := d) (front := front) (suffix := suffix)
    (queries := queries) (height := height))
  (supported : (before,some child) ∈ support
    (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial))

include supported in
/-- Reaching reconstruction derives both prior supports, the accepted NTT
loop and the exact inherited private memory/state used by this child. -/
theorem reached_reconstruction :
    ∃ later, before.2 = some later ∧ later.1.accepted = true ∧
      before ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial) ∧
      child ∈ support (MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests
          (reconstruction family inputs nodesEnough radix linearBase false later.1.memory).tag
          (AuthenticatedLinear.factors (2*d+2)))
        (reconstruction family inputs nodesEnough radix linearBase false later.1.memory).commit
        (AuthenticatedLinear.continuation (reconstruction family inputs nodesEnough radix linearBase false later.1.memory)) later.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none => simp [equal] at remainder
  | some later =>
    by_cases passed : later.1.accepted = true
    · simp only [equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have sameBefore : before = selected := congrArg Prod.fst same
      have sameChild : child = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨later,equal,passed,selectedSupported,actualSupported⟩
    · simp [equal,passed] at remainder

include supported in
/-- The actual child uses the caller's original input root and first-half
coefficient roots, including on subsequent linear/opening rejection paths. -/
theorem reconstruction_roots :
    child.1.1.1 DecompositionLinear.input = inputs.roots false ∧
    ∀ level, child.1.1.1 (DecompositionLinear.digit level) =
      family.coefficients (PackedPBSDecompositionReferences.digitSlot false level) := by
  obtain ⟨later,_,_,_,present⟩ := reached_reconstruction length psi primitive family inputs base hs nodesEnough
    radix linearBase dummy initial before child supported
  simp only [MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at present
  obtain ⟨first,firstSupported,last,_,equal⟩ := present
  subst child
  simp only [reconstruction,AuthenticatedLinear.nativeScheme,OwnedDecompositionSoundness.stage,
    DecompositionLinear.stage,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,same⟩ := firstSupported
  subst first
  exact ⟨OwnedDecompositionSoundness.roots_input (inputs.roots false)
    (fun level => family.coefficients (PackedPBSDecompositionReferences.digitSlot false level)) emission.1.1,
    fun level => OwnedDecompositionSoundness.roots_digit (inputs.roots false)
      (fun i => family.coefficients (PackedPBSDecompositionReferences.digitSlot false i)) emission.1.1 level⟩

end
end FormalProof4FHE.HasteBoots.PackedPBSFirstReconstruction
