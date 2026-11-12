module
public import FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness
public import FormalProof4FHE.HasteBoots.CallerBoundStageRoots
@[expose] public section

/-! The monomial prefix executes two concrete packed NTT calls in native order.
Each call borrows its caller coefficient/evaluation roots and inherits the
previous call's actual private memory and entire ambient monitor state. -/
namespace FormalProof4FHE.HasteBoots.AmbientMonomialNTT
open OracleSpec OracleComp BinaryTree
open InteractiveAuthenticatedOpening
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {log b c r k front suffix m queries height : ℕ}

/-- Trusted roots, encoding and exact packed butterflies replace factory fields.
The factory's commitment work, returned private memory and other callbacks remain. -/
def factory (enc : MerkleOracle.Encoding Input Digest (List F)) (length : 2^c*b = 2^log)
    (psi : F) (primitive : IsPrimitiveRoot psi (2^(log+1))) (coefficients evaluations : Bool → Digest)
    (base : Bool → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height) (side : Bool) (memory : Memory) :=
  {CallerBoundStageRoots.ntt (coefficients side) (evaluations side)
    (PackedNTT.scheme length psi primitive (base side memory)) with encoding := enc}

variable [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]
variable (enc : MerkleOracle.Encoding Input Digest (List F)) (length : 2^c*b = 2^log)
  (psi : F) (primitive : IsPrimitiveRoot psi (2^(log+1))) (coefficients evaluations : Bool → Digest)
  (base : Bool → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)

abbrev Child (heights : Cfg → ℕ) := AmbientNTTSequence.Child heights (F := F) (Input := Input) (Digest := Digest)
  (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)

abbrev Trace (heights : Cfg → ℕ) := AmbientNTTSequenceSoundness.Trace heights (F := F) (Index := Bool) (Input := Input)
  (Digest := Digest) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)

def program (memory : Memory) :=
  AmbientNTTSequence.program (factory enc length psi primitive coefficients evaluations base) [false,true] memory

def witness (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  AmbientNTTSequence.witness (factory enc length psi primitive coefficients evaluations base) heights enc dummy [false,true] memory initial

/-- The retained loop witness erases to the exact two-call program, including
all commitment work, early rejection and returned memory/state. -/
theorem project_witness (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => (AmbientNTTSequence.erase heights outcome.1,outcome.2)) <$> witness enc length psi primitive coefficients evaluations base heights dummy memory initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights))
        (program enc length psi primitive coefficients evaluations base memory)).run initial :=
  AmbientNTTSequence.project_witness (factory enc length psi primitive coefficients evaluations base) heights enc dummy [false,true] memory initial

/-- Root binding follows from actual child support, including rejected calls. -/
theorem child_roots (heights : Cfg → ℕ) (dummy : Digest) (side : Bool) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (child : Child heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
      (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (supported : child ∈ support (AmbientNTT.witness heights
      (factory enc length psi primitive coefficients evaluations base side memory) dummy initial)) :
    child.1.1.1 = fun source => if source then evaluations side else coefficients side := by
  simp only [AmbientNTT.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst child
  simp only [factory,CallerBoundStageRoots.ntt,PackedNTT.scheme,simulateQ_bind,StateT.run_bind,
    simulateQ_pure,StateT.run_pure,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,same⟩ := firstSupported
  subst first
  rfl

/-- Every retained call uses the same enclosing root pair; a second factory
cannot independently choose substitute coefficient or evaluation commitments. -/
theorem retained_roots (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Trace heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
      (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (supported : outcome ∈ support (witness enc length psi primitive coefficients evaluations base heights dummy memory initial))
    (entry : Bool × Memory × Child heights (F := F) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
      (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results) :
    entry.2.2.1.1.1 = fun source => if source then evaluations entry.1 else coefficients entry.1 := by
  obtain ⟨before,present⟩ := AmbientNTTSequenceSoundness.retained_child_support
    (factory enc length psi primitive coefficients evaluations base) heights enc dummy [false,true] memory initial outcome supported entry member
  exact child_roots enc length psi primitive coefficients evaluations base heights dummy entry.1 entry.2.1 before entry.2.2 present

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType F] [SampleableType (Fin r → F)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- The two reached native calls have their derived original-owner rates under
one final ambient exclusion. There is no child restart, security certificate or
extra availability/collision charge. -/
theorem original_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ) (dummy : Digest)
    (basis : Module.Basis (Fin b) F K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (radius : Bool → ℕ) (epsilon : Bool → ENNReal)
    (geometry : ∀ side memory source, heights ((base side memory).tag source) = height)
    (small : ∀ side memory, (radius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base side memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ side memory,
      ((((r : ENNReal)/Fintype.card F)^k) +
        (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) (base side memory).domain (radius side) +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) (base side memory).domain (radius side)) ≤ epsilon side)
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness enc length psi primitive coefficients evaluations base heights dummy memory initial)}[
      AmbientNTTSequenceSoundness.AnyOriginalRisk (factory enc length psi primitive coefficients evaluations base) heights dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] ≤ epsilon false + epsilon true := by
  have bound := AmbientNTTSequenceSoundness.derived_original_safe_union_bound
    (factory enc length psi primitive coefficients evaluations base) heights enc dummy basis [false,true] enough capacity radius epsilon
    (fun _ _ => rfl) geometry small calibrated memory initial audited
  simpa only [witness,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using bound

end
end FormalProof4FHE.HasteBoots.AmbientMonomialNTT
