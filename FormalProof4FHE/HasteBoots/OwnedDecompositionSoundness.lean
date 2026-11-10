module
public import FormalProof4FHE.HasteBoots.OwnedLinearSoundness
public import FormalProof4FHE.HasteBoots.DecompositionLinear
@[expose] public section

/-! Original-owner reconstruction with caller-selected input/digit roots.
Only borrow roots are supplied by the decomposition proof. The native linear
stage checks reconstruction and both borrow endpoints on the same registry. -/
namespace FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
open OracleSpec OracleComp BinaryTree
open InteractiveAuthenticatedOpening
noncomputable section
variable {d : ℕ} {Digest : Type}

def roots (inputRoot : Digest) (digits : Fin d → Digest) (supplied : Fin (2*d+2) → Digest)
    (factor : Fin (2*d+2)) : Digest :=
  if zero : factor.val = 0 then inputRoot
  else if small : factor.val ≤ d then digits ⟨factor.val-1,by omega⟩ else supplied factor

theorem roots_input (inputRoot : Digest) (digits : Fin d → Digest) (supplied : Fin (2*d+2) → Digest) :
    roots inputRoot digits supplied DecompositionLinear.input = inputRoot := by
  simp [roots,DecompositionLinear.input]

theorem roots_digit (inputRoot : Digest) (digits : Fin d → Digest) (supplied : Fin (2*d+2) → Digest) (i : Fin d) :
    roots inputRoot digits supplied (DecompositionLinear.digit i) = digits i := by
  have small : i.val+1 ≤ d := by have := i.isLt; omega
  simp [roots,DecompositionLinear.digit,small]

theorem roots_borrow (inputRoot : Digest) (digits : Fin d → Digest) (supplied : Fin (2*d+2) → Digest) (i : Fin (d+1)) :
    roots inputRoot digits supplied (DecompositionLinear.borrow i) = supplied (DecompositionLinear.borrow i) := by
  have large : ¬d+1+i.val ≤ d := by omega
  simp [roots,DecompositionLinear.borrow,large]

theorem registry_error_sum (count : ℕ) (error : ENNReal) :
    ((AuthenticatedLinear.factors count).map (fun _ => error)).sum = (count : ENNReal)*error := by
  simp [AuthenticatedLinear.factors,nsmul_eq_mul]

variable {F Input Cfg Response Memory CommitMemory : Type} [Field F]
  {b front suffix m queries height : ℕ}

def stage (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory (2*d+2) b front suffix m queries height) :=
  { DecompositionLinear.stage radix s with
    commit := do
      let emission ← s.commit
      pure (roots inputRoot digits emission.1,emission.2) }

variable [DecidableEq Digest] [DecidableEq F]

theorem original_relation_iff (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory (2*d+2) b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :
    PackedLinear.Holds (DecompositionLinear.relations radix)
      (OwnedLinearSoundness.originalSources (stage inputRoot digits radix s) dummy capacity radius owner) ↔
    DecompositionLinear.Relation radix
      (OwnedLinearSoundness.originalSources (stage inputRoot digits radix s) dummy capacity radius owner) :=
  DecompositionLinear.holds_iff radix _

section Execution
variable [DecidableEq Input] [Fintype F] [SampleableType Digest]
  [SampleableType (Fin b → F)] [SampleableType (TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]

/-- Every supported execution uses the caller's input and digit commitments,
including executions whose subsequent linear check or opening rejects. -/
theorem witness_expected_roots (inputRoot : Digest) (digits : Fin d → Digest) (radix : F)
    (s : AuthenticatedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory (2*d+2) b front suffix m queries height)
    (dummy : Digest)
    (outcome : AuthenticatedLinear.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) (count := 2*d+2) ×
      AuthenticatedLinear.RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input)
        (Digest := Digest) (Cfg := Cfg) (b := b) (count := 2*d+2) (front := front) (suffix := suffix)
        (queries := queries) (height := height))
    (supported : outcome ∈ support (AuthenticatedLinear.witness (stage inputRoot digits radix s) dummy)) :
    outcome.1.1.1 DecompositionLinear.input = inputRoot ∧
      ∀ i : Fin d, outcome.1.1.1 (DecompositionLinear.digit i) = digits i := by
  simp only [AuthenticatedLinear.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [stage,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,equal⟩ := firstSupported
  subst first
  exact ⟨roots_input inputRoot digits emission.1.1,fun i => roots_digit inputRoot digits emission.1.1 i⟩

end Execution

variable {p : ℕ} [Fact p.Prime] [NeZero b] [NeZero m]
  [DecidableEq Input] [Fintype Digest] [SampleableType Digest]
  [SampleableType (Fin b → ZMod p)] [SampleableType (TestMatrix (ZMod p) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]

/-- No caller-supplied analysis field/basis, source-safety, wrong-opening or
linear-validity certificate is needed. Tuple lookup remains a separate check. -/
theorem soundness_from_empty
    (inputRoot : Digest) (digits : Fin d → Digest) (radix : ZMod p) (nodesEnough : 2*b ≤ p)
    (s : AuthenticatedLinear.Scheme (ZMod p) Input Digest Cfg Response Memory CommitMemory (2*d+2) b front suffix m queries height)
    (dummy : Digest) (enough : m ≤ 2^height) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) < (PCSParameters.distance height m : ℚ≥0)/3) :
    Pr{let outcome ← (AuthenticatedLinear.witness
      (AuthenticatedLinear.nativeScheme p nodesEnough (stage inputRoot digits radix s)) dummy)}[
      OwnedLinearSoundness.OriginalRisk
        (AuthenticatedLinear.nativeScheme p nodesEnough (stage inputRoot digits radix s)) dummy capacity radius outcome] ≤
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/p)^b)) +
        ((2*d+2 : ℕ) : ENNReal)*PCSParameters.error p b height m queries radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedLinear.program (AuthenticatedLinear.nativeScheme p nodesEnough (stage inputRoot digits radix s)))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have liftedSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := PCSAnalysisField.Alphabet p b) s.domain) m :
        Set (Fin (2^height) → PCSAnalysisField.Alphabet p b)) : ℚ≥0)/3 := by
    rwa [PCSParameters.lifted_distance]
  have bound := OwnedLinearSoundness.original_soundness_from_empty (K := PCSAnalysisField.Alphabet p b)
    (AuthenticatedLinear.nativeScheme p nodesEnough (stage inputRoot digits radix s)) (PCSAnalysisField.basis p b)
    dummy (by simpa only [Fintype.card_fin] using enough) capacity radius liftedSmall
  simp only [registry_error_sum,PCSParameters.error_eq,ZMod.card] at bound
  have encoding : (AuthenticatedLinear.nativeScheme p nodesEnough (stage inputRoot digits radix s)).encoding = s.encoding := rfl
  rw [encoding] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
