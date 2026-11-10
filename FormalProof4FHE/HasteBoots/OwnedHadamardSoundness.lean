module
public import FormalProof4FHE.HasteBoots.PBSHadamard
public import FormalProof4FHE.HasteBoots.OriginalFactorExceptionUnion
@[expose] public section

/-! Recorded-original Hadamard sources with trusted setup key roots. All
original digit/key/result factors retain their authenticated native openings.
No key coefficients or folds are substituted for those openings. -/
namespace FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
noncomputable section
variable {F K FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] {count b n front suffix m queries height : ℕ}

/-- Only setup key slots are fixed externally. Digits and the final result
retain their originally emitted commitments and their original slot order. -/
def roots (expected : Fin count → Digest) (supplied : PBSHadamard.Factor count → Digest) :
    PBSHadamard.Factor count → Digest
  | .inl (index,true) => expected index
  | other => supplied other

theorem roots_key (expected : Fin count → Digest) (supplied : PBSHadamard.Factor count → Digest) (index : Fin count) :
    roots expected supplied (.inl (index,true)) = expected index := rfl

theorem roots_digit (expected : Fin count → Digest) (supplied : PBSHadamard.Factor count → Digest) (index : Fin count) :
    roots expected supplied (.inl (index,false)) = supplied (.inl (index,false)) := rfl

theorem roots_result (expected : Fin count → Digest) (supplied : PBSHadamard.Factor count → Digest) :
    roots expected supplied (.inr ()) = supplied (.inr ()) := rfl

/-- Every product pair keeps its digit and key opening; the result is last. -/
theorem factors_length (count : ℕ) : (PBSHadamard.factors count).length = 2*count+1 := by
  simp [PBSHadamard.factors,List.length_flatMap,Nat.mul_comm]

/-- Public setup keys still contribute PCS arithmetic error because the native
verifier opens their commitments rather than computing their folds. -/
theorem factor_error_sum (count : ℕ) (error : ENNReal) :
    ((PBSHadamard.factors count).map (fun _ => error)).sum = ((2*count+1 : ℕ) : ENNReal)*error := by
  simp [List.sum_replicate,factors_length,nsmul_eq_mul]

/-- Trusted degree-two native shape, original opening order, and key roots
from public setup. All actual prover callbacks and their hash calls remain. -/
def stage (expected : Fin count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count) FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) :=
  { PBSHadamard.stage s with
    commit := do
      let emission ← s.commit
      pure (roots expected emission.1,emission.2) }

variable [DecidableEq Digest]

/-- Original recorded-owner interpretation is the literal native Hadamard
identity, for all cells and lanes, including the original result slot. -/
theorem original_vanishes_iff (expected : Fin count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count) FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :
    PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
      (OriginalFactorExceptionUnion.originalSources (stage expected s) dummy capacity radius owner) ↔
    PBSHadamard.Relation (OriginalFactorExceptionUnion.originalSources (stage expected s) dummy capacity radius owner) :=
  PBSHadamard.vanishes_iff _

variable [DecidableEq Input]
  [Fintype Digest] [SampleableType Digest]
  [SampleableType F] [SampleableType (Fin b → F)] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)]
  [SampleableType (Fin b → Fin b → F)] [SampleableType (Fin b → ((Fin b → F) × F))]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

omit [Fintype Digest] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))] [Fintype F] in
/-- Every supported execution uses the trusted setup root at each key slot,
regardless of the roots returned by the arbitrary commitment callback. -/
theorem witness_key_root (expected : Fin count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count) FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (outcome : AuthenticatedZeroCheck.Prefix (Factor := PBSHadamard.Factor count) (Digest := Digest)
        (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      AuthenticatedZeroCheck.RunResult (F := F) (Factor := PBSHadamard.Factor count) (Memory := Memory)
        (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AuthenticatedZeroCheck.witness (stage expected s) dummy))
    (index : Fin count) : outcome.1.1.1 (.inl (index,true)) = expected index := by
  simp only [AuthenticatedZeroCheck.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [stage,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,equal⟩ := firstSupported
  subst first
  rfl

/-- Original-owner false relation, PCS errors for ALL original factors, and
ONE hash charge for the complete committed/ZeroCheck/native-worker run. -/
theorem native_original_soundness_from_empty [NeZero m] [NeZero b]
    (characteristic : ℕ) [CharP F characteristic]
    (firstSmall : (2*b-1)*2+1 ≤ characteristic) (roundSmall : (2*b-1)*3+1 ≤ characteristic)
    (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (expected : Fin count → Digest)
    (s : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      (Fin b → Fin ((2*b-1)*2+1) → F) (Fin ((2*b-1)*3+1) → F)
      Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← (AuthenticatedZeroCheck.witness
      (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s)) dummy)}[
      OriginalFactorExceptionUnion.OriginalRisk
        (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s))
        dummy capacity radius outcome] ≤
      (((n : ENNReal)/Fintype.card F)^b +
        (((((2*b-1)*2+1 : ℕ) : ENNReal)/Fintype.card F)^b) +
        (n : ENNReal)*(((((2*b-1)*3 : ℕ) : ENNReal)/Fintype.card F)^b) +
        ((2*count+1 : ℕ) : ENNReal)*
          JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedZeroCheck.program (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s)))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  rw [←factor_error_sum count (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)]
  exact OriginalFactorExceptionUnion.original_soundness_from_empty
    (AuthenticatedZeroCheck.nativeScheme characteristic 2 firstSmall roundSmall nodesEnough (stage expected s))
    basis dummy PBSHadamard.factors_complete enough capacity radius 2 PBSHadamard.degree_bound
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small

end
end FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
