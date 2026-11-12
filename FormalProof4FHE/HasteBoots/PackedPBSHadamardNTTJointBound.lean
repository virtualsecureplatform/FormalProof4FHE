module
public import FormalProof4FHE.HasteBoots.PackedPBSHadamardNTTProbability
public import FormalProof4FHE.HasteBoots.HadamardConditionalSoundness
@[expose] public section

/-! False original Hadamard relations and all reached original NTT risks share
one collision charge for the actual complete short-circuit program. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHadamardNTTJointBound
open OracleSpec OracleComp
open NativeRootMessage (Digest)
noncomputable section
variable {q log count b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {K Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

  [SampleableType (Fin n → ZMod q)] [SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]

/-- Three degree-two ZeroCheck terms and all original-factor PCS errors. -/
def rate
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (radius : ℕ) : ENNReal :=
  ((n : ENNReal)/Fintype.card (ZMod q))^b +
    (((((2*b-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b) +
    (n : ENNReal)*(((((2*b-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b) +
    ((2*count+1 : ℕ) : ENNReal)*
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) hs.domain radius

omit [SampleableType (Fin r → ZMod q)] in
/-- Later loop execution cannot increase the already determined safe
Hadamard event, even when its adaptive prover behavior may abort. -/
theorem safe_hadamard_risk_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (hadRadius : ℕ)
    (firstDegree : ∀ message point, (hs.interpretFirst message point).natDegree ≤ (2*b-1)*2)
    (messageDegree : ∀ message, (hs.interpret message).natDegree ≤ (2*b-1)*3)
    (hadSmall : (hadRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial)}[
      OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
        dummy capacity hadRadius outcome.1 ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2] ≤
      rate (K := K) hs hadRadius := by
  let h := PackedPBSHadamardNTT.hadamard family hs
  have conditional := ZeroCheckConditionalSoundness.original_safe_bound h basis dummy PBSHadamard.factors_complete
    enough capacity hadRadius 2 PBSHadamard.degree_bound firstDegree messageDegree hadSmall initial audited
  have bound : Pr{let first ← ZeroCheckConditionalSoundness.witness h dummy initial}[
      OriginalFactorExceptionUnion.OriginalRisk h dummy capacity hadRadius first ∧
        ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) first.2.2] ≤
      rate (K := K) hs hadRadius := by
    simpa only [rate, h, PackedPBSHadamardNTT.hadamard, CallerBoundStageRoots.hadamard,
      OwnedHadamardSoundness.stage, PBSHadamard.stage, OwnedHadamardSoundness.factor_error_sum] using conditional
  unfold PackedPBSHadamardNTT.witness
  apply le_trans (prEvent_bind_le_prEvent_of_forall_eq_zero _ _
    (fun first => OriginalFactorExceptionUnion.OriginalRisk h dummy capacity hadRadius first ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) first.2.2) _ ?_) bound
  intro first outside
  dsimp only [h] at outside
  by_cases passes : AuthenticatedZeroCheck.accepted first.2.1 = true
  · simp only [passes,ite_true,prEvent_norm]
    exact prEvent_eq_zero_of_forall_not _ _ (fun _ event => outside event)
  · simp [passes,prEvent_norm,outside]

/-- The whole composed stage has a conditional arithmetic bound from any
audited incoming state; the enclosing PBS caller owns the final hash charge. -/
theorem safe_risk_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (hadRadius : ℕ)
    (firstDegree : ∀ message point, (hs.interpretFirst message point).natDegree ≤ (2*b-1)*2)
    (messageDegree : ∀ message, (hs.interpret message).natDegree ≤ (2*b-1)*3)
    (hadSmall : (hadRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy
      initial)}[
      (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
        dummy capacity hadRadius outcome.1 ∨
      ∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1) ∧
      ¬(match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)] ≤
      rate (K := K) hs hadRadius + ((List.finRange (count+1)).map epsilon).sum := by
  have had := safe_hadamard_risk_bound length psi primitive family base hs basis dummy enough capacity hadRadius
    firstDegree messageDegree hadSmall initial audited
  have ntt := PackedPBSHadamardNTTProbability.safe_ntt_risk_bound length psi primitive family base hs basis dummy
    enough capacity radius epsilon encoding small calibrated initial audited
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
      dummy capacity hadRadius outcome.1 ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2) ∨
    (∃ later, outcome.2 = some later ∧ NTTSequenceSoundness.AnySafeRisk
      (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add had ntt)
  · intro outcome supported event
    obtain ⟨event,safe⟩ := event
    rcases outcome with ⟨first,optional⟩
    rcases event with risk | event
    · refine Or.inl ⟨risk,?_⟩
      intro bad
      apply safe
      cases optional with
      | none => exact bad
      | some later =>
        have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
        exact NTTSequenceSoundness.bad_persistent (PackedPBSNTTLoop.factory length psi primitive family base)
          hs.encoding dummy (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reached.2.2 bad
    · obtain ⟨later,reached,entry,member,risk⟩ := event
      change optional = some later at reached
      subst optional
      refine Or.inr ⟨later,rfl,entry,member,risk,?_⟩
      intro bad
      apply safe
      have reachedLoop := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
      exact NTTSequenceSoundness.child_bad_persistent (PackedPBSNTTLoop.factory length psi primitive family base)
        hs.encoding dummy (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reachedLoop.2.2 entry member bad

/-- The joint original-relation event pays Hadamard arithmetic, the full
reached NTT rate sum and ONE collision charge on the entire actual program.
The event also covers the final collision itself for subsequent composition. -/
theorem risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (hadRadius : ℕ)
    (firstDegree : ∀ message point, (hs.interpretFirst message point).natDegree ≤ (2*b-1)*2)
    (messageDegree : ∀ message, (hs.interpret message).natDegree ≤ (2*b-1)*3)
    (hadSmall : (hadRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
        dummy capacity hadRadius outcome.1 ∨
      ∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1) ∨
      (match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)] ≤
      (rate (K := K) hs hadRadius + ((List.finRange (count+1)).map epsilon).sum) +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (PackedPBSHadamardNTT.program length psi primitive family base hs)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have arithmetic := safe_risk_bound length psi primitive family base hs basis dummy enough capacity hadRadius
    firstDegree messageDegree hadSmall radius epsilon encoding small calibrated _ ⟨initial.1,fun _ => initial.2.2⟩
  have hash := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (RecordedSourceCoherence.Shape Cfg height) (PackedPBSHadamardNTT.program length psi primitive family base hs)
  rw [←PackedPBSHadamardNTT.project_witness length psi primitive family base hs dummy
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at hash
  apply le_trans (prEvent_mono _ _ (fun outcome =>
    (((OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
      dummy capacity hadRadius outcome.1 ∨
      ∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1) ∧
      ¬(match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)) ∨
    (match outcome.2 with
      | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
      | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2))) ?_)
  · apply (prEvent_or_le _ _ _).trans
    apply add_le_add arithmetic
    convert hash using 1
    apply prEvent_congr
    intro outcome
    cases outcome.2 <;> rfl
  · intro outcome event
    by_cases bad : (match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)
    · exact Or.inr bad
    · exact Or.inl ⟨event.resolve_right bad,bad⟩

/-- Typed interpolation supplies both degree bounds in the actual composed
program; no prover-supplied degree or truthfulness certificate remains. -/
theorem native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
    (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (hadRadius : ℕ)
    (hadSmall : (hadRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs))
        dummy capacity hadRadius outcome.1 ∨
      ∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1) ∨
      (match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)] ≤
      (rate (K := K) hs hadRadius + ((List.finRange (count+1)).map epsilon).sum) +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (PackedPBSHadamardNTT.program length psi primitive family base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs))
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  exact risk_or_bad_bound length psi primitive family base
    (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) basis dummy enough capacity hadRadius
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    hadSmall radius epsilon encoding small calibrated

/-- The typed native composed stage is reusable inside a larger audited
execution, with the collision charge left to its enclosing caller. -/
theorem native_safe_risk_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
    (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (hadRadius : ℕ)
    (hadSmall : (hadRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) dummy
      initial)}[
      (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs))
        dummy capacity hadRadius outcome.1 ∨
      ∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1) ∧
      ¬(match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)] ≤
      rate (K := K) hs hadRadius + ((List.finRange (count+1)).map epsilon).sum := by
  exact safe_risk_bound length psi primitive family base
    (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) basis dummy enough capacity hadRadius
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    hadSmall radius epsilon encoding small calibrated initial audited

end
end FormalProof4FHE.HasteBoots.PackedPBSHadamardNTTJointBound
