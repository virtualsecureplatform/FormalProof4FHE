module
public import FormalProof4FHE.HasteBoots.PackedPBSLoopEnforcement
@[expose] public section

/-! Wrong transforms against original Hadamard factors are measured on the
actual complete accepted loop, jointly with original Hadamard relation errors. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSLoopFunctionBound
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open CommittedJointMatrixOpening (snapshots)
noncomputable section
variable {q log count b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family count)
  (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)

/-- A wrong polynomial row at any retained original slot of the accepted
loop. The target is the actual original Hadamard prefix source. -/
def WrongTransform (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height) ×
      Option (LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
        (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := count)
        (front := front) (queries := queries) (height := height))) : Prop :=
  ∃ later, outcome.2 = some later ∧ later.1.accepted = true ∧
    ∃ entry ∈ later.1.results, ∃ row : MatrixFold.Cube r,
      BlindRotationNTT.transform log psi
        (PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1)
          dummy capacity radius entry.2.2.1 false) row) ≠
      PackedNTTBinding.row length
        (QueryReindex.source ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm)
          (AuthenticatedZeroCheck.sources hs dummy capacity radius outcome.1.1
            (PackedPBSOriginalReferences.evaluationFactor entry.1))) row

/-- Any number of row/slot failures reduce to the existing joint risk event,
using only the actual retained child support and original root family. -/
theorem wrong_transform_coverage (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (domain : ∀ slot incoming, hs.domain = (base slot incoming).domain)
    (tags : ∀ slot incoming, (base slot incoming).tag true = hs.tag (PackedPBSOriginalReferences.evaluationFactor slot))
    (outcome : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height) ×
      Option (LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
        (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := count)
        (front := front) (queries := queries) (height := height)))
    (supported : outcome ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial))
    (wrong : WrongTransform length psi base hs dummy capacity radius outcome) :
    (∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
      (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity (fun _ => radius) later.1) ∨
    (match outcome.2 with
      | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
      | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2) := by
  obtain ⟨later,reached,accepted,entry,member,wrong⟩ := wrong
  rcases outcome with ⟨first,optional⟩
  change optional = some later at reached
  subst optional
  rcases PackedPBSLoopEnforcement.false_transform_coverage length psi primitive family base hs dummy initial
      first later supported entry member capacity radius audited (encoding _ _) (domain _ _) (tags _ _)
      accepted wrong with risk | bad
  · exact Or.inl ⟨later,rfl,risk⟩
  · exact Or.inr bad

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]
  [SampleableType (Fin n → ZMod q)] [SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]

/-- The actual typed-message program's accepted original relation failures
and wrong transforms share its single expected hash charge, with no row union. -/
theorem native_original_relation_bound [Fintype Digest] [NeZero m] [NeZero b]
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
    (radius : ℕ)
    (hadSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (domain : ∀ slot incoming, hs.domain = (base slot incoming).domain)
    (tags : ∀ slot incoming, (base slot incoming).tag true = hs.tag (PackedPBSOriginalReferences.evaluationFactor slot))
    (small : ∀ slot incoming, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) radius ≤ epsilon slot) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs))
        dummy capacity radius outcome.1 ∨
      WrongTransform length psi base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) dummy capacity radius outcome) ∨
      (match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)] ≤
      (PackedPBSHadamardNTTJointBound.rate (K := K) hs radius + ((List.finRange (count+1)).map epsilon).sum) +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (PackedPBSHadamardNTT.program length psi primitive family base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs))
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  let ns := (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs)
  have bound := PackedPBSHadamardNTTJointBound.native_risk_or_bad_bound length psi primitive family base
    firstSmall roundSmall nodesEnough hs basis dummy enough capacity radius hadSmall (fun _ => radius) epsilon
    encoding small calibrated
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) bound
  intro outcome supported event
  rcases event with event | bad
  · rcases event with had | wrong
    · exact Or.inl (Or.inl had)
    · have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      rcases wrong_transform_coverage length psi primitive family base ns dummy capacity radius _
          ⟨initial.1,fun _ => initial.2.2⟩ encoding domain tags outcome supported wrong with risk | bad
      · exact Or.inl (Or.inr risk)
      · exact Or.inr bad
  · exact Or.inr bad

/-- The same original-function event composes inside an arbitrary audited PBS
execution, leaving the one final collision charge to that enclosing caller. -/
theorem native_safe_original_relation_bound [NeZero m] [NeZero b]
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
    (radius : ℕ)
    (hadSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (domain : ∀ slot incoming, hs.domain = (base slot incoming).domain)
    (tags : ∀ slot incoming, (base slot incoming).tag true = hs.tag (PackedPBSOriginalReferences.evaluationFactor slot))
    (small : ∀ slot incoming, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) radius ≤ epsilon slot)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) dummy
      initial)}[
      (OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs))
        dummy capacity radius outcome.1 ∨
      WrongTransform length psi base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs) dummy capacity radius outcome) ∧
      ¬(match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)] ≤
      (PackedPBSHadamardNTTJointBound.rate (K := K) hs radius + ((List.finRange (count+1)).map epsilon).sum) := by
  let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough hs
  have bound := PackedPBSHadamardNTTJointBound.native_safe_risk_bound length psi primitive family base
    firstSmall roundSmall nodesEnough hs basis dummy enough capacity radius hadSmall (fun _ => radius) epsilon
    encoding small calibrated initial audited
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) bound
  intro outcome supported event
  obtain ⟨event,safe⟩ := event
  refine ⟨?_,safe⟩
  rcases event with had | wrong
  · exact Or.inl had
  · rcases wrong_transform_coverage length psi primitive family base ns dummy capacity radius initial audited
        encoding domain tags outcome supported wrong with risk | bad
    · exact Or.inr risk
    · exact False.elim (safe bad)

end
end FormalProof4FHE.HasteBoots.PackedPBSLoopFunctionBound
