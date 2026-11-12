module
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
public import FormalProof4FHE.HasteBoots.PackedPBSFirstComparisonSoundness
@[expose] public section

/-! One derived bound covers original Hadamard/NTT/first-reconstruction risks,
accepted false first-comparison tuples and the same whole-prefix exception. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSFirstHalfJointBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open NativeRootMessage (Digest)
open PackedPBSFirstComparisons (priorState finalState)
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
open FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → P)]
  [SampleableType (Fin n → ZMod q)] [SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]

variable {K LookupMessage LookupMemory LookupResponse HelperMemory : Type}
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K] [SampleableType K]
  {e padding helperPadding lookupC lookupRow requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC lookupRow (2*d+1) (∑ i, repetitions i)}
  {L : Root (2*d+1) (∑ i, repetitions i) → Type}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (lookupC+lookupRow) → K)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra (ZMod q) (L root)]
  [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → L root)]

/-- Derived native first-half arithmetic risks outside its final exception.
This form composes with later stages without paying an intermediate charge. -/
theorem native_safe_joint_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
  (hadNodes : 2*b ≤ (2*b-1)*2+1)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

    (nativeBasis : Module.Basis (Fin b) (ZMod q) P) (dummy : Digest)
    (nativeEnough : m ≤ Fintype.card (Fin (2^height))) (nativeCapacity : 2^suffix ≤ m*b) (nativeRadius : ℕ)
    (nttEpsilon : Fin (2*d+1) → ENNReal) (linearEpsilon : ENNReal)
    (nttEncoding : ∀ slot memory, (base slot memory).encoding = hs.encoding)
    (linearEncoding : ∀ memory, (linearBase memory).encoding = hs.encoding)
    (hadSmall : (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) hs.domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (nttSmall : ∀ slot memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (base slot memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (linearSmall : ∀ memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (linearBase memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ slot memory, HadamardNTTProbability.rate (K := P) (base slot memory) nativeRadius ≤ nttEpsilon slot)
    (linearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := P) (m := m) (b := b) (queries := queries)
        (linearBase memory).domain nativeRadius ≤ linearEpsilon)
    [∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e+padding) (e+helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e + padding) (e + helperPadding) root)) (ZMod q) (L root))
    (config : MixedWidthRequestSharedLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ (ZMod q))
    (lookupEnough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (lookupCapacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (e + padding) (e + helperPadding) root) (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) K LookupMemory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse LookupMemory (packedWidth (e + padding) (e + helperPadding)) heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (lookupRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)) :
    let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
    let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy comparator
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius outcome.1 ∨
        ∃ compared, outcome.2 = some compared ∧
          MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
            compared.2.2.1.2.accepted = true) ∧
      ¬CheckpointCollision.Bad _ (finalState comparator outcome)] ≤
      (((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      (error K mode (lookupC+lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain lookupRadius))) := by
  dsimp only
  let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
  let s := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have incoming : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :=
    ⟨initial.1,fun _ => initial.2.2⟩
  have earlier := PackedPBSReconstructionJointBound.native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
    hadSmall nttSmall linearSmall nttCalibrated linearCalibrated _ incoming
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => Skeleton.perfect (heights cfg))
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag entry member
    cases member
  have compatible := fun prior supported => PackedPBSComparisonSharedExecution.prefix_compatible length psi primitive
    family inputs base ns nodesEnough radix linearBase dummy (fun cfg => Skeleton.perfect (heights cfg))
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted prior supported
  have comparison := PackedPBSFirstComparisonSoundness.original_false_comparison_bound length psi primitive family inputs base ns nodesEnough radix linearBase
    analysisBasis dummy config p small domain lookupEnough lookupCapacity lookupRadius fallback behavior pairEnough lookupSmall build distance
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) incoming compatible
  dsimp only at comparison
  exact PackedPBSComparisonJointBound.safe_joint_bound length psi primitive family inputs base ns nodesEnough radix linearBase dummy s
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))
    (fun prior => PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior)
    (fun compared => MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
      compared.2.2.1.2.accepted = true) _ _ earlier comparison

/-- The native typed-message prefix and concrete request comparisons pay
all arithmetic rates and a single charge over their actual shared execution. -/
theorem native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
  (hadNodes : 2*b ≤ (2*b-1)*2+1)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

    (nativeBasis : Module.Basis (Fin b) (ZMod q) P) (dummy : Digest)
    (nativeEnough : m ≤ Fintype.card (Fin (2^height))) (nativeCapacity : 2^suffix ≤ m*b) (nativeRadius : ℕ)
    (nttEpsilon : Fin (2*d+1) → ENNReal) (linearEpsilon : ENNReal)
    (nttEncoding : ∀ slot memory, (base slot memory).encoding = hs.encoding)
    (linearEncoding : ∀ memory, (linearBase memory).encoding = hs.encoding)
    (hadSmall : (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) hs.domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (nttSmall : ∀ slot memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (base slot memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (linearSmall : ∀ memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (linearBase memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ slot memory, HadamardNTTProbability.rate (K := P) (base slot memory) nativeRadius ≤ nttEpsilon slot)
    (linearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := P) (m := m) (b := b) (queries := queries)
        (linearBase memory).domain nativeRadius ≤ linearEpsilon)
    [∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e+padding) (e+helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e + padding) (e + helperPadding) root)) (ZMod q) (L root))
    (config : MixedWidthRequestSharedLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ (ZMod q))
    (lookupEnough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (lookupCapacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (e + padding) (e + helperPadding) root) (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) K LookupMemory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse LookupMemory (packedWidth (e + padding) (e + helperPadding)) heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (lookupRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)) :
    let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
    let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy comparator
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius outcome.1 ∨
        ∃ compared, outcome.2 = some compared ∧
          MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
            compared.2.2.1.2.accepted = true) ∨
      CheckpointCollision.Bad _ (finalState comparator outcome)] ≤
      (((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      (error K mode (lookupC+lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain lookupRadius))) +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (PackedPBSFirstComparisons.program length psi primitive family inputs base ns nodesEnough radix linearBase comparator)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
  let s := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  refine PackedPBSComparisonSharedExecution.risk_or_bad_bound length psi primitive family inputs base ns nodesEnough radix linearBase dummy s restricted
    (fun outcome => PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius outcome.1 ∨
      ∃ compared, outcome.2 = some compared ∧
        MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
          compared.2.2.1.2.accepted = true) _ ?_
  exact native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
    hadSmall nttSmall linearSmall nttCalibrated linearCalibrated analysisBasis config p small domain lookupEnough lookupCapacity lookupRadius
    fallback behavior pairEnough lookupSmall build distance restricted

end
end FormalProof4FHE.HasteBoots.PackedPBSFirstHalfJointBound
