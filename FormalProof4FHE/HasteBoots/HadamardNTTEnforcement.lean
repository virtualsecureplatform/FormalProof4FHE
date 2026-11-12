module
public import FormalProof4FHE.HasteBoots.HadamardNTTSourceAssociation
public import FormalProof4FHE.HasteBoots.OwnedNTTBindingCoverage
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! False polynomial transforms against original Hadamard factors are covered
by the concrete NTT original-source risk or the composed history's shared
collision event. Source association is derived from the actual reached pair. -/
namespace FormalProof4FHE.HasteBoots.HadamardNTTEnforcement
open OracleSpec OracleComp
open HadamardNTTSourceAssociation (FirstOutcome SecondOutcome)
noncomputable section
variable {q log b c r k n count front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)]
  [SampleableType (Fin b → Fin b → ZMod q)]

/-- An accepted wrong transform at ANY original row reaches one concrete NTT
risk, or the common source-association exception. No row-count union occurs. -/
theorem false_transform_coverage
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (coefficient : Digest) (expected : Fin count → Digest)
    (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (first : FirstOutcome (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height))
    (second : SecondOutcome (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : (first,some second) ∈ support (HadamardNTTComposition.witness coefficient expected publicRoots factor
      (PackedNTT.scheme length psi primitive ns) hs dummy initial))
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : hs.encoding = ns.encoding) (domain : hs.domain = ns.domain)
    (tags : ns.tag true = hs.tag factor)
    (wrong : ∃ row : MatrixFold.Cube r,
      BlindRotationNTT.transform log psi
        (PackedNTTBinding.row length (AuthenticatedNTT.sources ns dummy capacity radius second.1 false) row) ≠
      PackedNTTBinding.row length (QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
        (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1 factor)) row)
    (passes : AuthenticatedNTT.accepted second.2.1 = true) :
    OwnedNTTSoundness.OriginalRisk
      (CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor)
        (PackedNTT.scheme length psi primitive ns)) dummy capacity radius second ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2 := by
  let concrete := PackedNTT.scheme length psi primitive ns
  let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) concrete
  have supports := HadamardNTTSourceAssociation.child_supports coefficient expected publicRoots factor concrete hs
    dummy initial first second supported
  rcases HadamardNTTSourceAssociation.source_association coefficient expected publicRoots factor concrete hs
      dummy initial first second supported capacity radius audited encoding domain tags with associated | bad
  · left
    refine ⟨CommittedJointMatrixOpening.snapshots ns.tag second.1,?_,?_,passes⟩
    · intro side
      refine ⟨rfl,?_⟩
      exact SequentialStageHistory.witness_recorded hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests t.tag [false,true]) t.commit (AuthenticatedNTT.continuation t)
        first.2.2 second supports.2 (ns.tag side,second.1.1.1 side)
        (List.mem_map_of_mem (by cases side <;> simp))
    · intro holds
      have relation : PackedNTT.Relation length psi
          (NTTCompression.sourceRows c r (AuthenticatedNTT.sources ns dummy capacity radius second.1 false))
          (NTTCompression.sourceRows c r (AuthenticatedNTT.sources ns dummy capacity radius second.1 true)) := holds
      obtain ⟨row,different⟩ := wrong
      have transformed := PackedNTTBinding.transform_of_relation length psi primitive _ _ relation row
      have projected := congrArg (fun table => PackedNTTBinding.row length table row) associated
      exact different (transformed.trans projected)
  · exact Or.inr bad

/-- A false canonical-digit transform exposes concrete input/reconstruction/
comparison failures, or the actual reached NTT risk/shared collision event.
Canonical-digit correctness is derived, never an acceptance certificate. -/
theorem canonical_digit_coverage {d levels dc dw : ℕ}
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (coefficient : Digest) (expected : Fin count → Digest)
    (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (first : FirstOutcome (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
      (front := front) (queries := queries) (height := height))
    (second : SecondOutcome (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : (first,some second) ∈ support (HadamardNTTComposition.witness coefficient expected publicRoots factor
      (PackedNTT.scheme length psi primitive ns) hs dummy initial))
    (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : hs.encoding = ns.encoding) (domain : hs.domain = ns.domain)
    (tags : ns.tag true = hs.tag factor)
    (bits : ℕ) (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q)
    (enough : q-1 < (2^bits)^d) (covered : levels ≤ d)
    (registry : DecompositionBlindRotation.Registry q d dc dw)
    (address : Fin (2^log) → MatrixFold.Cube dc × Fin dw)
    (input : NativeBlindRotation.Poly q (2^log)) (level : Fin levels) (row : MatrixFold.Cube r)
    (coefficientSource : PackedNTTBinding.row length
      (AuthenticatedNTT.sources ns dummy capacity radius second.1 false) row =
      DecompositionBlindRotation.project registry address (DecompositionLinear.digit (Fin.castLE covered level)))
    (wrong : BlindRotationNTT.transform log psi (NativeBlindRotation.digit bits level input) ≠
      PackedNTTBinding.row length (QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
        (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1 factor)) row)
    (passes : AuthenticatedNTT.accepted second.2.1 = true) :
    DecompositionBlindRotation.project registry address DecompositionLinear.input ≠ input ∨
    ¬DecompositionLinear.Relation ((2^bits : ℕ) : ZMod q) registry ∨
    (∃ index, ¬RadixCanonicity.LookupAt q (2^bits) registry (address index).1 (address index).2) ∨
    OwnedNTTSoundness.OriginalRisk
      (CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor)
        (PackedNTT.scheme length psi primitive ns)) dummy capacity radius second ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2 := by
  classical
  by_cases canonical : DecompositionBlindRotation.project registry address
      (DecompositionLinear.digit (Fin.castLE covered level)) = NativeBlindRotation.digit bits level input
  · have falseTransform : ∃ selected : MatrixFold.Cube r,
        BlindRotationNTT.transform log psi
          (PackedNTTBinding.row length (AuthenticatedNTT.sources ns dummy capacity radius second.1 false) selected) ≠
        PackedNTTBinding.row length (QueryReindex.source (ns.dimensions.trans hs.dimensions.symm)
          (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1 factor)) selected := by
      refine ⟨row,?_⟩
      rw [coefficientSource,canonical]
      exact wrong
    rcases false_transform_coverage length psi primitive coefficient expected publicRoots factor ns hs dummy initial
      first second supported capacity radius audited encoding domain tags falseTransform passes with risk | bad
    · exact Or.inr (Or.inr (Or.inr (Or.inl risk)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))
  · rcases DecompositionBlindRotation.wrong_digit_coverage bits radixLarge radixSmall enough covered
      registry address input level canonical with source | linear | lookup
    · exact Or.inl source
    · exact Or.inr (Or.inl linear)
    · exact Or.inr (Or.inr (Or.inl lookup))

end
end FormalProof4FHE.HasteBoots.HadamardNTTEnforcement
