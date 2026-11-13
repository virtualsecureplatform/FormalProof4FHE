module
public import FormalProof4FHE.HasteBoots.TransportedOriginalNTTSource
public import FormalProof4FHE.HasteBoots.TransportedOriginalHadamardSource
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Original retained NTT sources keep their decoder/root/log through the
actual geometry transition and agree with other actual recorded families only
under complete public metadata/root association and one final history. -/
namespace FormalProof4FHE.HasteBoots.TransportedOriginalNTTBinding
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
noncomputable section
attribute [local irreducible] MonadAttach.support
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

variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (first : HadamardOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n) (count := count)
    (front := front) (queries := queries) (height := height))
  (later : LoopOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (count := count)
    (front := front) (queries := queries) (height := height))
  (supported : (first,some later) ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial))


variable
    (entry : Fin (count+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ later.1.results)

variable (heights : Cfg → ℕ)

include supported member in
/-- Actual original NTT evaluations and copied original Hadamard factors agree
under complete public metadata association in the same later audited state. -/
theorem evaluation_source_eq_or_bad (capacity : 2^suffix ≤ m*b)
    (radius : Fin (count+1) → ℕ) (hadamardRadius : ℕ)
    (nttGeometry : ∀ side, heights ((base entry.1 entry.2.1).tag side) = height)
    (hadamardGeometry : ∀ factor, heights (hs.tag factor) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : TransportedOriginalNTTSource.parameters base entry heights capacity (radius entry.1) nttGeometry true =
      TransportedOriginalHadamardSource.parameters hs heights capacity hadamardRadius hadamardGeometry
        (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights) later.2) state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape heights) state) :
    AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2.1 true =
      RecordedPaddedSourceFamily.logical
        (TransportedOriginalHadamardSource.sources hs first heights capacity hadamardRadius hadamardGeometry)
        hs.encoding dummy (r+c) (PackedPBSOriginalReferences.evaluationFactor entry.1) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have roots := (TransportedOriginalHadamardSource.evaluation_root length psi primitive family base hs dummy initial first later supported
    heights capacity hadamardRadius hadamardGeometry entry.1).symm
  exact TransportedOriginalNTTSource.source_agrees_or_bad length psi primitive family base hs dummy initial first later supported
    entry member heights capacity (radius entry.1) nttGeometry encoding
    (TransportedOriginalHadamardSource.sources hs first heights capacity hadamardRadius hadamardGeometry)
    (PackedPBSOriginalReferences.evaluationFactor entry.1) true associated roots state retained audited
    (TransportedOriginalHadamardSource.recorded length psi primitive family base hs dummy initial first later supported
      heights capacity hadamardRadius hadamardGeometry state retained)

include supported member in
/-- Every retained original coefficient row transforms into its original
Hadamard factor, or the existing loop OriginalRisk or same later Bad occurs.
The true transform relation is derived from actual native acceptance. -/
theorem transforms_or_risks (capacity : 2^suffix ≤ m*b)
    (radius : Fin (count+1) → ℕ) (hadamardRadius : ℕ)
    (nttGeometry : ∀ side, heights ((base entry.1 entry.2.1).tag side) = height)
    (hadamardGeometry : ∀ factor, heights (hs.tag factor) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : TransportedOriginalNTTSource.parameters base entry heights capacity (radius entry.1) nttGeometry true =
      TransportedOriginalHadamardSource.parameters hs heights capacity hadamardRadius hadamardGeometry
        (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights) later.2) state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (accepted : later.1.accepted = true) :
    (∀ row, BlindRotationNTT.transform log psi
      (PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2.1 false) row) =
      (fun coefficient => RecordedPaddedSourceFamily.logical
        (TransportedOriginalHadamardSource.sources hs first heights capacity hadamardRadius hadamardGeometry)
        hs.encoding dummy (n+1) (PackedPBSOriginalReferences.evaluationFactor entry.1)
        (PackedHadamardRows.address length ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm) row coefficient).1
        (PackedHadamardRows.address length ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm) row coefficient).2)) ∨
      NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1 ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases risky : NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1
  · exact Or.inr (Or.inl risky)
  rcases evaluation_source_eq_or_bad length psi primitive family base hs dummy initial first later supported entry member heights
    capacity radius hadamardRadius nttGeometry hadamardGeometry encoding associated state retained audited with equal | bad
  · have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
    have passes := NTTSequenceHistory.accepted_children (PackedPBSNTTLoop.factory length psi primitive family base) hs.encoding dummy
      (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reached.2.2 entry member accepted
    have relation : PackedNTT.Relation length psi
        (NTTCompression.sourceRows c r (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2.1 false))
        (NTTCompression.sourceRows c r (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2.1 true)) := by
      by_contra wrong
      apply risky
      refine ⟨entry,member,CommittedJointMatrixOpening.snapshots (base entry.1 entry.2.1).tag entry.2.2.1,?_,wrong,passes⟩
      intro side
      exact ⟨rfl,PackedPBSLoopEnforcement.child_recorded length psi primitive family base hs dummy initial first later supported entry member side⟩
    left
    intro row
    have transformed := PackedNTTBinding.transform_of_relation length psi primitive _ _ relation row
    have regroup : QueryReindex.source ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm)
        (RecordedPaddedSourceFamily.logical
          (TransportedOriginalHadamardSource.sources hs first heights capacity hadamardRadius hadamardGeometry)
          hs.encoding dummy (n+1) (PackedPBSOriginalReferences.evaluationFactor entry.1)) =
        RecordedPaddedSourceFamily.logical
          (TransportedOriginalHadamardSource.sources hs first heights capacity hadamardRadius hadamardGeometry)
          hs.encoding dummy (r+c) (PackedPBSOriginalReferences.evaluationFactor entry.1) :=
      PaddedSourceAddress.logical_reindex ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm) _
    exact transformed.trans (congrArg (fun table => PackedNTTBinding.row length table row) (equal.trans regroup.symm))
  · exact Or.inr (Or.inr bad)

end
end FormalProof4FHE.HasteBoots.TransportedOriginalNTTBinding
