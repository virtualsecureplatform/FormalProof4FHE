module
public import FormalProof4FHE.HasteBoots.PackedPBSLoopEnforcement
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Original Hadamard sources keep their decoder/root/log through the
actual geometry transition and agree with other actual recorded families only
under complete public metadata/root association and one final history. -/
namespace FormalProof4FHE.HasteBoots.TransportedOriginalHadamardSource
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


variable (heights : Cfg → ℕ)

/-- Copy the literal original Hadamard owner, including its complete saved log. -/
def owner (factor : PBSHadamard.Factor count) :=
  CheckpointShapeTransport.checkpoint (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)
    (hs.tag factor) (CommittedJointMatrixOpening.snapshots hs.tag first.1 factor)

/-- Full public decoder metadata of the original Hadamard factor. -/
def parameters (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, heights (hs.tag factor) = height) (factor : PBSHadamard.Factor count) :=
  AmbientSourceDescriptor.parameters (front := front) heights (hs.tag factor) (geometry factor) hs.domain capacity radius

/-- One actual retained family for all original digit, key and result factors. -/
def sources (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, heights (hs.tag factor) = height) :
    RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (PBSHadamard.Factor count) heights b where
  parameters := parameters hs heights capacity radius geometry
  roots := first.1.1.1
  owners := owner hs first heights
  ownerRoots := fun _ => rfl

include supported in
/-- Every original Hadamard source survives the loop, shape transport and
later retained history. No independent availability certificate is required. -/
theorem recorded (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, heights (hs.tag factor) = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights) later.2) state) :
    RecordedPaddedSourceFamily.Recorded (sources hs first heights capacity radius geometry) state := by
  intro factor
  have original := PackedPBSLoopEnforcement.hadamard_recorded length psi primitive family base hs dummy initial first later supported factor
  have copied := (CheckpointShapeTransport.recorded_iff (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)
    later.2.checkpoints (hs.tag factor) (CommittedJointMatrixOpening.snapshots hs.tag first.1 factor)).mpr original
  exact retained _ _ copied

include supported in
/-- The evaluation factors have the original caller NTT evaluation roots. -/
theorem evaluation_root (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, heights (hs.tag factor) = height) (slot : Fin (count+1)) :
    (sources hs first heights capacity radius geometry).roots (PackedPBSOriginalReferences.evaluationFactor slot) =
      family.evaluations slot := by
  change first.1.1.1 (PackedPBSOriginalReferences.evaluationFactor slot) = _
  rw [PackedPBSHadamardNTT.hadamard_roots length psi primitive family base hs dummy initial first later supported]
  exact congrArg NativeGoldParameterStore.Reference.root (PackedPBSOriginalReferences.evaluation_reference family slot)

omit [DecidableEq Input] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)] in
/-- Decoding the copied owner preserves every original Hadamard scalar. -/
theorem original_logical (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, heights (hs.tag factor) = height) :
    AuthenticatedZeroCheck.sources hs dummy capacity radius first.1 =
      RecordedPaddedSourceFamily.logical (sources hs first heights capacity radius geometry) hs.encoding dummy (n+1) := by
  funext factor
  exact AmbientSourceDescriptor.original hs.encoding dummy heights (hs.tag factor) (geometry factor)
    hs.domain capacity radius hs.dimensions (owner hs first heights factor)

include supported in
/-- Actual accepted Hadamard constraints hold on these copied original sources,
or the existing original Hadamard risk occurs. Shape transport adds no event. -/
theorem relation_or_risk (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, heights (hs.tag factor) = height) :
    PBSHadamard.Relation (RecordedPaddedSourceFamily.logical (sources hs first heights capacity radius geometry) hs.encoding dummy (n+1)) ∨
      OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy capacity radius first := by
  classical
  by_cases risky : OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy capacity radius first
  · exact Or.inr risky
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  have truthful : PBSHadamard.Relation (AuthenticatedZeroCheck.sources hs dummy capacity radius first.1) := by
    by_contra wrong
    apply risky
    refine ⟨CommittedJointMatrixOpening.snapshots hs.tag first.1,?_,?_,reached.1⟩
    · intro factor
      exact ⟨rfl,ZeroCheckConditionalSoundness.fresh_recorded (PackedPBSHadamardNTT.hadamard family hs)
        dummy PBSHadamard.factors_complete initial first reached.2.1 factor⟩
    · exact fun vanished => wrong ((PBSHadamard.vanishes_iff _).mp vanished)
  rw [original_logical hs dummy first heights capacity radius geometry] at truthful
  exact Or.inl truthful

end
end FormalProof4FHE.HasteBoots.TransportedOriginalHadamardSource
