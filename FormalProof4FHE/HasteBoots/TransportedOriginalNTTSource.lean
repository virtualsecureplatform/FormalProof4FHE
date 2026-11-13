module
public import FormalProof4FHE.HasteBoots.PackedPBSLoopEnforcement
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Original retained NTT sources keep their decoder/root/log through the
actual geometry transition and agree with other actual recorded families only
under complete public metadata/root association and one final history. -/
namespace FormalProof4FHE.HasteBoots.TransportedOriginalNTTSource
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

/-- Copy the actual retained source owner; no new root or word is sampled. -/
def owner (side : Bool) :=
  CheckpointShapeTransport.checkpoint (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)
    ((base entry.1 entry.2.1).tag side)
    (CommittedJointMatrixOpening.snapshots (base entry.1 entry.2.1).tag entry.2.2.1 side)

/-- Complete physical decoder metadata of this actual retained child. -/
def parameters (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ side, heights ((base entry.1 entry.2.1).tag side) = height) (side : Bool) :=
  AmbientSourceDescriptor.parameters (front := front) heights ((base entry.1 entry.2.1).tag side)
    (geometry side) (base entry.1 entry.2.1).domain capacity radius

include supported member in
/-- Both literal source owners survive in the copied loop history and every
later retained shared state, without independent availability receipts. -/
theorem owner_recorded
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights) later.2) state)
    (side : Bool) :
    ⟨(base entry.1 entry.2.1).tag side,owner base entry heights side⟩ ∈ state.checkpoints.checkpoints := by
  have original := PackedPBSLoopEnforcement.child_recorded_final length psi primitive family base hs dummy initial first later supported entry member side
  have copied := (CheckpointShapeTransport.recorded_iff (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)
    later.2.checkpoints ((base entry.1 entry.2.1).tag side)
    (CommittedJointMatrixOpening.snapshots (base entry.1 entry.2.1).tag entry.2.2.1 side)).mpr original
  exact retained _ _ copied

include supported member in
/-- Caller roots are derived from the same reached child, including the
coefficient/result slot distinction and original evaluation root. -/
theorem owner_root (side : Bool) :
    (owner base entry heights side).root =
      (if side then family.evaluations entry.1 else family.coefficients entry.1) := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial first later supported
  have roots := PackedPBSNTTLoop.retained_roots length psi primitive family base hs.encoding dummy first.2.1.2.memory first.2.2
    later reached.2.2 entry member
  exact congrFun roots side

omit [DecidableEq Input] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)] in
/-- The literal original row source and copied owner's canonical logical view
are equal. Encoding association concerns the real factory, not a replacement. -/
theorem original_logical (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ side, heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding) (side : Bool) :
    AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 side =
    RecordedPaddedSource.logical (parameters base entry heights capacity radius geometry side) hs.encoding dummy (r+c)
      (owner base entry heights side) := by
  change QueryReindex.source (base entry.1 entry.2.1).dimensions
    (RecordedSourceCoherence.source (front := front) (base entry.1 entry.2.1).encoding dummy
      (base entry.1 entry.2.1).domain capacity radius ((base entry.1 entry.2.1).tag side)
      (CommittedJointMatrixOpening.snapshots (base entry.1 entry.2.1).tag entry.2.2.1 side)) = _
  rw [encoding]
  exact AmbientSourceDescriptor.original hs.encoding dummy heights ((base entry.1 entry.2.1).tag side)
    (geometry side) (base entry.1 entry.2.1).domain capacity radius (base entry.1 entry.2.1).dimensions
    (owner base entry heights side)

variable {Index : Type}
include supported member in
/-- Complete source agreement with another recorded executed family follows
from public decoder/root association under the same final Bad exclusion. -/
theorem source_agrees_or_bad (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ side, heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (target : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights b)
    (index : Index) (side : Bool)
    (associated : parameters base entry heights capacity radius geometry side = target.parameters index)
    (roots : (if side then family.evaluations entry.1 else family.coefficients entry.1) = target.roots index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights) later.2) state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (targetRecorded : RecordedPaddedSourceFamily.Recorded target state) :
    AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 side =
      RecordedPaddedSourceFamily.logical target hs.encoding dummy (r+c) index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rw [original_logical base hs dummy entry heights capacity radius geometry encoding side]
  exact RecordedPaddedSourceFamily.associated_owner_agrees_or_bad target hs.encoding dummy (r+c) index
    (parameters base entry heights capacity radius geometry side) associated state audited targetRecorded
    (owner base entry heights side)
    (owner_recorded length psi primitive family base hs dummy initial first later supported entry member heights state retained side)
    ((owner_root length psi primitive family base hs dummy initial first later supported entry member heights side).trans roots)

include supported member in
/-- Polynomial rows retain their exact native addresses when the original
NTT source is associated with an actual recorded target family. -/
theorem row_agrees_or_bad (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ side, heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (target : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights b)
    (index : Index) (side : Bool)
    (associated : parameters base entry heights capacity radius geometry side = target.parameters index)
    (roots : (if side then family.evaluations entry.1 else family.coefficients entry.1) = target.roots index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights) later.2) state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (targetRecorded : RecordedPaddedSourceFamily.Recorded target state)
    (row : MatrixFold.Cube r) :
    PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 side) row =
      PackedNTTBinding.row length (QueryReindex.source (base entry.1 entry.2.1).dimensions
        (RecordedPaddedSourceFamily.logical target hs.encoding dummy (front+suffix) index)) row ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rcases source_agrees_or_bad length psi primitive family base hs dummy initial first later supported entry member heights
      capacity radius geometry encoding target index side associated roots state retained audited targetRecorded with same | bad
  · left
    have regroup : QueryReindex.source (base entry.1 entry.2.1).dimensions
        (RecordedPaddedSourceFamily.logical target hs.encoding dummy (front+suffix) index) =
        RecordedPaddedSourceFamily.logical target hs.encoding dummy (r+c) index :=
      PaddedSourceAddress.logical_reindex (base entry.1 entry.2.1).dimensions
        (RecordedPaddedSource.decoded (target.parameters index) hs.encoding dummy (target.owners index))
    exact congrArg (fun table => PackedNTTBinding.row length table row) (same.trans regroup.symm)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.TransportedOriginalNTTSource
