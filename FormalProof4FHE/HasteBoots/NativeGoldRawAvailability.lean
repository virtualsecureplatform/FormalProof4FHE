module

public import FormalProof4FHE.HasteBoots.NativeGoldRawRequests

@[expose] public section

/-! Freeze original raw Rows first, then interpret their coordinates in the
field. Hash inputs never serialize a projected field list. Semantic transport
failure is charged to the existing joint root-wide availability event. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldRawAvailability

open NativeGoldRawRequests (Request)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row)
open NativeFieldRepresentation (GoldWord)
open NativeFields (Goldilocks)
open NativeBrakedownParameters (Geometry)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def emptyRow : Row := ⟨[],by decide⟩

noncomputable section
open scoped BigOperators

def frozenRaw {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (position : Fin (2^(height tag))) : Row :=
  MerkleAvailability.word encoding dummy emptyRow (height tag) checkpoint.cumulativeLog checkpoint.root position

/-- Query-independent projection of the immutable raw prefix word. Missing
coordinates, including the empty raw fallback, have field value zero. -/
def frozenValue {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (position : Fin (2^(height tag))) (coordinate : ℕ) : Goldilocks :=
  NativeGoldColumnChecks.view (frozenRaw dummy height tag checkpoint position).val coordinate

def frozenWord {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (coordinates : ℕ) : Fin (2^(height tag)) → Fin coordinates → Goldilocks :=
  fun position coordinate => frozenValue dummy height tag checkpoint position coordinate.val

theorem empty_view (coordinate : ℕ) : NativeGoldColumnChecks.view emptyRow.val coordinate = 0 := by
  simp only [NativeGoldColumnChecks.view,emptyRow,List.getElem?_nil,Option.getD_none,
    NativeFieldRepresentation.goldValue,Fin.val_zero,Nat.cast_zero]

theorem payload_of_no_failure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ)
    (requests : List (Request height)) (request : Request height) (member : request ∈ requests)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (replayed : ParallelColumnAvailability.Replays encoding height request state.hash.cache)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag)
    (recorded : ⟨request.tag,checkpoint⟩ ∈ state.checkpoints.checkpoints) (root : checkpoint.root = request.root)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height requests state) :
    request.payload = frozenRaw dummy height request.tag checkpoint request.position := by
  by_contra different
  exact noFailure (ParallelColumnAvailability.failure_of_word_disagreement encoding dummy height requests state
    request member replayed checkpoint recorded root emptyRow (Ne.symm different))

theorem values_of_no_failure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ)
    (requests : List (Request height)) (request : Request height) (member : request ∈ requests)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (replayed : ParallelColumnAvailability.Replays encoding height request state.hash.cache)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag)
    (recorded : ⟨request.tag,checkpoint⟩ ∈ state.checkpoints.checkpoints) (root : checkpoint.root = request.root)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height requests state) :
    (fun coordinate => NativeGoldColumnChecks.view request.payload.val coordinate) =
      frozenValue dummy height request.tag checkpoint request.position := by
  rw [payload_of_no_failure dummy height requests request member state replayed checkpoint recorded root noFailure]
  rfl

def Equations (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (values : ℕ → Goldilocks) (index : ℕ) : Prop :=
  ∀ lane < width, ∀ component < geometry.blockWidth,
    (∑ row : Fin geometry.rows, NativeGoldColumnChecks.view random (lane*geometry.rows+row.val)*values (row.val*geometry.blockWidth+component)) =
      NativeGoldColumnChecks.view test (lane*geometry.stride+index*geometry.blockWidth+component) ∧
    (∑ row : Fin geometry.rows, NativeGoldColumnChecks.view structured (lane*geometry.rows+row.val)*values (row.val*geometry.blockWidth+component)) =
      NativeGoldColumnChecks.view evaluation (lane*geometry.stride+index*geometry.blockWidth+component)

theorem equations_of_no_failure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ)
    (requests : List (Request height)) (request : Request height) (member : request ∈ requests)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (replayed : ParallelColumnAvailability.Replays encoding height request state.hash.cache)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag)
    (recorded : ⟨request.tag,checkpoint⟩ ∈ state.checkpoints.checkpoints) (root : checkpoint.root = request.root)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height requests state)
    (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (checked : NativeGoldColumnChecks.check geometry width random structured test evaluation request.payload.val request.position.val = true) :
    Equations geometry width random structured test evaluation
      (frozenValue dummy height request.tag checkpoint request.position) request.position.val := by
  have same := payload_of_no_failure dummy height requests request member state replayed checkpoint recorded root noFailure
  rw [same] at checked
  exact (NativeGoldColumnChecks.check_iff _ _ _ _ _ _ _ _).mp checked

structure View {Cfg : Type} (height : Cfg → ℕ) where
  geometry : Geometry
  width : ℕ
  random : List GoldWord
  structured : List GoldWord
  test : List GoldWord
  evaluation : List GoldWord
  requests : List (Request height)

/-- Both native raw coordinate checks pass, but their fixed-prefix semantic
interpretation fails for one matching recorded root. -/
def Failure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (view : View height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag))) : Prop :=
  ∃ request ∈ view.requests, ParallelColumnAvailability.Replays encoding height request state.hash.cache ∧
    ∃ checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag,
      ⟨request.tag,checkpoint⟩ ∈ state.checkpoints.checkpoints ∧ checkpoint.root = request.root ∧
      NativeGoldColumnChecks.check view.geometry view.width view.random view.structured view.test view.evaluation request.payload.val request.position.val = true ∧
      ¬Equations view.geometry view.width view.random view.structured view.test view.evaluation
        (frozenValue dummy height request.tag checkpoint request.position) request.position.val

theorem failure_implies_availability {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (view : View height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (failure : Failure dummy height view state) :
    ParallelColumnAvailability.Failure encoding dummy height view.requests state := by
  obtain ⟨request,member,replayed,checkpoint,recorded,root,checked,different⟩ := failure
  by_contra noFailure
  exact different (equations_of_no_failure dummy height view.requests request member state replayed checkpoint recorded root noFailure
    view.geometry view.width view.random view.structured view.test view.evaluation checked)

section Runtime
variable {Cfg : Type} [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

/-- All columns and both families share the existing root-wide hash charge;
projection introduces no additional per-worker/lane/coordinate union loss. -/
theorem failure_le_charge (implBase : QueryImpl base ProbComp) (dummy : Digest) (height : Cfg → ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (View height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe encoding dummy (fun tag => Skeleton.perfect (height tag)) state) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag))) program).run state}[
      Failure dummy height result.1 result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program state := by
  apply le_trans (prEvent_mono _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge implBase encoding dummy (fun tag => Skeleton.perfect (height tag)) program state safe)
  intro result failure
  exact ParallelColumnAvailability.failure_implies_disagreement encoding dummy height _ result.2
    (failure_implies_availability dummy height result.1 result.2 failure)

theorem failure_from_empty_le_charge (implBase : QueryImpl base ProbComp) (dummy : Digest) (height : Cfg → ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (View height)) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag))) program).run (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))}[
      Failure dummy height result.1 result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) :=
  failure_le_charge implBase dummy height program _ (CheckpointCollision.safe_empty encoding dummy (fun tag => Skeleton.perfect (height tag)))

end Runtime
end
end FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
