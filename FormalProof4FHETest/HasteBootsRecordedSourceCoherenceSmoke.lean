module
import FormalProof4FHE.HasteBoots.RecordedSourceCoherence
import FormalProof4FHE.HasteBoots.RecordedPayloadCoherence
import FormalProof4FHE.HasteBoots.ReusedPrivateSource
import Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
namespace HasteBootsRecordedSourceCoherenceSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev Input := Sum (List (ZMod 17)) (Fin 2 × Fin 2)
def encoding : MerkleOracle.Encoding Input (Fin 2) (List (ZMod 17)) where
  leaf _ := Sum.inl
  node _ := Sum.inr
  leaf_injective _ := Sum.inl_injective
  node_injective _ := Sum.inr_injective

def shape := RecordedSourceCoherence.Shape Unit 0
def initial : CheckpointExecution.State (Input := Input) (Digest := Fin 2) shape := CheckpointExecution.empty shape
def ownerState := CheckpointExecution.record shape initial () 0
def query : Input := .inl [9]
def nextHash := CachedHashHandler.observe ownerState.hash query 1 (ownerState.hash.cache.cacheQuery query 1)
def afterHash := CheckpointExecution.afterHash encoding 0 shape ownerState nextHash
def finalState := CheckpointExecution.record shape afterHash () 0

def original : RecordedSourceCoherence.Snapshot Input (Fin 2) Unit 0 () := ⟨0,[]⟩
def reused : RecordedSourceCoherence.Snapshot Input (Fin 2) Unit 0 () := ⟨0,[⟨query,1⟩]⟩

theorem owner_stable : MerklePayloadCheckpoints.StableAt encoding 0 shape ownerState.checkpoints [] :=
  MerklePayloadCheckpoints.stable_record encoding 0 shape _ []
    (MerklePayloadCheckpoints.stable_empty encoding 0 shape []) () 0

theorem outside : (1 : Fin 2) ∉ ownerState.checkpoints.liveTargetSet (MerkleOracle.model encoding 0).view [] := by decide +kernel

theorem continued_stable : MerklePayloadCheckpoints.StableAt encoding 0 shape ownerState.checkpoints [⟨query,1⟩] :=
  MerklePayloadCheckpoints.stable_append_outside_live encoding 0 shape ownerState.checkpoints [] owner_stable query 1 outside

theorem final_stable : MerklePayloadCheckpoints.StableAt encoding 0 shape finalState.checkpoints finalState.hash.log :=
  MerklePayloadCheckpoints.stable_record encoding 0 shape ownerState.checkpoints [⟨query,1⟩] continued_stable () 0

theorem original_recorded : ⟨(),original⟩ ∈ finalState.checkpoints.checkpoints := by
  change (⟨(),original⟩ : (tag : Unit) ×' RecordedSourceCoherence.Snapshot Input (Fin 2) Unit 0 tag) ∈ [⟨(),original⟩,⟨(),reused⟩]
  exact List.mem_cons_self
theorem reused_recorded : ⟨(),reused⟩ ∈ finalState.checkpoints.checkpoints := by
  change (⟨(),reused⟩ : (tag : Unit) ×' RecordedSourceCoherence.Snapshot Input (Fin 2) Unit 0 tag) ∈ [⟨(),original⟩,⟨(),reused⟩]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
example : original.cumulativeLog ≠ reused.cumulativeLog := by decide +kernel
example : finalState.checkpoints.checkpoints.length = 2 := by decide +kernel
example : finalState.hash.log = [⟨query,1⟩] := rfl

-- Same original context/root, different cumulative logs, complete words.
example : InteractiveAuthenticatedOpening.word (leftCount := 1) (b := 1) encoding 0 (fun _ : Unit => 0) () original =
    InteractiveAuthenticatedOpening.word (leftCount := 1) (b := 1) encoding 0 (fun _ : Unit => 0) () reused :=
  RecordedSourceCoherence.word_eq_of_stable (front := 0) (b := 1) encoding 0 finalState final_stable () original reused
    original_recorded reused_recorded rfl

def domain : Fin 1 ↪ ZMod 17 := ⟨fun _ => 0,by decide +kernel⟩
theorem capacity : 2^0 ≤ 1*1 := by decide +kernel
example : RecordedSourceCoherence.source (front := 0) encoding 0 domain capacity 0 () original =
    RecordedSourceCoherence.source (front := 0) encoding 0 domain capacity 0 () reused :=
  RecordedSourceCoherence.source_eq_of_stable (front := 0) (suffix := 0) (b := 1) (m := 1) (height := 0) encoding 0 domain capacity 0 finalState final_stable () original reused
    original_recorded reused_recorded rfl

-- Coherence includes real cache insertion; the source monitor stays clear.
theorem coherent : CachedHashHandler.Coherent finalState.hash :=
  CachedHashHandler.coherent_fresh ownerState.hash CachedHashHandler.coherent_empty query 1 rfl
theorem clear : finalState.failed = false := by
  apply Bool.eq_false_of_not_eq_true
  intro failed
  have alternative := (CheckpointExecution.afterHash_failed_iff encoding 0 shape ownerState nextHash).mp failed
  rcases alternative with prior | unstable
  · exact Bool.false_ne_true prior
  · exact unstable continued_stable

theorem audited : CheckpointExecution.Audited encoding 0 shape finalState := ⟨coherent,fun _ => final_stable⟩
example : RecordedSourceCoherence.source (front := 0) encoding 0 domain capacity 0 () original =
    RecordedSourceCoherence.source (front := 0) encoding 0 domain capacity 0 () reused ∨ CheckpointCollision.Bad shape finalState :=
  RecordedSourceCoherence.source_eq_or_bad (front := 0) (suffix := 0) (b := 1) (m := 1) (height := 0) encoding 0 domain capacity 0 finalState audited () original reused original_recorded reused_recorded rfl
example : ¬RecordedSourceCoherence.Drift (front := 0) encoding 0 domain capacity 0 finalState := by
  intro drift
  have failed := RecordedSourceCoherence.drift_implies_failed (front := 0) (suffix := 0) (b := 1) (m := 1) (height := 0) encoding 0 domain capacity 0 finalState audited drift
  exact Bool.false_ne_true (clear.symm.trans failed)
-- One shared state can contain different tree shapes under different contexts.
def shapes (tag : Bool) : Skeleton := .perfect (if tag then 1 else 0)
def mixed : CheckpointExecution.State (Input := Input) (Digest := Fin 2) shapes :=
  RecordRoots.state shapes [(false,0),(true,0)] (CheckpointExecution.empty shapes)
theorem mixed_stable : MerklePayloadCheckpoints.StableAt encoding 0 shapes mixed.checkpoints mixed.hash.log :=
  MerklePayloadCheckpoints.stable_record encoding 0 shapes _ []
    (MerklePayloadCheckpoints.stable_record encoding 0 shapes _ []
      (MerklePayloadCheckpoints.stable_empty encoding 0 shapes []) false 0) true 0
example : mixed.checkpoints.checkpoints.length = 2 := by decide +kernel
example : ¬RecordedPayloadCoherence.Drift encoding 0 shapes mixed := by
  intro drift
  have auditedMixed : CheckpointExecution.Audited encoding 0 shapes mixed :=
    ⟨CachedHashHandler.coherent_empty,fun _ => mixed_stable⟩
  have failed := RecordedPayloadCoherence.drift_implies_failed encoding 0 shapes mixed auditedMixed drift
  exact Bool.false_ne_true failed
end
end HasteBootsRecordedSourceCoherenceSmoke
