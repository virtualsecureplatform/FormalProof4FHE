module
import FormalProof4FHE.HasteBoots.HeterogeneousSourceCoherence
import Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
namespace HasteBootsHeterogeneousSourceCoherenceSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev Input := Sum (List (ZMod 17)) (Fin 4 × Fin 4)
def encoding : MerkleOracle.Encoding Input (Fin 4) (List (ZMod 17)) where
  leaf _ := Sum.inl
  node _ := Sum.inr
  leaf_injective _ := Sum.inl_injective
  node_injective _ := Sum.inr_injective

def heights (tag : Bool) : ℕ := if tag then 1 else 0
def shape (tag : Bool) : Skeleton := .perfect (heights tag)
def initial : CheckpointExecution.State (Input := Input) (Digest := Fin 4) shape := CheckpointExecution.empty shape
-- Both contexts alias the same digest, with distinct tree heights and layouts.
def sourceState := CheckpointExecution.record shape initial false 0
def ownerState := CheckpointExecution.record shape sourceState true 0
def query : Input := .inl [9]
def nextHash := CachedHashHandler.observe ownerState.hash query 3 (ownerState.hash.cache.cacheQuery query 3)
def afterHash := CheckpointExecution.afterHash encoding 0 shape ownerState nextHash
def sourceReused := CheckpointExecution.record shape afterHash false 0
def finalState := CheckpointExecution.record shape sourceReused true 0

def originalSource : HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights false := ⟨0,[]⟩
def reusedSource : HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights false := ⟨0,[⟨query,3⟩]⟩
def originalHelper : HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights true := ⟨0,[]⟩
def reusedHelper : HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights true := ⟨0,[⟨query,3⟩]⟩

theorem owner_stable : MerklePayloadCheckpoints.StableAt encoding 0 shape ownerState.checkpoints [] :=
  MerklePayloadCheckpoints.stable_record encoding 0 shape _ []
    (MerklePayloadCheckpoints.stable_record encoding 0 shape _ []
      (MerklePayloadCheckpoints.stable_empty encoding 0 shape []) false 0) true 0

theorem outside : (3 : Fin 4) ∉ ownerState.checkpoints.liveTargetSet (MerkleOracle.model encoding 0).view [] := by
  decide +kernel

theorem continued_stable : MerklePayloadCheckpoints.StableAt encoding 0 shape ownerState.checkpoints [⟨query,3⟩] :=
  MerklePayloadCheckpoints.stable_append_outside_live encoding 0 shape ownerState.checkpoints [] owner_stable query 3 outside

theorem final_stable : MerklePayloadCheckpoints.StableAt encoding 0 shape finalState.checkpoints finalState.hash.log :=
  MerklePayloadCheckpoints.stable_record encoding 0 shape _ [⟨query,3⟩]
    (MerklePayloadCheckpoints.stable_record encoding 0 shape _ [⟨query,3⟩] continued_stable false 0) true 0

theorem source_recorded : ⟨false,originalSource⟩ ∈ finalState.checkpoints.checkpoints := by
  change (⟨false,originalSource⟩ : (tag : Bool) ×' HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights tag) ∈
    [⟨false,originalSource⟩,⟨true,originalHelper⟩,⟨false,reusedSource⟩,⟨true,reusedHelper⟩]
  exact List.mem_cons_self
theorem helper_recorded : ⟨true,originalHelper⟩ ∈ finalState.checkpoints.checkpoints := by
  change (⟨true,originalHelper⟩ : (tag : Bool) ×' HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights tag) ∈
    [⟨false,originalSource⟩,⟨true,originalHelper⟩,⟨false,reusedSource⟩,⟨true,reusedHelper⟩]
  exact List.mem_cons_of_mem _ List.mem_cons_self
theorem reused_source_recorded : ⟨false,reusedSource⟩ ∈ finalState.checkpoints.checkpoints := by
  change (⟨false,reusedSource⟩ : (tag : Bool) ×' HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights tag) ∈
    [⟨false,originalSource⟩,⟨true,originalHelper⟩,⟨false,reusedSource⟩,⟨true,reusedHelper⟩]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem reused_helper_recorded : ⟨true,reusedHelper⟩ ∈ finalState.checkpoints.checkpoints := by
  change (⟨true,reusedHelper⟩ : (tag : Bool) ×' HeterogeneousSourceCoherence.Snapshot Input (Fin 4) Bool heights tag) ∈
    [⟨false,originalSource⟩,⟨true,originalHelper⟩,⟨false,reusedSource⟩,⟨true,reusedHelper⟩]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

example : heights false = 0 ∧ heights true = 1 := by decide +kernel
example : originalSource.root = originalHelper.root := rfl
example : originalSource.cumulativeLog ≠ reusedSource.cumulativeLog := by decide +kernel
example : finalState.hash.log.length = 1 ∧ finalState.checkpoints.checkpoints.length = 4 := by decide +kernel

example : InteractiveAuthenticatedOpening.word (leftCount := 1) (b := 1) encoding 0 heights false originalSource =
    InteractiveAuthenticatedOpening.word encoding 0 heights false reusedSource :=
  HeterogeneousSourceCoherence.word_eq_of_stable (front := 0) (b := 1) encoding 0 heights finalState final_stable
    false originalSource reusedSource source_recorded reused_source_recorded rfl
example : InteractiveAuthenticatedOpening.word (leftCount := 2) (b := 2) encoding 0 heights true originalHelper =
    InteractiveAuthenticatedOpening.word encoding 0 heights true reusedHelper :=
  HeterogeneousSourceCoherence.word_eq_of_stable (front := 1) (b := 2) encoding 0 heights finalState final_stable
    true originalHelper reusedHelper helper_recorded reused_helper_recorded rfl

theorem coherent : CachedHashHandler.Coherent finalState.hash :=
  CachedHashHandler.coherent_fresh ownerState.hash CachedHashHandler.coherent_empty query 3 rfl
theorem audited : CheckpointExecution.Audited encoding 0 shape finalState := ⟨coherent,fun _ => final_stable⟩
def domain : Fin 2 ↪ ZMod 17 := ⟨fun index => (index.val : ZMod 17),by decide +kernel⟩
example : SubclaimSourceLayout.decodedSource (front := 1) domain (by decide +kernel : 2^0 ≤ 1*2) 0
    (InteractiveAuthenticatedOpening.word encoding 0 heights true originalHelper) =
    SubclaimSourceLayout.decodedSource (front := 1) domain (by decide +kernel : 2^0 ≤ 1*2) 0
      (InteractiveAuthenticatedOpening.word encoding 0 heights true reusedHelper) ∨ CheckpointCollision.Bad shape finalState :=
  HeterogeneousSourceCoherence.source_eq_or_bad (front := 1) encoding 0 heights true domain (by decide +kernel) 0 finalState audited
    originalHelper reusedHelper helper_recorded reused_helper_recorded rfl

end
end HasteBootsHeterogeneousSourceCoherenceSmoke
