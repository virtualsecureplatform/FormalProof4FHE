module
import FormalProof4FHE.HasteBoots.OwnedPrivateLookupSoundness
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp BinaryTree
namespace HasteBootsStagedLookupExceptionSmoke
noncomputable section
namespace RecordingTimes
abbrev Shared := SharedSequence.Shared Bool (Fin 4) (Fin 2)
inductive Event where
  | hash : Fin 4 → Event
  | coin : ℕ → Event
  | record : Bool → Fin 2 → Event
  deriving DecidableEq

def handler : QueryImpl Shared (StateM (List Event)) := fun query => match query with
  | .inl size => do
      modify (· ++ [.coin size])
      pure (⟨0,Nat.zero_lt_succ size⟩ : Fin (size+1))
  | .inr (.inl input) => do
      modify (· ++ [.hash input])
      pure (⟨input.val%2,Nat.mod_lt _ (by decide +kernel)⟩ : Fin 2)
  | .inr (.inr (tag,root)) => do
      modify (· ++ [.record tag root])
      pure ()

def hash (input : Fin 4) : OracleComp Shared (Fin 2) := liftM (Shared.query (.inr (.inl input)))
def sourceCommit : OracleComp Shared ((Unit → Fin 2) × ℕ) := do
  let _ ← hash 0
  pure (fun _ => 0,7)
def helperCommit (first : (Unit → Fin 2) × ℕ) : OracleComp Shared ((Unit → Fin 2) × ℕ) := do
  let _ ← Shared.query (.inl 1)
  let _ ← hash 1
  pure (fun _ => 1,first.2+5)
def next (_first _second : (Unit → Fin 2) × ℕ) : OracleComp Shared Bool := do
  let _ ← hash 2
  pure false

def program := StagedCommitmentPrefix.program
  (fun first : (Unit → Fin 2) × ℕ => [(false,first.1 ())])
  (fun _ second : (Unit → Fin 2) × ℕ => [(true,second.1 ())]) sourceCommit helperCommit next

-- Source recording is before both the middle private draw and helper hash;
-- helper recording is after them. Rejection retains the final hash call.
example : (simulateQ handler program).run [] =
    (((fun _ : Unit => (0 : Fin 2),7),(fun _ : Unit => (1 : Fin 2),12),false),
      [.hash 0,.record false 0,.coin 1,.hash 1,.record true 1,.hash 2]) := rfl
end RecordingTimes

namespace CommonException
local instance : SampleableType Unit := SampleableType.ofFintype _
def encoding : MerkleOracle.Encoding (Fin 4) Unit Unit where
  leaf _ _ := 2
  node _ _ := 3
  leaf_injective _ := by intro first last _; cases first; cases last; rfl
  node_injective _ := by intro first last _; cases first with | mk firstA firstB => cases last with | mk lastA lastB => cases firstA; cases firstB; cases lastA; cases lastB; rfl

def shape (_ : Unit) : Skeleton := .perfect 0
def initial : CheckpointExecution.State (Input := Fin 4) (Digest := Unit) shape := CheckpointExecution.empty shape
def firstHash := CachedHashHandler.observe initial.hash 0 () (initial.hash.cache.cacheQuery 0 ())
def first := CheckpointExecution.afterHash encoding () shape initial firstHash
def secondHash := CachedHashHandler.observe first.hash 1 () (first.hash.cache.cacheQuery 1 ())
def finalState := CheckpointExecution.afterHash encoding () shape first secondHash

theorem collision : CacheHasCollision finalState.hash.cache := ⟨0,1,(),(),by decide +kernel,rfl,rfl,HEq.rfl⟩
example : CheckpointCollision.Bad shape finalState := Or.inr collision
example : ¬CheckpointAvailability.Disagreement encoding () shape finalState := by
  rintro ⟨tag,checkpoint,recorded,_⟩
  exact List.not_mem_nil recorded

abbrev Shared := SharedSequence.Shared Unit (Fin 4) Unit
def hash (input : Fin 4) : OracleComp Shared Unit := liftM (Shared.query (.inr (.inl input)))
def sourceCommit : OracleComp Shared Unit := hash 0
def helperCommit (_ : Unit) : OracleComp Shared Unit := hash 1
def next (_ _ : Unit) : OracleComp Shared Bool := pure false

-- A collision spanning the two prefixes remains in the terminal event even
-- when acceptance is always false and no root has an availability disagreement.
example : Pr{let outcome ← (StagedCommitmentPrefix.witness encoding () shape (fun _ : Unit => [])
    (fun _ _ : Unit => []) sourceCommit helperCommit next initial)}[
      CheckpointCollision.Bad shape outcome.2.2.2] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding () shape)
      (CheckpointCollision.loss unifSpec shape)
      (StagedCommitmentPrefix.program (fun _ : Unit => []) (fun _ _ : Unit => []) sourceCommit helperCommit next) initial := by
  have bound := StagedCommitmentException.event_bound_or_bad encoding () shape (fun _ : Unit => []) (fun _ _ : Unit => [])
    sourceCommit helperCommit next (fun _ _ _ => False) (fun _ _ _ => False) 0
    (by intro first second; simp [prEvent_norm])
    (by intro first firstSupported second secondSupported last lastSupported impossible; exact False.elim impossible)
  simpa only [initial,false_or,zero_add] using bound
end CommonException
end
end HasteBootsStagedLookupExceptionSmoke
