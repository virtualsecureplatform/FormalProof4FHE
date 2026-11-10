module
import FormalProof4FHE.HasteBoots.OwnedExtractionSoundness
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp BinaryTree
namespace HasteBootsExceptionUnionSmoke
noncomputable section
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

theorem coherent : CachedHashHandler.Coherent finalState.hash :=
  CachedHashHandler.coherent_fresh first.hash
    (CachedHashHandler.coherent_fresh initial.hash CachedHashHandler.coherent_empty 0 () rfl) 1 () rfl

theorem collision : CacheHasCollision finalState.hash.cache :=
  ⟨0,1,(),(),by decide +kernel,rfl,rfl,HEq.rfl⟩
example : CheckpointCollision.Bad shape finalState := Or.inr collision
example : finalState.checkpoints.checkpoints = [] := rfl
example : ¬CheckpointAvailability.Disagreement encoding () shape finalState := by
  rintro ⟨tag,checkpoint,recorded,_⟩
  exact List.not_mem_nil recorded
example : finalState.hash.log.length = 2 := by decide +kernel

abbrev Shared := SharedSequence.Shared Unit (Fin 4) Unit
def hash (input : Fin 4) : OracleComp Shared Unit := liftM (Shared.query (.inr (.inl input)))
def later (_ : Unit) : OracleComp Shared Bool := do
  let _ ← hash 0
  let _ ← hash 1
  pure false

-- Even with an always-false acceptance predicate and no recorded roots, the
-- terminal cache-collision event belongs to the bound and pays one charge.
example : Pr{let outcome ← (MultiCommitmentPrefix.witness encoding () shape (fun _ : Unit => []) (pure ()) later initial)}[
    CheckpointCollision.Bad shape outcome.2.2] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding () shape)
      (CheckpointCollision.loss unifSpec shape) (MultiCommitmentPrefix.program (fun _ : Unit => []) (pure ()) later) initial := by
  have bound := CommitmentExceptionUnion.event_bound_or_bad encoding () shape (fun _ : Unit => []) (pure ()) later
    (fun _ _ => False) (fun _ _ => False) 0
    (by intro first; simp [prEvent_norm])
    (by intro first last supported impossible; exact False.elim impossible)
  simpa only [initial,false_or,zero_add] using bound
end
end HasteBootsExceptionUnionSmoke
