module
import FormalProof4FHE.HasteBoots.StagedSharedLookupSoundness
import Mathlib.Algebra.Field.ZMod
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
namespace HasteBootsSharedLookupPCSSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17
abbrev Input := Sum (List F) (Fin 2 × Fin 2)
abbrev Root := SharedLookupOpeningFamily.Root 3 2
abbrev Shared := SharedSequence.Shared Unit Input (Fin 2)
def encoding : MerkleOracle.Encoding Input (Fin 2) (List F) where
  leaf _ := Sum.inl
  node _ := Sum.inr
  leaf_injective _ := Sum.inl_injective
  node_injective _ := Sum.inr_injective

def geometry : SharedLookupOpeningFamily.Geometry 0 0 3 2 where
  front _ := 0
  suffix _ := 0
  m _ := 1
  queries _ := 1
  sourceArity _ := rfl
  helperArity _ := rfl
def heights (_ : Unit) : ℕ := 0
def tag (_ : Root) : Unit := ()
local instance : ∀ root, SampleableType (TestMatrix F (2 ^ (SharedLookupOpeningFamily.layout geometry root).front) 1) :=
  fun _ => SampleableType.ofFintype _
local instance : ∀ root, SampleableType (Fin (SharedLookupOpeningFamily.layout geometry root).queries → Fin (2 ^ heights (tag root))) :=
  fun _ => SampleableType.ofFintype _
def domain (_ : Root) : Fin (2 ^ heights ()) ↪ F := ⟨fun _ => 0,fun a b _ => Subsingleton.elim (α := Fin 1) a b⟩
def basis : Module.Basis (Fin 1) F F := Module.Basis.singleton _ _
def emission : SharedLookupPCS.Emission 3 2 (Fin 2) Unit Unit := (fun _ => 0,(fun _ => 0,()),(fun _ => 0,()))
def rejected : SharedLookupPCS.Selection F F ℕ 1 3 2 0 := (((fun _ => Fin.elim0,11),none),none)
def handler : QueryImpl Shared (StateM (List Input)) := fun query => match query with
  | .inl size => pure (⟨0,Nat.zero_lt_succ size⟩ : Fin (size+1))
  | .inr (.inl input) => do modify (· ++ [input]); pure (0 : Fin 2)
  | .inr (.inr _) => pure ()
def hash (input : Input) : OracleComp Shared (Fin 2) := liftM (Shared.query (.inr (.inl input)))
def run (_ : SharedLookupPCS.Emission 3 2 (Fin 2) Unit Unit) : OracleComp Shared (SharedLookupPCS.Selection F F ℕ 1 3 2 0) := do
  let _ ← hash (.inl [1])
  pure rejected

-- Both helper roots precede the three original source roots. Reusing a source
-- in many jobs does not add a source root to this list.
example : StagedHeterogeneousBatchOpening.factors (List.finRange 3) (List.finRange 2) =
    [.inr 0,.inr 1,.inl 0,.inl 1,.inl 2] := rfl

-- For arbitrary fallback packets AND arbitrary opening behavior, rejection
-- cannot be turned into PCS acceptance and no opening work is run. The real
-- hash in terminal selection is retained. No enabled/start flag is supplied.
example (fallback : SharedLookupOpeningFamily.Packet F F 1 3 0 2)
    (behavior : SharedLookupPCS.Emission 3 2 (Fin 2) Unit Unit → SharedLookupPCS.Selection F F ℕ 1 3 2 0 →
      (root : Root) → Protocol F Input (Fin 2) Unit Unit ℕ 1 heights tag (SharedLookupOpeningFamily.layout geometry) root) :
    (simulateQ handler (SharedLookupPCS.program (g := geometry) encoding basis (padding := 0) (c := 0) (row := 0) rfl
      domain fallback run behavior emission)).run [] = ((rejected,⟨[],11,false⟩),[.inl [1]]) := by
  simp only [SharedLookupPCS.program,HeterogeneousBatchOpening.continuation,SharedContinuation.program,run,
    simulateQ_bind,StateT.run_bind]
  have observed : (simulateQ handler (hash (.inl [1]))).run [] = (0,[.inl [1]]) := rfl
  rw [observed]
  simp only [simulateQ_pure,StateT.run_pure]
  rfl
end
end HasteBootsSharedLookupPCSSmoke
