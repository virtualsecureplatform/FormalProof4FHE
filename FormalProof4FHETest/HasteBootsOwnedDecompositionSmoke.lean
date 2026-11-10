module
import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp
namespace HasteBootsOwnedDecompositionSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev Input := Sum (List (ZMod 17)) (Fin 4 × Fin 4)
abbrev Shared := SharedSequence.Shared Unit Input (Fin 4)
def encoding : MerkleOracle.Encoding Input (Fin 4) (List (ZMod 17)) where
  leaf _ := Sum.inl
  node _ := Sum.inr
  leaf_injective _ := Sum.inl_injective
  node_injective _ := Sum.inr_injective

def domain : Fin 1 ↪ ZMod 17 := ⟨fun _ => 0,by decide +kernel⟩
def nodes : PackedSumcheckRound.Node 1 ↪ ZMod 17 :=
  ⟨fun node => if node.1 then 1 else 0,by decide +kernel⟩
def digits (i : Fin 3) : Fin 4 := ⟨i.val+1,by have := i.isLt; omega⟩
def supplied (_ : Fin 8) : Fin 4 := 3
def commit : OracleComp Shared ((Fin 8 → Fin 4) × ℕ) := do
  let _ ← Shared.query (.inr (.inl (.inl [9])))
  let _ ← Shared.query (.inl 1)
  pure (supplied,7)

def protocol : SingletonOpening.Protocol (ZMod 17) Input (Fin 4) Unit Unit ℕ 1 0 0 1 0 0 where
  encoding := encoding
  domain := domain
  root := 3
  query := .nil
  value := 0
  testResponse := fun _ _ => 0
  structuredResponse := fun _ _ => 0
  prepare := pure
  respond := fun _ _ => pure ()
  receiveColumns := fun memory _ => pure ([],memory)
  choose := fun _ _ _ _ memory => pure (none,memory)
  fuel := fun _ _ _ => 0

def scheme : AuthenticatedLinear.Scheme (ZMod 17) Input (Fin 4) Unit Unit ℕ ℕ 8 1 0 0 1 0 0 where
  encoding := encoding
  domain := domain
  tag := fun _ => ()
  relations := []
  nodes := nodes
  commit := commit
  initial := Prod.snd
  bindRelations := fun _ => pure
  receive := fun _ memory _ => pure (fun _ => 0,memory)
  build := fun _ _ _ => protocol

def configured := OwnedDecompositionSoundness.stage (0 : Fin 4) digits (4 : ZMod 17) scheme
inductive Event where
  | hash : Input → Event
  | coin : ℕ → Event
  | root : Fin 4 → Event
  deriving DecidableEq

def handler : QueryImpl Shared (StateM (List Event)) := fun query => match query with
  | .inl size => do
      modify (· ++ [.coin size])
      pure (⟨0,Nat.zero_lt_succ size⟩ : Fin (size+1))
  | .inr (.inl input) => do
      modify (· ++ [.hash input])
      pure (0 : Fin 4)
  | .inr (.inr (_,root)) => do
      modify (· ++ [.root root])
      pure ()

example : (simulateQ handler configured.commit).run [] =
    ((OwnedDecompositionSoundness.roots 0 digits supplied,7),[.hash (.inl [9]),.coin 1]) := rfl
example : AuthenticatedLinear.preflight configured = true := by decide +kernel
example : AuthenticatedLinear.factors 8 = [0,1,2,3,4,5,6,7] := by decide +kernel
example : configured.relations.length = 3 := by decide +kernel
example : OwnedDecompositionSoundness.roots 0 digits supplied DecompositionLinear.input = 0 ∧
    (∀ i : Fin 3, OwnedDecompositionSoundness.roots 0 digits supplied (DecompositionLinear.digit i) = digits i) ∧
    (∀ i : Fin 4, OwnedDecompositionSoundness.roots 0 digits supplied (DecompositionLinear.borrow i) = 3) := by
  decide +kernel

def packet : PackedLinearOracle.Packet (ZMod 17) (Fin 8) ℕ 1 0 := ⟨.nil,fun _ => 0,7,false⟩
def actual (factor : Fin 8) := AuthenticatedLinear.single configured
  (OwnedDecompositionSoundness.roots 0 digits supplied,7) packet factor
-- A conflicting factory root cannot replace any caller-supplied source/digit.
example : protocol.root = 3 ∧ (actual (DecompositionLinear.input (d := 3))).root = 0 ∧
    (actual (DecompositionLinear.digit (0 : Fin 3))).root = 1 ∧
    (actual (DecompositionLinear.lastBorrow (d := 3))).root = 3 := by decide +kernel

end
end HasteBootsOwnedDecompositionSmoke
