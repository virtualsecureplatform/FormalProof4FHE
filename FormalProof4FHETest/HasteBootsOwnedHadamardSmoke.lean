module
import FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
import Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp
namespace HasteBootsOwnedHadamardSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev Factor := PBSHadamard.Factor 2
abbrev Input := Sum (List (ZMod 17)) (Fin 2 × Fin 2)
abbrev Shared := SharedSequence.Shared Unit Input (Fin 2)
def encoding : MerkleOracle.Encoding Input (Fin 2) (List (ZMod 17)) where
  leaf _ := Sum.inl
  node _ := Sum.inr
  leaf_injective _ := Sum.inl_injective
  node_injective _ := Sum.inr_injective

def domain : Fin 1 ↪ ZMod 17 := ⟨fun _ => 0,by decide +kernel⟩
def nodes : PackedSumcheckRound.Node 1 ↪ ZMod 17 :=
  ⟨fun node => if node.1 then 1 else 0,by decide +kernel⟩
def expected : Fin 2 → Fin 2 := fun level => level
-- The callback proposes the opposite setup roots. Trusted setup must win.
def supplied : Factor → Fin 2 := fun role => match role with
  | .inl (level,true) => if level.val = 0 then 1 else 0
  | .inl (_,false) => 1
  | .inr _ => 1

def commit : OracleComp Shared ((Factor → Fin 2) × ℕ) := do
  let _ ← Shared.query (.inr (.inl (Sum.inl [9])))
  let _ ← Shared.query (.inl 1)
  pure (supplied,7)

def protocol : NativeMatrixVerifier.Protocol (ZMod 17) Factor Input (Fin 2) Unit Unit ℕ 2 1 1 1 0 0 where
  encoding := encoding
  domain := domain
  root := supplied
  left := fun _ => 0
  right := fun _ => 0
  value := fun _ => 0
  testResponse := fun _ _ _ => 0
  structuredResponse := fun _ _ _ => 0
  respond := fun _ _ _ => pure ()
  receiveColumns := fun _ memory _ => pure ([],memory)
  choose := fun _ _ _ _ _ memory => pure (none,memory)
  fuel := fun _ _ _ _ => 0

def scheme : AuthenticatedZeroCheck.Scheme (ZMod 17) Factor (PBSHadamard.Term 2) Unit Unit
    Input (Fin 2) Unit Unit ℕ ℕ 1 0 1 0 1 0 0 where
  dimensions := rfl
  encoding := encoding
  domain := domain
  tag := fun _ => ()
  factors := []
  nodes := nodes
  arity := fun _ => 0
  coefficient := fun _ => 0
  indices := fun _ position => Fin.elim0 position
  interpretFirst := fun _ _ => 0
  interpret := fun _ => 0
  commit := commit
  initial := fun emission => emission.2
  firstRespond := fun _ _ memory => pure ((),memory)
  afterFirst := fun _ _ earlier _ => pure earlier.2
  send := fun _ _ memory _ => pure ((),memory)
  afterChallenge := fun _ memory _ => pure memory
  receiveValues := fun _ _ memory => pure (fun _ => 0,memory)
  bindValues := fun _ _ _ memory => pure memory
  build := fun _ _ => protocol

inductive Event where
  | hash : Input → Event
  | coin : ℕ → Event
  | root : Fin 2 → Event
  deriving DecidableEq

def handler : QueryImpl Shared (StateM (List Event)) := fun query => match query with
  | .inl size => do
      modify (· ++ [.coin size])
      pure (⟨0,Nat.zero_lt_succ size⟩ : Fin (size+1))
  | .inr (.inl input) => do
      modify (· ++ [.hash input])
      pure (0 : Fin 2)
  | .inr (.inr (_,root)) => do
      modify (· ++ [.root root])
      pure ()

def configured := OwnedHadamardSoundness.stage expected scheme

-- The actual callback still performs its hash and private draw, in order,
-- and retains its memory. No setup-root replacement performs an oracle call.
example : (simulateQ handler configured.commit).run [] =
    ((OwnedHadamardSoundness.roots expected supplied,7),[.hash (.inl [9]),.coin 1]) := rfl

-- The original native factor order includes BOTH setup key openings.
example : configured.factors = [.inl (0,false),.inl (0,true),.inl (1,false),.inl (1,true),.inr ()] := by
  decide +kernel
example : configured.factors.length = 5 := by decide +kernel
example : OwnedHadamardSoundness.roots expected supplied (.inl (0,true)) ≠ supplied (.inl (0,true)) := by decide +kernel
example : OwnedHadamardSoundness.roots expected supplied (.inl (1,true)) ≠ supplied (.inl (1,true)) := by decide +kernel
example : OwnedHadamardSoundness.roots expected supplied (.inl (0,false)) = 1 ∧
    OwnedHadamardSoundness.roots expected supplied (.inr ()) = 1 := by decide +kernel

-- The supplied opening factory also proposes the wrong key root. The actual
-- native opening adapter reads the trusted emitted root instead.
def packet : PreparedZeroTerminal.Packet (ZMod 17) Factor ℕ 1 0 :=
  ⟨none,⟨fun _ => 0,7,false⟩⟩
def actualProtocol := NativeCommittedOpening.protocol configured.encoding configured.domain
  (AuthenticatedZeroCheck.left configured) (AuthenticatedZeroCheck.right configured)
  (AuthenticatedZeroCheck.build configured) (OwnedHadamardSoundness.roots expected supplied,7) packet
example : protocol.root (.inl (0,true)) = 1 ∧ actualProtocol.root (.inl (0,true)) = 0 := by
  decide +kernel
example : actualProtocol.root (.inl (1,true)) = 1 := by decide +kernel

end
end HasteBootsOwnedHadamardSmoke
