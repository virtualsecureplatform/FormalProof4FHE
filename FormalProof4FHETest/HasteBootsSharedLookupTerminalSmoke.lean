module
import FormalProof4FHE.HasteBoots.SharedLookupTerminalSoundness
import Mathlib.Algebra.Field.ZMod
open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
open scoped Matrix
namespace HasteBootsSharedLookupTerminalSmoke
noncomputable section
open scoped Classical
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17
def basis : Module.Basis (Fin 1) F F := Module.Basis.singleton _ _

theorem zero_decode (columns : ℕ) :
    LookupPairTerminal.decodeSources basis (padding := 0) (c := 0) (row := 0) rfl Fin.elim0 columns
      (fun _ _ => 0) = some (fun _ => 0) := by
  have parsed : PaddedExtension.element (padding := 0) basis (0 : Fin 1 → F) = some 0 := by
    simpa only [map_zero] using PaddedExtension.element_encode (padding := 0) basis (0 : F)
  have projected : (ExtensionLookupTerminal.sourceQuery basis (padding := 0) (c := 0) (row := 0) rfl
      (Fin.elim0 : Fin 0 → F)).finish (0 : Fin 1 → F) = 0 := Matrix.mulVec_zero _
  induction columns with
  | zero =>
    change some (Fin.elim0 : Fin 0 → F) = some (fun _ => 0)
    congr 1
    funext index
    exact Fin.elim0 index
  | succ columns ih =>
    change (PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis (padding := 0) (c := 0) (row := 0) rfl
      Fin.elim0).finish (0 : Fin 1 → F))).bind (fun first : F =>
        (LookupPairTerminal.decodeSources basis (padding := 0) (c := 0) (row := 0) rfl Fin.elim0 columns (fun _ _ => 0)).bind
          (fun rest => some (Fin.cons first rest))) = some (fun _ : Fin (columns+1) => (0 : F))
    rw [projected,parsed,ih]
    simp only [Option.bind_some]
    congr 1
    funext index
    exact Fin.cases rfl (fun _ => rfl) index

theorem zero_check (columns : ℕ) :
    LookupPairTerminal.check basis (padding := 0) (c := 0) (row := 0) rfl Fin.elim0 Fin.elim0
      1 0 1 (by decide +kernel) (fun _ : Fin columns => fun _ => 0) 1 0 = true := by
  rw [LookupPairTerminal.check,zero_decode]
  simp only [decide_eq_true_eq]
  simp [ExtensionLookupIdentity.terminal,NativePrefixMask.evaluatePrefix,ExtensionLookupIdentity.equality]

theorem wrong_helper_check (columns : ℕ) :
    LookupPairTerminal.check basis (padding := 0) (c := 0) (row := 0) rfl Fin.elim0 Fin.elim0
      1 0 1 (by decide +kernel) (fun _ : Fin columns => fun _ => 0) 2 0 = false := by
  rw [LookupPairTerminal.check,zero_decode]
  simp [ExtensionLookupIdentity.terminal,NativePrefixMask.evaluatePrefix,ExtensionLookupIdentity.equality]
  decide +kernel

def slots : (job : Fin 2) → Fin 3 → Fin 3 := ![![0,1,1],![1,2,0]]
def pairs (_ : Fin 2) : F × F := (0,1)
def active (_ : Fin 2) : ℕ := 1
theorem enough (job : Fin 2) : active job ≤ 2^(0+0) := le_rfl

def claims (wrongSum : Bool) (equation : Fin 2 × Bool) : Subclaim F 1 0 :=
  ⟨.nil,fun _ => if equation.2 then 0 else if wrongSum && equation.1 = 1 then 2 else 1⟩
def earlier (wrongSum : Bool) : SharedLookupBatchSequence.Result F ℕ 2 0 :=
  ((fun _ => Fin.elim0,99),some (claims wrongSum,11))
def values : SharedLookupTerminal.Values F F 1 3 2 := ⟨fun _ _ => 0,fun _ => 1⟩
def packet (wrongSum : Bool) : SharedLookupOpeningFamily.Packet F F 1 3 0 2 :=
  SharedLookupOpeningFamily.ofBatch (d := 1) (padding := 0) (c := 0) (row := 0)
    (claims wrongSum) (0,false) values.sources values.helpers (fun _ => Fin.elim0)

theorem guard_accepts : SharedLookupTerminal.guard basis (padding := 0) (c := 0) (row := 0) rfl
    slots pairs active enough (packet false) = true := by
  simp [SharedLookupTerminal.guard,packet,SharedLookupOpeningFamily.ofBatch,values,claims,pairs,active,ScalarSumcheckQuery.point,zero_check]

-- The first job passes; a false sum/helper equality in the second job rejects
-- the entire guard, even though both identity checks would otherwise pass.
theorem guard_rejects : SharedLookupTerminal.guard basis (padding := 0) (c := 0) (row := 0) rfl
    slots pairs active enough (packet true) = false := by
  have neq : (2 : F) ≠ 1 := by decide +kernel
  simp [SharedLookupTerminal.guard,packet,SharedLookupOpeningFamily.ofBatch,values,claims,pairs,active,ScalarSumcheckQuery.point,zero_check,neq]

-- Every sum/helper equality passes here, but the second identity fails.
-- This checks the identity gate independently of the sum/helper gate.
def badIdentity : SharedLookupOpeningFamily.Packet F F 1 3 0 2 :=
  { packet true with helpers := fun job => if job = 1 then 2 else 1 }
example : SharedLookupTerminal.guard basis (padding := 0) (c := 0) (row := 0) rfl
    slots pairs active enough badIdentity = false := by
  simp [SharedLookupTerminal.guard,badIdentity,packet,SharedLookupOpeningFamily.ofBatch,values,claims,pairs,
    active,ScalarSumcheckQuery.point,zero_check,wrong_helper_check]

abbrev Shared := SharedLookupBatchSequence.Shared Unit (Fin 4) (Fin 2)
def handler : QueryImpl Shared (StateM (List (Fin 4))) := fun query => match query with
  | .inl _ => pure ⟨0,Nat.zero_lt_succ _⟩
  | .inr (.inl input) => do modify (· ++ [input]); pure (0 : Fin 2)
  | .inr (.inr _) => pure ()
def hash (input : Fin 4) : OracleComp Shared (Fin 2) := liftM (Shared.query (.inr (.inl input)))
def receiver : SharedLookupTerminal.Receiver F F ℕ Unit (Fin 4) (Fin 2) 1 3 2 0 where
  receive _ _ memory := do let _ ← hash 1; pure (values,memory+5)
  bindValues _ memory := do let _ ← hash 2; pure (memory+7)

-- Successful binding follows receipt, using the batch memory (11), not the
-- older equality-draw memory (99), and preserves the actual packet.
example : (simulateQ handler (SharedLookupTerminal.prepare basis (padding := 0) (c := 0) (row := 0) rfl
    (by decide +kernel) slots pairs active enough receiver (earlier false))).run [] =
    (some (packet false,23),[1,2]) := by
  simp only [SharedLookupTerminal.prepare,earlier,receiver,simulateQ_bind,StateT.run_bind]
  have received : (simulateQ handler (hash 1)).run [] = (0,[1]) := rfl
  rw [received]
  simp only [simulateQ_pure,StateT.run_pure]
  change (simulateQ handler (if SharedLookupTerminal.guard basis (padding := 0) (c := 0) (row := 0) rfl
    slots pairs active enough (packet false) = true then _ else _)).run [1] = _
  rw [guard_accepts]
  rfl

-- Failed terminals keep receipt's hash work and skip value binding.
example : (simulateQ handler (SharedLookupTerminal.prepare basis (padding := 0) (c := 0) (row := 0) rfl
    (by decide +kernel) slots pairs active enough receiver (earlier true))).run [] = (none,[1]) := by
  simp only [SharedLookupTerminal.prepare,earlier,receiver,simulateQ_bind,StateT.run_bind]
  have received : (simulateQ handler (hash 1)).run [] = (0,[1]) := rfl
  rw [received]
  simp only [simulateQ_pure,StateT.run_pure]
  change (simulateQ handler (if SharedLookupTerminal.guard basis (padding := 0) (c := 0) (row := 0) rfl
    slots pairs active enough (packet true) = true then _ else _)).run [1] = _
  rw [guard_rejects]
  rfl

-- A rejected batch causes neither receipt nor binding.
example : (simulateQ handler (SharedLookupTerminal.prepare basis (padding := 0) (c := 0) (row := 0) rfl
    (by decide +kernel) slots pairs active enough receiver ((fun _ => Fin.elim0,99),none))).run [] = (none,[]) := rfl
-- Local terminal acceptance is insufficient for authentication: the accepted
-- received helper one is a wrong opening of an original all-zero helper.
example : SharedLookupTerminalReduction.Wrong basis (padding := 0) (c := 0) (row := 0) rfl slots
    (fun _ _ _ => 0) (fun _ _ _ => 0) (packet false) := by
  refine ⟨(0 : Fin 2),Or.inl ?_⟩
  change PaddedExtension.encode (padding := 0) basis (1 : F) ≠ (0 : Fin 1 → F)
  intro equal
  have decoded := congrArg (PaddedExtension.decode basis) equal
  have impossible : (1 : F) = 0 := by simpa only [PaddedExtension.decode_encode,map_zero] using decoded
  exact one_ne_zero impossible

end
end HasteBootsSharedLookupTerminalSmoke
