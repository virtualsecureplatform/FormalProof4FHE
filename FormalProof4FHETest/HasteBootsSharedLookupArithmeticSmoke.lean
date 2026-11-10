module
import FormalProof4FHE.HasteBoots.SharedLookupBatchArithmetic
import Mathlib.Algebra.Field.ZMod
open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots
open scoped BigOperators Matrix
namespace HasteBootsSharedLookupArithmeticSmoke
noncomputable section
namespace Order
abbrev Shared := OrderedPrivateDraws.Shared Unit (Fin 4) (Fin 2)
inductive Event where
  | coin : ℕ → Event
  | hash : Fin 4 → Event
  deriving DecidableEq

def handler : QueryImpl Shared (StateM (List Event)) := fun query => match query with
  | .inl size => do
      modify (· ++ [.coin size])
      pure (⟨0,Nat.zero_lt_succ size⟩ : Fin (size+1))
  | .inr (.inl input) => do
      modify (· ++ [.hash input])
      pure (⟨0,by decide +kernel⟩ : Fin 2)
  | .inr (.inr _) => pure ()
def hash (input : Fin 4) : OracleComp Shared (Fin 2) := liftM (Shared.query (.inr (.inl input)))
def beforeDraw (offset memory : ℕ) : OracleComp Shared ℕ := do
  let _ ← hash ⟨offset%4,Nat.mod_lt _ (by decide +kernel)⟩
  pure (memory+1)
def afterDraw (offset memory : ℕ) (_ : Fin 2) : OracleComp Shared ℕ := do
  let _ ← hash ⟨(offset+2)%4,Nat.mod_lt _ (by decide +kernel)⟩
  pure (memory+10)

-- Work remains interleaved with individual draws in job order, rather than
-- being moved outside a single simultaneous draw of all equality points.
example : ((simulateQ handler (OrderedPrivateDraws.program beforeDraw afterDraw 2 0 0)).run []).2 =
    [.hash 0,.coin 1,.hash 2,.hash 1,.coin 1,.hash 3] := rfl
example : ((simulateQ handler (OrderedPrivateDraws.program beforeDraw afterDraw 2 0 0)).run []).1.2 = 22 := rfl
end Order

namespace HeterogeneousJobs
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17
local instance : SampleableType F := SampleableType.ofFintype _
local instance : SampleableType (Fin 1 → F) := SampleableType.ofFintype _
local instance : SampleableType Unit := SampleableType.ofFintype _
def columns : Fin 2 → ℕ := ![1,2]
def sizes : Fin 2 → ℕ := ![1,2]
def tables (job : Fin 2) : Fin (sizes job) → Fin (columns job) → F :=
  fun row _ => if job = 0 then 4 else row.val
-- The literal tables have different tuple widths and row counts.
example : tables 0 (0 : Fin 1) = (![4] : Fin 1 → F) := by funext i; fin_cases i; rfl
example : tables 1 (1 : Fin 2) = (![1,1] : Fin 2 → F) := by funext i; fin_cases i <;> rfl

def multiplicities (job : Fin 2) : Fin (sizes job) → F := fun _ => if job = 0 then 1 else 0
def pairs : Fin 2 → F × F := ![(3,2),(2,1)]
def sources (_ : Fin 2) (_ : MatrixFold.Cube 1) : F := 2
def helpers (_ : MatrixFold.Cube 1) : F := 0

theorem notPasses : ¬TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples (active := 1) (inactive := 1) (n := 1) rfl sources) (tables 1)
    (fun i => algebraMap F F (multiplicities 1 i)) (pairs 1) := by
  unfold TupleLookupPair.Passes
  rw [ReciprocalDetection.passes_iff]
  decide +kernel

abbrev Shared := SharedLookupBatchSequence.Shared Unit (Fin 4) Unit
def schedule : SharedLookupBatchSequence.Schedule F Unit ℕ Unit (Fin 4) Unit 2 1 where
  beforeEquality _ memory := pure (memory+1)
  afterEquality _ memory _ := pure (memory+10)
  interpret _ _ equation := if equation.2 then 0 else
    Polynomial.C (SharedLookupBatchArithmetic.totals pairs tables multiplicities equation.1 / 2)
  send _ _ memory _ := pure ((),memory+100)
  afterChallenge _ memory _ := pure (memory+1000)

-- The adversarial constant messages pass every equation's round check;
-- the probability regression is not made vacuous by another job rejecting.
theorem all_checks (points : SharedLookupBatchSequence.Points F 2 1) :
    ∀ equation, PackedSumcheckProbability.Checks (NativePackedInterpolation.nodes 17 (by decide +kernel))
      (SharedLookupBatchSequence.initialClaims (SharedLookupBatchArithmetic.totals pairs tables multiplicities) equation)
      (schedule.interpret points () equation) := by
  intro equation lane
  rcases equation with ⟨job,bit⟩
  cases bit <;> simp [schedule,SharedLookupBatchSequence.initialClaims]
  have two : (2 : F) ≠ 0 := by decide +kernel
  field_simp [two]
  ring

def encoding : MerkleOracle.Encoding (Fin 4) Unit Unit where
  leaf _ _ := 2
  node _ _ := 3
  leaf_injective _ := by intro first last _; cases first; cases last; rfl
  node_injective _ := by intro first last _; cases first with | mk a b => cases last with | mk c d => cases a; cases b; cases c; cases d; rfl

def shape (_ : Unit) : Skeleton := .perfect 0

-- A real nonpassing job uses its own table and multiplicities, even though
-- the other job has a different table and contributes different public claims.
example : Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding () shape)
    (SharedLookupBatchSequence.program 17 (by decide +kernel) schedule
      (SharedLookupBatchArithmetic.totals pairs tables multiplicities) 0)).run (CheckpointExecution.empty shape)}[
      SharedLookupBatchSequence.JointTruthful (1 : Fin 2) ExtensionLookupIdentity.partialArity
        (ExtensionLookupIdentity.partialCoefficient (pairs 1).2) ExtensionLookupIdentity.partialIndices
        (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs 1).1 sources helpers 1) helpers outcome.1] ≤
      (1 : ENNReal)/17 + 1*(4/17) := by
  have bound := SharedLookupBatchArithmetic.partial_bound encoding () shape 17 (by decide +kernel) schedule
    (1 : Fin 2) pairs tables multiplicities (active := 1) (inactive := 1) rfl sources helpers
    (by decide +kernel) notPasses (by intro points message; simp [schedule])
    (by intro points message; simp [schedule]) 0 (CheckpointExecution.empty shape)
  convert bound using 1 <;> norm_num [F,ZMod.card]
  rfl
theorem notPassesFull : ¬TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples (active := 2) (inactive := 0) (n := 1) rfl sources) (tables 1)
    (fun i => algebraMap F F (multiplicities 1 i)) (pairs 1) := by
  unfold TupleLookupPair.Passes
  rw [ReciprocalDetection.passes_iff]
  decide +kernel

-- The same shared execution retains the sharper full-table degree-three
-- bound when both Boolean rows are active.
example : Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding () shape)
    (SharedLookupBatchSequence.program 17 (by decide +kernel) schedule
      (SharedLookupBatchArithmetic.totals pairs tables multiplicities) 0)).run (CheckpointExecution.empty shape)}[
      SharedLookupBatchSequence.JointTruthful (1 : Fin 2) ExtensionLookupIdentity.fullArity
        (ExtensionLookupIdentity.fullCoefficient (K := F)) ExtensionLookupIdentity.fullIndices
        (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs 1).2 (pairs 1).1 sources helpers) helpers outcome.1] ≤
      (1 : ENNReal)/17 + 1*(3/17) := by
  have bound := SharedLookupBatchArithmetic.full_bound encoding () shape 17 (by decide +kernel) schedule
    (1 : Fin 2) pairs tables multiplicities sources helpers (by decide +kernel) notPassesFull
    (by intro points message; simp [schedule]) (by intro points message; simp [schedule])
    0 (CheckpointExecution.empty shape)
  convert bound using 1 <;> norm_num [F,ZMod.card]
  rfl

end HeterogeneousJobs
end
end HasteBootsSharedLookupArithmeticSmoke
