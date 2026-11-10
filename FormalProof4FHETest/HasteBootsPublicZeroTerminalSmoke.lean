module
import FormalProof4FHE.HasteBoots.AuthenticatedExtraction
import FormalProof4FHETest.HasteBootsKeySwitchExtractionSmoke
open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp
open scoped BigOperators Matrix
namespace HasteBootsPublicZeroTerminalSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

abbrev Shared := SharedSequence.Shared Unit (Fin 4) (Fin 2)
def hash (input : Fin 4) : OracleComp Shared (Fin 2) :=
  liftM (Shared.query (.inr (.inl input)))
def nodes : PackedSumcheckRound.Node 1 ↪ ZMod 17 := NativePackedInterpolation.nodes 17 (by decide +kernel)
def publicTables (target : Bool) : MatrixFold.Cube 1 → Fin 1 → ZMod 17 := fun _ _ => if target then 3 else 1
def claim : PackedZeroOracle.Subclaim (ZMod 17) 1 0 where
  points := fun _ index => Fin.elim0 index
  coins := (fun _ _ => 1, fun _ => nodes (false,0))
  rest := ⟨.nil,fun _ => 0⟩
def receive (claimed : ZMod 17) (_claim : PackedZeroOracle.Subclaim (ZMod 17) 1 0) (memory : ℕ) :
    OracleComp Shared ((Unit → Fin 1 → ZMod 17) × ℕ) := do
  let _ ← hash 0
  pure (fun _ _ => claimed,memory+1)
def bind (_claim : PackedZeroOracle.Subclaim (ZMod 17) 1 0) (_values : Unit → Fin 1 → ZMod 17) (memory : ℕ) : OracleComp Shared ℕ := do
  let _ ← hash 1
  pure (memory+10)

theorem fold_at_node (value : ZMod 17) : (claim.query nodes).fold (fun _ _ => value) = fun _ => value := by
  funext lane
  fin_cases lane
  change (∑ bit : Bool, PackedSumcheckRound.challengePair nodes (fun _ => nodes (false,0)) bit *ᵥ (fun _ => value)) 0 = value
  rw [PackedSumcheckRound.challengePair_fold]
  exact PackedSumcheckRound.factorPolynomial_node nodes (fun _ _ => value) false 0

theorem public_fold (role : Bool) : (claim.query nodes).fold (publicTables role) = fun _ => if role then 3 else 1 := by
  cases role <;> exact fold_at_node _

theorem correct_check : PackedZeroOracle.Subclaim.check PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices
    (PreparedPublicZeroTerminal.values nodes publicTables (fun _ _ => (3 : ZMod 17)) claim) claim = true := by
  simp only [PackedZeroOracle.Subclaim.check,PackedZeroTerminal.check,AuthenticatedExtraction.expression,
    PreparedPublicZeroTerminal.values,Sum.elim_inl,Sum.elim_inr,public_fold]
  decide +kernel
theorem wrong_check : PackedZeroOracle.Subclaim.check PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices
    (PreparedPublicZeroTerminal.values nodes publicTables (fun _ _ => (4 : ZMod 17)) claim) claim = false := by
  simp only [PackedZeroOracle.Subclaim.check,PackedZeroTerminal.check,AuthenticatedExtraction.expression,
    PreparedPublicZeroTerminal.values,Sum.elim_inl,Sum.elim_inr,public_fold]
  decide +kernel

-- A successful prepare retains the receive hash, bind hash, private values
-- and updated memory in precisely that order.
example : PreparedPublicZeroTerminal.prepare nodes publicTables PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices
    (receive 3) bind 99 (some (claim,5)) = (do
      let _ ← hash 0
      let _ ← hash 1
      pure (⟨fun _ _ => (3 : ZMod 17),16,true⟩ : PreparedPublicZeroTerminal.Data (ZMod 17) Unit ℕ 1)) := by
  simp only [PreparedPublicZeroTerminal.prepare,receive,bind,bind_assoc,pure_bind,correct_check,ite_true]
-- Rejection keeps the receive hash and its memory, and never runs bind.
example : PreparedPublicZeroTerminal.prepare nodes publicTables PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices
    (receive 4) bind 99 (some (claim,5)) = (do
      let _ ← hash 0
      pure (⟨fun _ _ => (4 : ZMod 17),6,false⟩ : PreparedPublicZeroTerminal.Data (ZMod 17) Unit ℕ 1)) := by
  simp only [PreparedPublicZeroTerminal.prepare,receive,bind_assoc,pure_bind,wrong_check,Bool.false_eq_true,ite_false]
-- No returned subclaim issues neither callback nor any fallback hash work.
example : PreparedPublicZeroTerminal.prepare nodes publicTables PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices
    (receive 3) bind 99 none = pure (⟨fun _ _ => 0,99,false⟩ : PreparedPublicZeroTerminal.Data (ZMod 17) Unit ℕ 1) := rfl

def privateTables (_ : Unit) : MatrixFold.Cube 1 → Fin 1 → ZMod 17 := fun _ _ => 3
def packet : PreparedPublicZeroTerminal.Packet (ZMod 17) Unit ℕ 1 0 := ⟨some (claim,5),⟨fun _ _ => 3,16,true⟩⟩
example : PackedZeroOracle.TruthfulResult nodes PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices
    (Sum.elim privateTables publicTables) packet.earlier := by
  have alternative := PreparedPublicZeroTerminal.checked_truthful_or_wrong_private nodes publicTables
    PBSHadamard.arity PBSHadamard.coefficient AuthenticatedExtraction.indices privateTables packet (claim,5) rfl correct_check
  rcases alternative with truthful | ⟨factor,wrong⟩
  · exact truthful
  · cases factor
    have equal : packet.data.values () = (PreparedPublicZeroTerminal.query nodes packet).fold (privateTables ()) := (fold_at_node 3).symm
    exact False.elim (wrong equal)

-- The complete extraction specialization uses the same golden source table.
example : AuthenticatedExtraction.Relation (c := 1) (lanes := 1) HasteBootsKeySwitchExtractionSmoke.positive
    HasteBootsCanonicalKeySwitchSmoke.acc HasteBootsCanonicalKeySwitchSmoke.output
    (KeySwitchExtraction.pack (c := 1) (lanes := 1) HasteBootsCanonicalKeySwitchSmoke.trace.increment) := by
  unfold AuthenticatedExtraction.Relation
  decide +kernel
end
end HasteBootsPublicZeroTerminalSmoke
