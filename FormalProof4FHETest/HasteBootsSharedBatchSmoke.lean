module
import FormalProof4FHE.HasteBoots.SharedScalarBatchQuery
import Mathlib.Algebra.Field.ZMod

open OracleSpec OracleComp BinaryTree Polynomial
open FormalProof4FHE.HasteBoots
namespace HasteBootsSharedBatchSmoke
noncomputable section
open scoped Classical
abbrev F := ZMod 17
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
local instance : SampleableType (Fin 1 → F) := SampleableType.ofFintype _
abbrev Shared := SharedBatchSumcheckOracle.Shared Unit (Fin 4) (Fin 2)
def nodes : PackedSumcheckRound.Node 1 ↪ F := NativePackedInterpolation.nodes 17 (by decide +kernel)
def interpret (_ : Unit) (equation : Bool) : Polynomial F := C (if equation then 2 else 1)
def claimed (equation : Bool) (_ : Fin 1) : F := if equation then 4 else 2
def rejectedClaim (equation : Bool) (_ : Fin 1) : F := if equation then 3 else 2

theorem checks : ∀ equation, PackedSumcheckProbability.Checks nodes (claimed equation) (interpret () equation) := by
  intro equation lane
  cases equation <;> simp only [claimed,interpret,Bool.false_eq_true,reduceIte,Polynomial.eval_C] <;> decide +kernel

-- The selected first equation passes, but the second equation rejects the
-- whole batch before any challenge or callback.
theorem other_rejects : ¬∀ equation, PackedSumcheckProbability.Checks nodes (rejectedClaim equation) (interpret () equation) := by
  intro all
  have wrong := all true 0
  have neq : (2 + 2 : F) ≠ 3 := by decide +kernel
  exact neq (by simpa only [rejectedClaim, interpret, ite_true, Polynomial.eval_C] using wrong)

def hash (input : Fin 4) : OracleComp Shared (Fin 2) := liftM (Shared.query (.inr (.inl input)))
def send (_ : ℕ) (memory : ℕ) (_ : Bool → Fin 1 → F) : OracleComp Shared (Unit × ℕ) := do
  let _ ← hash 1
  pure ((),memory+1)
def callback (memory : ℕ) (_ : Fin 1 → F) : OracleComp Shared ℕ := do
  let _ ← hash 2
  pure (memory+10)

-- Successful round syntax contains one private draw, after the complete
-- batch check; both equations use that same draw in their terminal values.
example : SharedBatchSumcheckOracle.program nodes interpret send callback 1 claimed 7 = (do
    let packet ← send 1 7 claimed
    let challenge ← PrivateSampling.embed Unit (Fin 4) (Fin 2) ($ᵗ (Fin 1 → F))
    let memory ← callback packet.2 challenge
    pure (SharedBatchSumcheckOracle.prependResult (PackedSumcheckRound.challengePair nodes challenge)
      (some ((fun equation => ⟨.nil,fun lane => (interpret packet.1 equation).eval (challenge lane)⟩),memory)))) := by
  simp only [SharedBatchSumcheckOracle.program, send, hash, bind_assoc, checks, implies_true, ite_true,
    pure_bind]

-- Hash work in the message remains even on rejection; no callback is run.
example : SharedBatchSumcheckOracle.program nodes interpret send callback 1 rejectedClaim 7 = (do
    let _ ← hash 1
    pure none) := by
  simp only [SharedBatchSumcheckOracle.program, send, bind_assoc, pure_bind, other_rejects, ite_false]

-- Query validity includes equality across equations, not merely scalar form
-- for independently sampled queries.
example (p : ℕ) [CharP F p] (small : 2 * 1 ≤ p) (challenge : Fin 1 → F) :
    SharedScalarBatchQuery.Valid (SharedBatchSumcheckOracle.prependResult
      (PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes p small) challenge)
      (some ((fun equation : Bool => ⟨.nil,claimed equation⟩),7))) :=
  SharedScalarBatchQuery.valid_prepend p small challenge _
    ⟨fun _ => ScalarSumcheckQuery.scalar_nil,fun _ _ => rfl⟩
-- Independently valid scalar queries do not satisfy the common-query
-- invariant when their points differ.
def differentQueries : Option ((Bool → PackedSumcheckSubclaim.Subclaim F 1 1) × ℕ) :=
  some ((fun equation => ⟨ScalarSumcheckQuery.query 1 (fun _ => if equation then 1 else 0),claimed equation⟩),7)
example : ¬SharedScalarBatchQuery.Valid differentQueries := by
  intro valid
  have equal := congrArg (fun q => ScalarSumcheckQuery.point q 0) (valid.2 false true)
  have neq : (0 : F) ≠ 1 := by decide +kernel
  exact neq (by simpa only [differentQueries,ScalarSumcheckQuery.point_query,Bool.false_eq_true,ite_false,ite_true] using equal)

end
end HasteBootsSharedBatchSmoke
