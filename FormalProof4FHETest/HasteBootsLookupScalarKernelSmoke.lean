module
import all FormalProof4FHE.HasteBoots.CallerLookupScalars
import all FormalProof4FHE.HasteBoots.LookupPairChallengeBounds
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace HasteBootsLookupScalarKernelSmoke
open FormalProof4FHE.HasteBoots
open NativeFields (Goldilocks goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open HasteBootsSamplerAncestrySmoke (child worldOne worldZero worldReject basis)
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

/-- Small-characteristic fixtures exercise the generic native offset guard
with computable field equality. The coefficient-rejection fixture uses the
actual Goldilocks cubic collector. -/
def accepted := (OracleProgram.run (NativeLookupChallenge.request basis 1 1 2 [[0]] child) worldOne).run
def zeros := (OracleProgram.run (NativeLookupChallenge.request basis 1 1 3 [[0]] child) worldZero).run
def rejected := (OracleProgram.run (NativeLookupChallenge.request goldilocksBasis 7 1 5 [[0]] child) worldReject).run

theorem completed_original_pair : accepted.1.draws.length = 2 ∧ accepted.1.rejected = 0 ∧
    accepted.1.draws.map (fun draw => (draw.coefficients.values.length,draw.coefficients.phase.consumed.length)) =
      [(1,1),(1,1)] := by decide +kernel

/-- Forbidden zero offsets remain as complete original draws and receipts. -/
theorem forbidden_offsets_retained : zeros.1.draws.length = 3 ∧ zeros.1.rejected = 2 ∧
    zeros.1.draws.map (fun draw => draw.coefficients.phase.consumed.length) = [1,1,1] := by decide +kernel

/-- Canonical coefficient rejection is a different suspension from forbidden
completed offsets; no draw or offset rejection is fabricated. -/
theorem coefficient_rejection : rejected.1.draws.length = 0 ∧ rejected.1.rejected = 0 ∧
    (match rejected.1.control with
      | .compression field => (field.values.length,field.phase.consumed.length)
      | _ => (99,99)) = (0,40) := by decide +kernel

theorem retained_inputs_exposed :
    accepted.1.draws.map (fun draw => CausalStreamExposure.seen accepted.2 draw.coefficients.phase.pending.input) = [true,true] ∧
    zeros.1.draws.map (fun draw => CausalStreamExposure.seen zeros.2 draw.coefficients.phase.pending.input) = [true,true,true] := by decide +kernel

/-- Each retry's receipt is incorporated in the next original field input. -/
theorem retry_inputs_distinct :
    (zeros.1.draws[1]'(by decide +kernel)).coefficients.phase.pending.input ≠
      (zeros.1.draws[2]'(by decide +kernel)).coefficients.phase.pending.input := by decide +kernel

/-- Tuple inequality alone does not imply hashed inequality at the stored y. -/
theorem genuine_compression_collision :
    (![0,1] : Fin 2 → Goldilocks) ≠ ![0,0] ∧
      TupleHash.hash (0 : Goldilocks3) (![0,1] : Fin 2 → Goldilocks) = TupleHash.hash 0 (![0,0] : Fin 2 → Goldilocks) := by
  constructor
  · intro same
    have unequal := congrFun same 1
    norm_num at unequal
  · simp [TupleHash.hash_eq_sum,Fin.sum_univ_two]

end
end HasteBootsLookupScalarKernelSmoke
