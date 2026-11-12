module
import all FormalProof4FHE.HasteBoots.LookupEqualityResidual
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace HasteBootsGoldEqualityPointSmoke
open FormalProof4FHE.HasteBoots
open NativeFields (Goldilocks goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject roots)
noncomputable section

def phase (n : ℕ) := TypedFieldVector.phase goldilocksModulus 3 7 n child NativeLookupEquality.pointLabel

/-- Consecutive extension triples, not transposed coefficient lanes. -/
theorem first_triple : goldilocksBasis.equivFun
    (GoldEqualityPointLaw.assemble 2 ![0,1,2,3,4,5] 0) = ![0,1,2] := by
  rw [GoldEqualityPointLaw.assemble_apply,LinearEquiv.apply_symm_apply]
  decide +kernel

theorem second_triple : goldilocksBasis.equivFun
    (GoldEqualityPointLaw.assemble 2 ![0,1,2,3,4,5] 1) = ![3,4,5] := by
  rw [GoldEqualityPointLaw.assemble_apply,LinearEquiv.apply_symm_apply]
  decide +kernel

theorem partial_vector_suspended : GoldEqualityPointLaw.values 1 2 (phase 1) worldZero = none := by
  have raw : NativeFieldVectorLaw.values goldilocksModulus 2 3 (phase 1) worldZero = none := by decide +kernel
  unfold GoldEqualityPointLaw.values
  rw [raw]
  rfl

theorem rejected_vector_suspended : GoldEqualityPointLaw.values 1 5 (phase 1) worldReject = none := by
  have raw : NativeFieldVectorLaw.values goldilocksModulus 5 3 (phase 1) worldReject = none := by decide +kernel
  unfold GoldEqualityPointLaw.values
  rw [raw]
  rfl

theorem zero_vector_complete : GoldEqualityPointLaw.values 0 0 (phase 0) worldReject = some Fin.elim0 := by
  unfold GoldEqualityPointLaw.values NativeFieldVectorLaw.values
  simp only [NativeFieldVector.execute,NativeFieldVector.initial,NativeFieldVectorValues.project,ite_true,
    Option.map_some,Option.some.injEq]
  funext i
  exact Fin.elim0 i

def equality := (NativeLookupEquality.execute goldilocksBasis 7 8
  (NativeLookupEquality.initial 1 child roots (by decide +kernel)) worldZero).1

theorem both_points_completed : equality.draws.length = 2 ∧ equality.remaining = 0 ∧ equality.active = none := by
  decide +kernel

/-- The second original collector input retains the first draw's receipt. -/
theorem distinct_original_inputs :
    (equality.draws[0]'(by decide +kernel)).coefficients.phase.pending.input ≠
      (equality.draws[1]'(by decide +kernel)).coefficients.phase.pending.input := by decide +kernel

end
end HasteBootsGoldEqualityPointSmoke
