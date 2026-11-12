module
import all FormalProof4FHE.HasteBoots.CallerReciprocalKernel

namespace HasteBootsReciprocalKernelSmoke
open FormalProof4FHE.HasteBoots
open NativeExtensionFields (Goldilocks3)
noncomputable section

/-- Two repeated missing source values can pass at an allowed offset. This
exercises multiplicity and the native plus sign in the reciprocal numerator. -/
theorem repeated_source_root :
    LookupReciprocalKernel.test (fun _ : Fin 2 => (0 : Goldilocks3))
      (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) (-2) ∧
    LookupPairChallengeBounds.Domain (fun _ : Fin 1 => (1 : Goldilocks3)) (-2) := by
  constructor
  · constructor
    · exact ⟨0,fun _ => zero_ne_one⟩
    · norm_num [ReciprocalPolynomial.numerator,ReciprocalPolynomial.denominator,
        ReciprocalPolynomial.tableNumerator,ReciprocalPolynomial.cofactor,
        ReciprocalPolynomial.factor,Fin.prod_univ_succ,Fin.sum_univ_succ,Polynomial.derivative_mul]
  · have two : (2 : Goldilocks3) ≠ 0 := by
      intro zero
      have base : (2 : NativeFields.Goldilocks) ≠ 0 := by decide +kernel
      apply base
      apply (algebraMap NativeFields.Goldilocks Goldilocks3).injective
      rw [map_ofNat,map_zero]
      exact zero
    constructor <;> norm_num [LookupPairChallengeBounds.Domain,two]

/-- The primitive root event conservatively includes a public pole. Native
acceptance must retain its separate domain guard. -/
theorem public_pole_is_only_overapproximation :
    LookupReciprocalKernel.test (fun _ : Fin 1 => (0 : Goldilocks3))
      (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 0) (-1) ∧
    ¬LookupPairChallengeBounds.Domain (fun _ : Fin 1 => (1 : Goldilocks3)) (-1) := by
  constructor
  · constructor
    · exact ⟨0,fun _ => zero_ne_one⟩
    · norm_num [ReciprocalPolynomial.numerator,ReciprocalPolynomial.denominator,
        ReciprocalPolynomial.tableNumerator,ReciprocalPolynomial.cofactor,
        ReciprocalPolynomial.factor,Fin.prod_univ_succ,Fin.sum_univ_succ]
  · intro allowed
    have := allowed.2 0
    simp at this

/-- An empty active source family contributes no reciprocal-miss event,
including the zero-degree boundary. -/
theorem empty_source_no_event (input : InputIndexedOracle.Input)
    {size : ℕ} (table multiplicities : Fin size → Goldilocks3) (world : InputIndexedOracle.World) :
    ¬LookupReciprocalKernel.Event input (Fin.elim0 : Fin 0 → Goldilocks3) table multiplicities world := by
  rintro ⟨budget,occurred⟩
  cases found : GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase input) world with
  | none => rw [found] at occurred; exact occurred.elim
  | some r =>
    rw [found] at occurred
    obtain ⟨index,_⟩ := occurred.1
    exact Fin.elim0 index

end
end HasteBootsReciprocalKernelSmoke
