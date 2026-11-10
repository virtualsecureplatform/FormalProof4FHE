module
public import FormalProof4FHE.HasteBoots.BlindRotationNTT
public import FormalProof4FHE.HasteBoots.PBSHadamard
@[expose] public section

/-! Deterministic application meaning of the complete-PBS Hadamard relation.
Both ciphertext halves and every gadget level occur in native half-major order.
Truthful NTT relations turn this identity into the coefficient external product.
Native source/key layout and actual accepted-stage coverage remain separate. -/
namespace FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
open scoped BigOperators
open NativeBlindRotation (Poly Cipher Control digit externalProduct)
noncomputable section

def digitIndex {levels : ℕ} (entry : Bool × Fin levels) : Fin (2*levels) :=
  ⟨(if entry.1 then levels else 0)+entry.2.val, by have := entry.2.isLt; split <;> omega⟩

theorem digitIndex_injective (levels : ℕ) : Function.Injective (digitIndex (levels := levels)) := by
  rintro ⟨first,index⟩ ⟨second,other⟩ equal
  have values := congrArg Fin.val equal
  have bound := index.isLt
  have otherBound := other.isLt
  change (if first then levels else 0)+index.val = (if second then levels else 0)+other.val at values
  cases first <;> cases second <;> simp only [Bool.false_eq_true, ite_false, ite_true, zero_add] at values
  · exact Prod.ext rfl (Fin.ext values)
  · omega
  · omega
  · have same : index = other := Fin.ext (Nat.add_left_cancel values)
    subst other
    rfl

def digitEquiv (levels : ℕ) : (Bool × Fin levels) ≃ Fin (2*levels) :=
  Equiv.ofBijective digitIndex ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨digitIndex_injective levels, by simp⟩)

variable {q log levels cells width : ℕ} [Fact q.Prime]

/-- Select the same complete polynomial's output points from a packed table.
The address may also fix a round/ciphertext half in a larger native table. -/
def project (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (factor : PBSHadamard.Factor (2*levels)) : Poly q (2^log) :=
  fun index => tables factor (address index).1 (address index).2

theorem projected_identity
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables) :
    project tables address (.inr ()) = ∑ source : Bool, ∑ level : Fin levels,
      project tables address (.inl (digitIndex (source,level),false)) * project tables address (.inl (digitIndex (source,level),true)) := by
  funext index
  have identity := relation (address index).1 (address index).2
  rw [← (digitEquiv levels).sum_comp] at identity
  simpa only [project, Fintype.sum_prod_type, Finset.sum_apply, Pi.mul_apply, digitEquiv, Equiv.ofBijective_apply] using identity

/-- The three source families are identified by actual NTT equalities. These
are stage relations, not an assumption that the native transform is correct. -/
theorem externalProduct_half (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (input output : Cipher q (2^log)) (half : Bool)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (digits : ∀ source level, BlindRotationNTT.transform log psi (digit bits level (input source)) =
      project tables address (.inl (digitIndex (source,level),false)))
    (keys : ∀ source level, BlindRotationNTT.transform log psi (control source level half) =
      project tables address (.inl (digitIndex (source,level),true)))
    (result : BlindRotationNTT.transform log psi (output half) = project tables address (.inr ())) :
    output half = externalProduct bits control input half := by
  apply BlindRotationNTT.transform_injective log psi primitive
  rw [BlindRotationNTT.externalProduct_transform log psi primitive]
  rw [result, projected_identity tables address relation]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro level _
  rw [digits, keys]

/-- Both output halves use their own original table addresses and public key
rows; every digit source and gadget level is retained. -/
theorem externalProduct_of_relations (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (input output : Cipher q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (digits : ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (input source)) =
      project tables (address half) (.inl (digitIndex (source,level),false)))
    (keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
      project tables (address half) (.inl (digitIndex (source,level),true)))
    (result : ∀ half, BlindRotationNTT.transform log psi (output half) = project tables (address half) (.inr ())) :
    output = externalProduct bits control input := by
  funext half
  exact externalProduct_half psi primitive bits control input output half tables (address half) relation
    (digits half) (keys half) (result half)

/-- A false external product must violate a concrete arithmetic-stage source
relation. No probability/Fiat--Shamir soundness premise is hidden here. -/
theorem wrong_external_coverage (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits : ℕ)
    (control : Control q (2^log) levels) (input output : Cipher q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (wrong : output ≠ externalProduct bits control input) :
    ¬PBSHadamard.Relation tables ∨
      (∃ half source level, BlindRotationNTT.transform log psi (digit bits level (input source)) ≠
        project tables (address half) (.inl (digitIndex (source,level),false))) ∨
      (∃ half source level, BlindRotationNTT.transform log psi (control source level half) ≠
        project tables (address half) (.inl (digitIndex (source,level),true))) ∨
      (∃ half, BlindRotationNTT.transform log psi (output half) ≠ project tables (address half) (.inr ())) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (externalProduct_of_relations psi primitive bits control input output tables address
    absent.1 absent.2.1 absent.2.2.1 absent.2.2.2)

/-- The external-product stage supplies the missing coefficient-domain
constraint in the independently defined reference blind-rotation step. Other
stage identities (monomial action, subtraction and accumulation) are explicit. -/
theorem validStep_of_relations (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits exponent : ℕ)
    (control : Control q (2^log) levels) (acc : Cipher q (2^log)) (trace : NativeBlindRotation.StepTrace q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (rotated : trace.product = fun half => NativeBlindRotation.rotate exponent (acc half))
    (difference : trace.difference = trace.product-acc) (combined : trace.output = acc+trace.external)
    (relation : PBSHadamard.Relation tables)
    (digits : ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (trace.difference source)) =
      project tables (address half) (.inl (digitIndex (source,level),false)))
    (keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
      project tables (address half) (.inl (digitIndex (source,level),true)))
    (result : ∀ half, BlindRotationNTT.transform log psi (trace.external half) = project tables (address half) (.inr ())) :
    NativeBlindRotation.ValidStep bits control exponent acc trace :=
  ⟨rotated,difference,externalProduct_of_relations psi primitive bits control trace.difference trace.external
    tables address relation digits keys result,combined⟩

end
end FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
