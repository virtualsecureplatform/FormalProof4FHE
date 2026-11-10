module
public import FormalProof4FHE.HasteBoots.BlindRotationMonomial
public import FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
@[expose] public section

/-! Deterministic meaning of the monomial Hadamard relation, composed with the
external-product relation. Public powers and NTT source equalities are explicit
obligations. Native public-plan evaluation, table layout and accepted-stage
soundness are not assumed proved by this arithmetic bridge. -/
namespace FormalProof4FHE.HasteBoots.PBSMonomialBlindRotation
open scoped BigOperators
open NativeBlindRotation (Poly Cipher Control digit rotate)
noncomputable section
variable {q log levels cells width : ℕ} [Fact q.Prime]

def project (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (factor : PBSHadamard.Factor 1) : Poly q (2^log) :=
  fun index => tables factor (address index).1 (address index).2

theorem projected_identity
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables) :
    project tables address (.inr ()) = project tables address (.inl (0,false)) * project tables address (.inl (0,true)) := by
  funext index
  simpa only [project, Fin.sum_univ_one, Pi.mul_apply] using relation (address index).1 (address index).2

theorem rotate_half (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (exponent : ℕ)
    (input output : Poly q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (address : Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (source : BlindRotationNTT.transform log psi input = project tables address (.inl (0,false)))
    (publicPowers : project tables address (.inl (0,true)) = BlindRotationMonomial.powers log psi exponent)
    (result : BlindRotationNTT.transform log psi output = project tables address (.inr ())) :
    output = rotate exponent input := by
  apply BlindRotationMonomial.rotate_of_pointwise log psi primitive input output exponent
  rw [result, projected_identity tables address relation, ← source, publicPowers]

theorem rotate_of_relations (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (exponent : ℕ)
    (input output : Cipher q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (source : ∀ half, BlindRotationNTT.transform log psi (input half) = project tables (address half) (.inl (0,false)))
    (publicPowers : ∀ half, project tables (address half) (.inl (0,true)) = BlindRotationMonomial.powers log psi exponent)
    (result : ∀ half, BlindRotationNTT.transform log psi (output half) = project tables (address half) (.inr ())) :
    output = fun half => rotate exponent (input half) := by
  funext half
  exact rotate_half psi primitive exponent (input half) (output half) tables (address half) relation
    (source half) (publicPowers half) (result half)

theorem wrong_rotation_coverage (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (exponent : ℕ)
    (input output : Cipher q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (wrong : output ≠ fun half => rotate exponent (input half)) :
    ¬PBSHadamard.Relation tables ∨
      (∃ half, BlindRotationNTT.transform log psi (input half) ≠ project tables (address half) (.inl (0,false))) ∨
      (∃ half, project tables (address half) (.inl (0,true)) ≠ BlindRotationMonomial.powers log psi exponent) ∨
      (∃ half, BlindRotationNTT.transform log psi (output half) ≠ project tables (address half) (.inr ())) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (rotate_of_relations psi primitive exponent input output tables address
    absent.1 absent.2.1 absent.2.2.1 absent.2.2.2)

/-- Both multiplication stages now supply their coefficient identities. The
accumulator's subtraction and addition constraints remain explicit premises. -/
theorem validStep_of_relations (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1))) (bits exponent : ℕ)
    (control : Control q (2^log) levels) (acc : Cipher q (2^log)) (trace : NativeBlindRotation.StepTrace q (2^log))
    (monomialTables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (monomialAddress : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (monomialRelation : PBSHadamard.Relation monomialTables)
    (monomialSource : ∀ half, BlindRotationNTT.transform log psi (acc half) = project monomialTables (monomialAddress half) (.inl (0,false)))
    (publicPowers : ∀ half, project monomialTables (monomialAddress half) (.inl (0,true)) = BlindRotationMonomial.powers log psi exponent)
    (monomialResult : ∀ half, BlindRotationNTT.transform log psi (trace.product half) = project monomialTables (monomialAddress half) (.inr ()))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width)
    (difference : trace.difference = trace.product-acc) (combined : trace.output = acc+trace.external)
    (relation : PBSHadamard.Relation tables)
    (digits : ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (trace.difference source)) =
      PBSHadamardBlindRotation.project tables (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)))
    (keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
      PBSHadamardBlindRotation.project tables (address half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)))
    (result : ∀ half, BlindRotationNTT.transform log psi (trace.external half) = PBSHadamardBlindRotation.project tables (address half) (.inr ())) :
    NativeBlindRotation.ValidStep bits control exponent acc trace :=
  PBSHadamardBlindRotation.validStep_of_relations psi primitive bits exponent control acc trace tables address
    (rotate_of_relations psi primitive exponent acc trace.product monomialTables monomialAddress
      monomialRelation monomialSource publicPowers monomialResult)
    difference combined relation digits keys result

end
end FormalProof4FHE.HasteBoots.PBSMonomialBlindRotation
