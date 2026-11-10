module
public import FormalProof4FHE.HasteBoots.CanonicalKeySwitch
@[expose] public section

namespace FormalProof4FHE.HasteBoots.PackedKeySwitchStage
open NativeBlindRotation
noncomputable section
variable {q log levels cells width : ℕ} [Fact q.Prime]

/-- Independent packing geometry for the final signed key product. -/
structure Stage (q log levels cells width : ℕ) where
  tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor levels) cells width
  address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width

/-- Every digit, original key row and result is bound to its full NTT source. -/
structure Holds (psi : ZMod q) (bits : ℕ) (key : NativeKeySwitch.Key q (2^log) levels)
    (mask : Poly q (2^log)) (result : Cipher q (2^log)) (stage : Stage q log levels cells width) : Prop where
  relation : PBSHadamard.Relation stage.tables
  digits : ∀ half level, BlindRotationNTT.transform log psi (digit bits level (-mask)) =
    CanonicalKeySwitch.project stage.tables (stage.address half) (.inl (level,false))
  keys : ∀ half level, BlindRotationNTT.transform log psi (key level half) =
    CanonicalKeySwitch.project stage.tables (stage.address half) (.inl (level,true))
  result : ∀ half, BlindRotationNTT.transform log psi (result half) =
    CanonicalKeySwitch.project stage.tables (stage.address half) (.inr ())

theorem increment_of_holds (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (bits : ℕ) (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log))
    (result : Cipher q (2^log)) (stage : Stage q log levels cells width)
    (checked : Holds psi bits key mask result stage) : result = CanonicalKeySwitch.increment bits key mask :=
  CanonicalKeySwitch.increment_of_relations psi primitive bits key mask result stage.tables stage.address
    checked.relation checked.digits checked.keys checked.result

/-- Exposes the four source failures rather than treating key-switch validity
as a certificate. In particular, relation satisfaction alone is insufficient. -/
theorem false_stage_coverage (psi : ZMod q) (bits : ℕ)
    (key : NativeKeySwitch.Key q (2^log) levels) (mask : Poly q (2^log))
    (result : Cipher q (2^log)) (stage : Stage q log levels cells width)
    (failed : ¬Holds psi bits key mask result stage) :
    ¬PBSHadamard.Relation stage.tables ∨
    (∃ half level, BlindRotationNTT.transform log psi (digit bits level (-mask)) ≠
      CanonicalKeySwitch.project stage.tables (stage.address half) (.inl (level,false))) ∨
    (∃ half level, BlindRotationNTT.transform log psi (key level half) ≠
      CanonicalKeySwitch.project stage.tables (stage.address half) (.inl (level,true))) ∨
    (∃ half, BlindRotationNTT.transform log psi (result half) ≠
      CanonicalKeySwitch.project stage.tables (stage.address half) (.inr ())) := by
  classical
  by_contra absent
  push Not at absent
  exact failed ⟨absent.1,absent.2.1,absent.2.2.1,absent.2.2.2⟩

end
end FormalProof4FHE.HasteBoots.PackedKeySwitchStage
