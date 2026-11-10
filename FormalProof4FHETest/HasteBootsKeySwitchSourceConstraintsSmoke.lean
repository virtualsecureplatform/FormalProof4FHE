module
public import FormalProof4FHE.HasteBoots.KeySwitchSourceConstraints
public import FormalProof4FHETest.HasteBootsCanonicalKeySwitchSmoke
@[expose] public section
open FormalProof4FHE.HasteBoots
open NativeBlindRotation
namespace HasteBootsKeySwitchSourceConstraintsSmoke
open HasteBootsCanonicalKeySwitchSmoke (key acc trace registry coefficientAddress source linear lookup shape)
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
theorem length : 2^1*2 = 2^2 := by decide +kernel

def coefficients (level : Fin 3) : PackedNTTBinding.Table 17 2 2 :=
  PackedNTTBinding.pack (r := 1) length (fun _ =>
    DecompositionBlindRotation.project registry coefficientAddress (DecompositionLinear.digit level))
def resultCoefficients : PackedNTTBinding.Table 17 2 2 :=
  PackedNTTBinding.pack (r := 1) length (fun row => trace.increment row.1)
def tables : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 3) 2 2 := fun factor =>
  PackedNTTBinding.pack (r := 1) length (fun row => match factor with
    | .inl (level,false) => BlindRotationNTT.transform 2 2 (digit 2 level (-(acc false)))
    | .inl (level,true) => BlindRotationNTT.transform 2 2 (key level row.1)
    | .inr _ => BlindRotationNTT.transform 2 2 (trace.increment row.1))

theorem digitSources : ∀ half (level : Fin 3), PackedNTTBinding.row length (coefficients level) (half,()) =
    DecompositionBlindRotation.project registry coefficientAddress (DecompositionLinear.digit level) := by
  intro half level
  exact PackedNTTBinding.row_pack (r := 1) length _ (half,())
theorem digitTransforms : ∀ level, PackedNTT.Relation length (2 : ZMod 17)
    (NTTCompression.sourceRows 1 1 (coefficients level))
    (NTTCompression.sourceRows 1 1 (tables (.inl (level,false)))) := by
  intro level
  unfold PackedNTT.Relation
  fin_cases level <;> decide +kernel

theorem resultSource : ∀ half, PackedNTTBinding.row length resultCoefficients (half,()) = trace.increment half := by
  intro half
  exact PackedNTTBinding.row_pack (r := 1) length _ (half,())
theorem resultTransform : PackedNTT.Relation length (2 : ZMod 17)
    (NTTCompression.sourceRows 1 1 resultCoefficients) (NTTCompression.sourceRows 1 1 (tables (.inr ()))) := by
  unfold PackedNTT.Relation
  decide +kernel

theorem keys : ∀ half level, BlindRotationNTT.transform 2 (2 : ZMod 17) (key level half) =
    PackedNTTBinding.row length (tables (.inl (level,true))) (half,()) := by
  intro half level
  exact (PackedNTTBinding.row_pack (r := 1) length (fun row => BlindRotationNTT.transform 2 (2 : ZMod 17) (key level row.1)) (half,())).symm

theorem relation : PBSHadamard.Relation tables := by
  unfold PBSHadamard.Relation
  decide +kernel

theorem checked : PackedKeySwitchStage.Holds (2 : ZMod 17) 2 key (acc false) trace.increment
    (KeySwitchSourceConstraints.stage length tables) :=
  KeySwitchSourceConstraints.holds_of_constraints length 2 HasteBootsHadamardBlindRotationSmoke.primitive
    2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel : 3 ≤ 3)
    registry coefficientAddress key (acc false) trace.increment source linear lookup coefficients resultCoefficients
    tables digitSources digitTransforms resultSource resultTransform keys relation

example : trace.increment = CanonicalKeySwitch.increment 2 key (acc false) :=
  PackedKeySwitchStage.increment_of_holds 2 HasteBootsHadamardBlindRotationSmoke.primitive
    2 key (acc false) trace.increment (KeySwitchSourceConstraints.stage length tables) checked

-- The final coefficient of the body retains both its high row and nonzero lane.
example : PackedNTTBinding.address (c := 1) (b := 2) (log := 2) (r := 1) length (true,()) (3 : Fin 4) = ((true,(true,())),(1 : Fin 2)) := by
  rfl

-- Swapping nonce/body evaluation rows is detected by the original NTT relation.
def swappedResult : PackedNTTBinding.Table 17 2 2 :=
  PackedNTTBinding.pack (r := 1) length (fun row => BlindRotationNTT.transform 2 2 (trace.increment (!row.1)))
example : ¬PackedNTT.Relation length (2 : ZMod 17)
    (NTTCompression.sourceRows 1 1 resultCoefficients) (NTTCompression.sourceRows 1 1 swappedResult) := by
  unfold PackedNTT.Relation
  decide +kernel

-- NTT correctness alone cannot turn positive-mask digits into native negative
-- digits. Both wrong-sign sources satisfy their transform relation, but the
-- original canonical-column source binding fails.
def positiveCoefficients : PackedNTTBinding.Table 17 2 2 :=
  PackedNTTBinding.pack (r := 1) length (fun _ => digit 2 (0 : Fin 3) (acc false))
def positiveEvaluations : PackedNTTBinding.Table 17 2 2 :=
  PackedNTTBinding.pack (r := 1) length (fun _ => BlindRotationNTT.transform 2 2 (digit 2 (0 : Fin 3) (acc false)))
example : PackedNTT.Relation length (2 : ZMod 17) (NTTCompression.sourceRows 1 1 positiveCoefficients)
    (NTTCompression.sourceRows 1 1 positiveEvaluations) := by
  unfold PackedNTT.Relation
  decide +kernel
example : PackedNTTBinding.row length positiveCoefficients (false,()) ≠
    DecompositionBlindRotation.project registry coefficientAddress (DecompositionLinear.digit (0 : Fin 3)) := by
  decide +kernel

end
end HasteBootsKeySwitchSourceConstraintsSmoke
