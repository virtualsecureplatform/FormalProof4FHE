module
import all FormalProof4FHE.HasteBoots.EqualityCandidateKernel

namespace HasteBootsEqualityResidualSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
noncomputable section

def world : World := fun coordinate => match coordinate with
  | .inl (_,position) => ⟨position % 17,(Nat.mod_lt _ (by decide)).trans (by decide)⟩
  | .inr _ => 0

def phaseA : NativeTranscript.FieldPhase := ⟨⟨[],fun _ => 0⟩,[],[]⟩
def phaseB : NativeTranscript.FieldPhase := ⟨⟨[],fun _ => 1⟩,[99],[]⟩
def shifted : NativeTranscript.FieldPhase := {phaseB with consumed := [42]}

theorem original_coefficients : NativeFieldVectorLaw.values 17 2 2 phaseA world = some ![0,1] := by decide +kernel

theorem metadata_does_not_change_values : NativeFieldVectorLaw.values 17 2 2 phaseB world = some ![0,1] := by decide +kernel

theorem cursor_changes_values : NativeFieldVectorLaw.values 17 2 2 shifted world = some ![1,2] := by decide +kernel

def helpers (_ : MatrixFold.Cube 2) := PaddedExtension.encode (padding := 5) goldilocksBasis (0 : Goldilocks3)
def sources (_ : Fin 1) (_ : MatrixFold.Cube 0) (_ : Fin 4) : NativeFields.Goldilocks := 0

theorem inactive_residual : EqualityResidualCongruence.packed (padding := 1) (rows := 0) (helperPadding := 5) (columns := 1)
    (by decide +kernel) NativeGoldLookup.one NativeGoldLookup.zero 0 sources helpers (false,(false,())) = 0 := by
  simp [EqualityResidualCongruence.packed,helpers,ReciprocalMask.residual]

theorem active_residual : EqualityResidualCongruence.packed (padding := 1) (rows := 0) (helperPadding := 5) (columns := 1)
    (by decide +kernel) NativeGoldLookup.one NativeGoldLookup.zero 4 sources helpers (false,(false,())) = -1 := by
  have active : (FlatMatrixFold.index (NativeScalarQueryShape.laneBits 4) (false,(false,()))).val < 4 := by decide +kernel
  simp [EqualityResidualCongruence.packed,helpers,ReciprocalMask.residual,active]

end
end HasteBootsEqualityResidualSmoke
