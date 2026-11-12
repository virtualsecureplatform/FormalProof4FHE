module
import all FormalProof4FHE.HasteBoots.CanonicalPairedIdentityWork
import all FormalProof4FHETest.HasteBootsCanonicalScalarSmoke
import all FormalProof4FHETest.HasteBootsLookupViewSumSmoke

namespace HasteBootsCanonicalSumSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

theorem absent {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : NativeRootMessage.Digest)
    (none : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run = .none) :
    ¬∃ input ordinal, CanonicalSumAttainableEvent.Event program position input ordinal dummy world := by
  rintro ⟨input,ordinal,⟨packet,_⟩⟩
  have selected := packet.classed.val.first.selected
  rw [packet.classed.val.first_position,none] at selected
  cases selected

theorem pure_empty {A : Type} (value : A) (world : World) (dummy : NativeRootMessage.Digest) :
    ¬CanonicalSumLifetime.Event (Program.pure value) dummy world := by
  rintro ⟨position,input,ordinal,event⟩
  have none : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position (Program.pure value) world).run = .none := by
    cases position <;> rfl
  exact absent _ position world dummy none ⟨input,ordinal,event⟩

theorem coin_only (dummy : NativeRootMessage.Digest) :
    ¬PrivateCoinCanonicalSumProbability.Event PrivateCoinScalarSmoke.code [] (fun _ => []) dummy 2
      (PrivateCoinScalarSmoke.changed,worldZero) := pure_empty _ worldZero dummy

theorem repeat_excluded (dummy : NativeRootMessage.Digest) :
    ¬∃ input ordinal, CanonicalSumAttainableEvent.Event HasteBootsCanonicalScalarSmoke.repeated 1 input ordinal dummy worldZero :=
  absent _ 1 worldZero dummy (by decide +kernel)

theorem empty_excluded (dummy : NativeRootMessage.Digest) :
    ¬∃ input ordinal, CanonicalSumAttainableEvent.Event HasteBootsCanonicalScalarSmoke.emptyFirst 0 input ordinal dummy worldZero :=
  absent _ 0 worldZero dummy (by decide +kernel)

-- Equal dimensions alone cannot identify the source-derived sum test.
def leftHelper (_ : MatrixFold.Cube 1) : Fin 4 → NativeFields.Goldilocks :=
  PaddedExtension.encode (padding := 1) NativeExtensionFields.goldilocksBasis (0 : NativeExtensionFields.Goldilocks3)
def rightHelper (_ : MatrixFold.Cube 1) : Fin 4 → NativeFields.Goldilocks :=
  PaddedExtension.encode (padding := 1) NativeExtensionFields.goldilocksBasis (1 : NativeExtensionFields.Goldilocks3)

theorem dimensions_do_not_fix_tables : LookupViewSumReduction.tables (helperPadding := 1) leftHelper ≠
    LookupViewSumReduction.tables (helperPadding := 1) rightHelper := by
  intro same
  have value := congrFun (congrFun same ExtensionLookupIdentity.Factor.helper) (false,())
  change PaddedExtension.decode (padding := 1) NativeExtensionFields.goldilocksBasis
    (PaddedExtension.encode (padding := 1) NativeExtensionFields.goldilocksBasis (0 : NativeExtensionFields.Goldilocks3)) =
      PaddedExtension.decode (padding := 1) NativeExtensionFields.goldilocksBasis
        (PaddedExtension.encode (padding := 1) NativeExtensionFields.goldilocksBasis (1 : NativeExtensionFields.Goldilocks3)) at value
  rw [PaddedExtension.decode_encode,PaddedExtension.decode_encode] at value
  exact zero_ne_one value

-- Original native even-slot healing remains an actual causal event.
theorem native_even_healing : HasteBootsLookupViewSumSmoke.Healing := HasteBootsLookupViewSumSmoke.actual_even_slot_healing

end
end HasteBootsCanonicalSumSmoke
