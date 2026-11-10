module
public import FormalProof4FHE.HasteBoots.PackedPBSCoverage
public import FormalProof4FHETest.HasteBootsCanonicalKeySwitchSmoke
@[expose] public section

open FormalProof4FHE.HasteBoots
namespace HasteBootsPackedKeySwitchStageSmoke
open HasteBootsCanonicalKeySwitchSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def stage : PackedKeySwitchStage.Stage 17 2 3 3 2 := ⟨tables,address⟩
theorem checked : PackedKeySwitchStage.Holds (2 : ZMod 17) 2 key (acc false) trace.increment stage :=
  ⟨relation,digits,keys,result⟩

example : trace.increment = CanonicalKeySwitch.increment 2 key (acc false) :=
  PackedKeySwitchStage.increment_of_holds 2 HasteBootsHadamardBlindRotationSmoke.primitive
    2 key (acc false) trace.increment stage checked

-- A different final sum can pass the public extraction while the authentic
-- packed key product remains unchanged. The result-source binding rejects it.
def foreignOutput : NativePublic.Ciphertext 17 3 :=
  NativeKeySwitch.extract shape (NativeKeySwitch.initial acc)

example : PBSHadamard.Relation (KeySwitchExtraction.tables (c := 1) (lanes := 1)
    (by decide +kernel : 0 < 3) acc 0 foreignOutput) := by
  unfold PBSHadamard.Relation
  decide +kernel

example : ¬PackedKeySwitchStage.Holds (2 : ZMod 17) 2 key (acc false) 0 stage := by
  intro falseStage
  have selected := falseStage.result false
  have atZero := congrFun selected (0 : Fin 4)
  change (0 : ZMod 17) = 3 at atZero
  exact (by decide +kernel : (0 : ZMod 17) ≠ 3) atZero

example : foreignOutput ≠ output := by
  intro same
  have masks := congrArg (fun x : NativePublic.Ciphertext 17 3 => x.mask 0) same
  change (0 : ZMod 17) = 3 at masks
  exact (by decide +kernel : (0 : ZMod 17) ≠ 3) masks

-- Replacing the original public key by a zero key is likewise observable;
-- satisfaction of the packed polynomial identity alone does not bind a key.
example : ¬PackedKeySwitchStage.Holds (2 : ZMod 17) 2 (0 : NativeKeySwitch.Key 17 4 3)
    (acc false) trace.increment stage := by
  intro falseStage
  have selected := falseStage.keys false (0 : Fin 3)
  have atZero := congrFun selected (0 : Fin 4)
  change (0 : ZMod 17) = 1 at atZero
  exact (by decide +kernel : (0 : ZMod 17) ≠ 1) atZero

end
end HasteBootsPackedKeySwitchStageSmoke
