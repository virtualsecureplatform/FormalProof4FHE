module
import FormalProof4FHE.HasteBoots.KeySwitchExtractionSoundness
import FormalProof4FHETest.HasteBootsCanonicalKeySwitchSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsCanonicalKeySwitchSmoke (acc trace output badOutput shape hidden key product)
open OracleSpec OracleComp BinaryTree
open scoped Matrix
namespace HasteBootsKeySwitchExtractionSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _
local instance : SampleableType (Fin (2^1) → ZMod 17) := SampleableType.ofFintype _

theorem positive : 0 < 3 := by decide +kernel
example : KeySwitchExtraction.mask 17 4 3 false = ![1,0,1,1] := by decide +kernel
example : KeySwitchExtraction.mask 17 4 3 true = ![1,0,0,0] := by decide +kernel
example : KeySwitchExtraction.target positive acc output false = ![3,0,0,0] := by decide +kernel
example : KeySwitchExtraction.target positive acc output true = ![4,0,0,0] := by decide +kernel

def sources := KeySwitchExtraction.tables (c := 1) (lanes := 1) positive acc trace.increment output
-- Native role order: increment, public mask, public target.
example : sources (.inl (0,false)) (false,(true,())) 0 = 4 ∧
    sources (.inl (0,true)) (false,(true,())) 0 = 1 ∧
    sources (.inr ()) (false,(true,())) 0 = 4 := by decide +kernel
theorem relation : PBSHadamard.Relation sources := by
  unfold PBSHadamard.Relation
  decide +kernel
example : CanonicalKeySwitch.Extraction shape acc trace.increment output :=
  KeySwitchExtraction.extraction_of_relation (c := 1) (lanes := 1) shape positive acc trace.increment output relation
theorem output_correct : output = NativeKeySwitch.extract shape (CanonicalKeySwitch.switch 2 key acc) :=
  CanonicalKeySwitch.valid_output 2 key shape acc trace output
    (CanonicalKeySwitch.valid_of_extraction 2 key shape acc trace output product rfl
      (KeySwitchExtraction.extraction_of_relation (c := 1) (lanes := 1) shape positive acc trace.increment output relation))

-- Unselected coefficients need not vanish; this is partial sample extraction.
example : PBSHadamard.Relation (KeySwitchExtraction.tables (c := 1) (lanes := 1) positive acc HasteBootsCanonicalKeySwitchSmoke.hidden output) := by
  unfold PBSHadamard.Relation
  decide +kernel
theorem wrong_extraction : ¬CanonicalKeySwitch.Extraction shape acc trace.increment badOutput := by
  unfold CanonicalKeySwitch.Extraction
  decide +kernel
example : ¬PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
    (KeySwitchExtraction.tables (c := 1) (lanes := 1) positive acc trace.increment badOutput) :=
  KeySwitchExtraction.false_zero_relation (c := 1) (lanes := 1) shape positive acc trace.increment badOutput wrong_extraction

theorem wrong_output : badOutput ≠ NativeKeySwitch.extract shape (CanonicalKeySwitch.switch 2 key acc) := by
  intro equal
  have different : badOutput ≠ output := by
    intro same
    have coordinate := congrArg (fun cipher : NativePublic.Ciphertext 17 3 => cipher.mask (2 : Fin 3)) same
    exact (by decide +kernel : (1 : ZMod 17) ≠ 0) coordinate
  exact different (equal.trans output_correct.symm)

-- The numerical bound applies to every adaptive shared prover and arbitrary
-- retained cache state; it does not assume three authenticated openings.
example {Cfg Input Digest Memory Payload : Type}
    [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (hashShape : Cfg → Skeleton)
    (prover : KeySwitchExtractionSoundness.Prover 17 1 (2^1) Cfg Input Digest Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) hashShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy hashShape)
      (KeySwitchExtractionSoundness.program (q := 17) (c := 1) (lanes := 1)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) prover)).run state}[
      PackedZeroOracle.TruthfulResult (NativePackedInterpolation.nodes 17 (show 2*(2^1) ≤ 17 by decide +kernel))
        PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
        (KeySwitchExtraction.tables (c := 1) (lanes := 1) positive acc trace.increment badOutput) outcome.1] ≤ (131 : ENNReal)/289 := by
  have bound := KeySwitchExtractionSoundness.wrong_output_bound (q := 17) (c := 1) (lanes := 1)
    enc dummy hashShape (by decide +kernel) (by decide +kernel) (by decide +kernel) prover state
    2 key shape positive acc trace.increment badOutput product wrong_output
  calc
    _ ≤ KeySwitchExtractionSoundness.error 17 1 (2^1) := bound
    _ = _ := by
      norm_num [KeySwitchExtractionSoundness.error,div_eq_mul_inv,mul_pow,← ENNReal.inv_pow,← mul_assoc]
      rw [show (131 : ENNReal) = 1+49+81 by norm_num,add_mul,add_mul,one_mul]
end
end HasteBootsKeySwitchExtractionSmoke
