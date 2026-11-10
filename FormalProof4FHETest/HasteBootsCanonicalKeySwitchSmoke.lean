module
import FormalProof4FHE.HasteBoots.CanonicalPBS
import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
import FormalProof4FHE.HasteBoots.RadixWitness
import FormalProof4FHETest.HasteBootsHadamardBlindRotationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsHadamardBlindRotationSmoke (polynomial primitive)
open NativeBlindRotation (Cipher digit)
open scoped Matrix
namespace HasteBootsCanonicalKeySwitchSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def key : NativeKeySwitch.Key 17 4 3 := fun level half =>
  if level.val = 0 then (if half then polynomial 2 0 0 0 else polynomial 1 0 0 0)
  else if level.val = 2 then (if half then polynomial 4 0 0 0 else polynomial 3 0 0 0) else 0
def acc : Cipher 17 4 := fun half => if half then polynomial 5 0 0 0 else polynomial 1 0 0 0
def trace := CanonicalKeySwitch.makeTrace 2 key acc
def output : NativePublic.Ciphertext 17 3 := ⟨![3,0,0],9⟩
theorem shape : 3 ≤ 4 := by decide +kernel

-- The native negative-mask digits are [0,0,1], not the negation of [1,0,0].
example : (digit 2 (0 : Fin 3) (-(acc false))) 0 = 0 := by decide +kernel
example : (digit 2 (2 : Fin 3) (-(acc false))) 0 = 1 := by decide +kernel
example : output = NativeKeySwitch.extract shape (CanonicalKeySwitch.switch 2 key acc) := by
  apply CanonicalKeySwitch.ciphertext_ext
  · funext i
    fin_cases i <;> decide +kernel
  · decide +kernel
example : (NativeKeySwitch.extract shape (NativeKeySwitch.switch 2 key acc)).mask 0 = 16 ∧
    (NativeKeySwitch.extract shape (NativeKeySwitch.switch 2 key acc)).body = 3 := by decide +kernel
example : CanonicalKeySwitch.switch 2 key acc ≠ NativeKeySwitch.switch 2 key acc := by decide +kernel

def address (half : Bool) (index : Fin 4) : MatrixFold.Cube 3 × Fin 2 :=
  ((half,(FlatMatrixFold.index 2).symm index),⟨index.val%2, Nat.mod_lt _ (by decide +kernel)⟩)
def tables : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 3) 3 2 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (level,isKey) => if isKey then BlindRotationNTT.transform 2 2 (key level cell.1) index
      else BlindRotationNTT.transform 2 2 (digit 2 level (-(acc false))) index
    | .inr _ => BlindRotationNTT.transform 2 2 (trace.increment cell.1) index

theorem relation : PBSHadamard.Relation tables := by
  unfold PBSHadamard.Relation
  decide +kernel

-- The canonical decomposition is of the negative original mask.
def coefficientAddress (index : Fin 4) : MatrixFold.Cube 2 × Fin 1 := ((FlatMatrixFold.index 2).symm index,0)
def registry : DecompositionBlindRotation.Registry 17 3 2 1 :=
  RadixWitness.tables 17 4 3 (fun cell _ => -(acc false (FlatMatrixFold.index 2 cell)))
theorem source : DecompositionBlindRotation.project (log := 2) registry coefficientAddress DecompositionLinear.input = -(acc false) := by
  funext index
  simp only [DecompositionBlindRotation.project,registry,RadixWitness.tables_input,coefficientAddress,Equiv.apply_symm_apply,Pi.neg_apply]
theorem linear : DecompositionLinear.Relation (4 : ZMod 17) registry :=
  RadixWitness.tables_valid (by decide +kernel) (by decide +kernel) _
theorem lookup (index : Fin 4) : RadixCanonicity.LookupAt 17 4 registry (coefficientAddress index).1 (coefficientAddress index).2 :=
  RadixWitness.tables_lookup (by decide +kernel) _ _ _
theorem column_binding : ∀ half (level : Fin 3), BlindRotationNTT.transform 2 (2 : ZMod 17)
    (DecompositionBlindRotation.project (log := 2) registry coefficientAddress (DecompositionLinear.digit level)) =
    CanonicalKeySwitch.project (log := 2) tables (address half) (.inl (level,false)) := by decide +kernel

theorem digits : ∀ half (level : Fin 3), BlindRotationNTT.transform 2 (2 : ZMod 17) (digit 2 level (-(acc false))) =
    CanonicalKeySwitch.project (log := 2) tables (address half) (.inl (level,false)) := by
  intro half level
  have canonical := DecompositionBlindRotation.digit_of_constraints (log := 2) (levels := 3)
    2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (show 3 ≤ 3 by decide +kernel)
    registry coefficientAddress (-(acc false)) source linear lookup level
  exact (congrArg (BlindRotationNTT.transform 2 (2 : ZMod 17)) canonical).symm.trans (column_binding half level)
theorem keys : ∀ half level, BlindRotationNTT.transform 2 (2 : ZMod 17) (key level half) =
    CanonicalKeySwitch.project (log := 2) tables (address half) (.inl (level,true)) := by decide +kernel
theorem result : ∀ half, BlindRotationNTT.transform 2 (2 : ZMod 17) (trace.increment half) =
    CanonicalKeySwitch.project (log := 2) tables (address half) (.inr ()) := by decide +kernel
theorem product : trace.increment = CanonicalKeySwitch.increment 2 key (acc false) :=
  CanonicalKeySwitch.increment_of_relations (log := 2) 2 primitive 2 key (acc false) trace.increment tables address relation digits keys result
theorem extraction : CanonicalKeySwitch.Extraction shape acc trace.increment output := by
  unfold CanonicalKeySwitch.Extraction
  decide +kernel
example : CanonicalKeySwitch.Valid 2 key shape acc trace output :=
  CanonicalKeySwitch.valid_of_extraction 2 key shape acc trace output product rfl extraction
example : output = NativeKeySwitch.extract shape (CanonicalKeySwitch.switch 2 key acc) :=
  CanonicalKeySwitch.valid_output 2 key shape acc trace output
    (CanonicalKeySwitch.valid_of_extraction 2 key shape acc trace output product rfl extraction)

-- Every selected public coordinate matters, including the last retained mask.
def badOutput : NativePublic.Ciphertext 17 3 := ⟨![3,0,1],9⟩
example : ¬CanonicalKeySwitch.Extraction shape acc trace.increment badOutput := by
  unfold CanonicalKeySwitch.Extraction
  decide +kernel
-- Extraction alone does not certify unselected coefficients or the key product.
def hidden : Cipher 17 4 := fun half index => if half = false ∧ index.val = 1 then trace.increment half index+1 else trace.increment half index
example : CanonicalKeySwitch.Extraction shape acc hidden output := by
  unfold CanonicalKeySwitch.Extraction
  decide +kernel
example : hidden ≠ CanonicalKeySwitch.increment 2 key (acc false) := by decide +kernel

-- Corrected full PBS reference: original public inputs, bias and final stage.
def publicKey : NativePBS.PublicKey 17 4 1 1 3 :=
  ⟨fun _ => HasteBootsHadamardBlindRotationSmoke.control,key⟩
def inputs : NativePBS.Inputs 17 1 := (⟨![4],1⟩,⟨![1],2⟩)
example : CanonicalPBS.Relation 2 2 1 (show 1 ≤ 4 by decide +kernel) publicKey inputs
    (CanonicalPBS.evaluate 2 2 1 (by decide +kernel) publicKey inputs) (CanonicalPBS.makeTrace 2 2 1 publicKey inputs) :=
  CanonicalPBS.makeTrace_valid 2 2 1 _ publicKey inputs
example : (CanonicalPBS.makeTrace 2 2 1 publicKey inputs).finalStage.switched =
    CanonicalKeySwitch.switch 2 key (NativePBS.bias (CanonicalPBS.makeTrace 2 2 1 publicKey inputs).accumulator) := rfl
end
end HasteBootsCanonicalKeySwitchSmoke
