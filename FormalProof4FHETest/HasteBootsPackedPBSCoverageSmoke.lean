module
public import FormalProof4FHE.HasteBoots.PackedPBSCoverage
public import FormalProof4FHETest.HasteBootsCanonicalKeySwitchSmoke
@[expose] public section

open FormalProof4FHE.HasteBoots
open NativeBlindRotation
namespace HasteBootsPackedPBSCoverageSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

-- One original public round, with coinciding last and wrap boundaries.
def key := HasteBootsCanonicalKeySwitchSmoke.publicKey
def input : NativePBS.Inputs 17 1 := (⟨fun _ => 4,8⟩,⟨fun _ => 1,2⟩)
def front := NativePublic.frontend (n := 4) 1 input.1 input.2
def initial := NativePBS.initial front
def step := makeStep 3 (key.blind 0) (front.rotations 0) initial
def tables : AccumulatorTrace.Tables 17 4 1 :=
  ⟨fun _ => initial,fun _ => step.product,fun _ => step.difference,
    fun _ => step.external,fun _ => step.output⟩
def rounds : PackedAccumulatorTrace.Rounds 0 := ⟨1,by decide +kernel,by decide +kernel⟩
def difference := PackedAccumulatorTrace.pack (c := 1) (lanes := 1) (r := 0) (RingHom.id (ZMod 17)) tables.difference
def decompositionA := AccumulatorMatrixSoundness.copyHalf difference false
def decompositionB := AccumulatorMatrixSoundness.copyHalf difference true

theorem arithmetic : AccumulatorEndpointSoundness.FullHolds
    (PackedAccumulatorTrace.sources (c := 1) (lanes := 1) (r := 0) (RingHom.id (ZMod 17))
      rounds tables initial step.output decompositionA decompositionB) := by
  constructor
  · unfold AccumulatorMatrixSoundness.Holds
    decide +kernel
  · unfold AccumulatorEndpointSoundness.Holds
    decide +kernel

def address (width : ℕ) (positive : 0 < width) (half : Bool) (index : Fin 4) :
    MatrixFold.Cube 3 × Fin width :=
  ((half,(FlatMatrixFold.index 2).symm index),⟨index.val%width,Nat.mod_lt _ positive⟩)
def monomial : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 1) 3 3 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (_,false) => BlindRotationNTT.transform 2 2 (initial cell.1) index
    | .inl (_,true) => BlindRotationMonomial.powers 2 (2 : ZMod 17) (front.rotations 0) index
    | .inr _ => BlindRotationNTT.transform 2 2 (step.product cell.1) index

def external : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 2) 3 6 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (source,false) => BlindRotationNTT.transform 2 2
        (digit 3 (0 : Fin 1) (step.difference (source.val != 0))) index
    | .inl (source,true) => BlindRotationNTT.transform 2 2
        (key.blind 0 (source.val != 0) 0 cell.1) index
    | .inr _ => BlindRotationNTT.transform 2 2 (step.external cell.1) index

def stages (_ : Fin 1) : PackedBlindRotationTrace.Stages 17 2 1 3 3 3 6 :=
  ⟨monomial,address 3 (by decide +kernel),external,address 6 (by decide +kernel)⟩

theorem multiplication : PackedBlindRotationTrace.AllHolds (c := 1) (lanes := 1) (2 : ZMod 17) 3 rounds tables
    (fun i => (key.blind i,front.rotations i)) stages := by
  intro round
  fin_cases round
  constructor
  · unfold PBSHadamard.Relation
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold PBSHadamard.Relation
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def increment := CanonicalKeySwitch.increment 2 key.switching ((NativePBS.bias step.output) false)
def keyTables : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 3) 3 2 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (level,false) => BlindRotationNTT.transform 2 2
        (digit 2 level (-((NativePBS.bias step.output) false))) index
    | .inl (level,true) => BlindRotationNTT.transform 2 2 (key.switching level cell.1) index
    | .inr _ => BlindRotationNTT.transform 2 2 (increment cell.1) index

def keyStage : PackedKeySwitchStage.Stage 17 2 3 3 2 :=
  ⟨keyTables,address 2 (by decide +kernel)⟩
theorem switched : PackedKeySwitchStage.Holds (2 : ZMod 17) 2 key.switching
    ((NativePBS.bias step.output) false) increment keyStage := by
  constructor
  · unfold PBSHadamard.Relation
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def output : NativePublic.Ciphertext 17 1 := NativeKeySwitch.extract (by decide +kernel)
  (NativeKeySwitch.initial (NativePBS.bias step.output)+increment)
theorem extracted : PBSHadamard.Relation (KeySwitchExtraction.tables (c := 1) (lanes := 1)
    (by decide +kernel : 0 < 1) (NativePBS.bias step.output) increment output) := by
  unfold PBSHadamard.Relation
  decide +kernel

example : increment ≠ 0 := by decide +kernel
example : output.mask 0 = 1 ∧ output.body = 2 := by decide +kernel

-- All premises are independently checked on packed source tables. This uses
-- the actual public frontend, not an arbitrary initial accumulator fixture.
theorem output_correct : output = CanonicalPBS.evaluate 3 2 1 (by decide +kernel) key input :=
  PackedPBSCoverage.output_of_constraints (c := 1) (lanes := 1) (r := 0)
    2 HasteBootsHadamardBlindRotationSmoke.primitive (RingHom.id (ZMod 17))
    3 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    key input tables step.output increment decompositionA decompositionB stages keyStage output
    arithmetic multiplication switched extracted

-- A changed final public body is detected with all earlier sources held fixed.
def badOutput : NativePublic.Ciphertext 17 1 := { output with body := output.body+1 }
example : ¬PBSHadamard.Relation (KeySwitchExtraction.tables (c := 1) (lanes := 1)
    (by decide +kernel : 0 < 1) (NativePBS.bias step.output) increment badOutput) := by
  unfold PBSHadamard.Relation
  decide +kernel

end
end HasteBootsPackedPBSCoverageSmoke
