module
public import FormalProof4FHE.HasteBoots.PackedAccumulatorTrace
public import FormalProof4FHETest.HasteBootsAccumulatorTraceSmoke
public import FormalProof4FHETest.HasteBootsAccumulatorMatrixSmoke
@[expose] public section
open FormalProof4FHE.HasteBoots
open HasteBootsAccumulatorTraceSmoke HasteBootsHadamardBlindRotationSmoke
open OracleSpec OracleComp
namespace HasteBootsPackedAccumulatorTraceSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
local instance : SampleableType (Fin (2^1) → ZMod 17) := SampleableType.ofFintype _

def rounds : PackedAccumulatorTrace.Rounds 2 := ⟨3,by decide +kernel,by decide +kernel⟩
def embed : ZMod 17 →+* ZMod 17 := RingHom.id _
def difference := PackedAccumulatorTrace.pack (c := 1) (lanes := 1) (r := 2) embed tables.difference
def decompositionA := AccumulatorMatrixSoundness.copyHalf difference false
def decompositionB := AccumulatorMatrixSoundness.copyHalf difference true
def sources := PackedAccumulatorTrace.sources (c := 1) (lanes := 1) embed rounds tables accumulator final decompositionA decompositionB

theorem holds : AccumulatorEndpointSoundness.FullHolds sources := by
  constructor
  · unfold AccumulatorMatrixSoundness.Holds
    decide +kernel
  · unfold AccumulatorEndpointSoundness.Holds
    decide +kernel

example : AccumulatorTrace.Arithmetic tables :=
  PackedAccumulatorTrace.arithmetic_of_holds (c := 1) (lanes := 1) (r := 2) embed rounds tables accumulator final decompositionA decompositionB holds
example : AccumulatorTrace.Linkage rounds.shape tables accumulator final :=
  PackedAccumulatorTrace.linkage_of_holds (c := 1) (lanes := 1) (r := 2) embed rounds tables accumulator final decompositionA decompositionB holds
example : NativeBlindRotation.ValidTrace 2 (List.ofFn controls) accumulator
    (List.ofFn (AccumulatorTrace.traceAt rounds.shape tables)) final :=
  PackedAccumulatorTrace.validTrace (c := 1) (lanes := 1) (r := 2) embed rounds tables accumulator final decompositionA decompositionB holds 2 controls rotations external
example : final = NativeBlindRotation.run 2 (List.ofFn controls) accumulator :=
  PackedAccumulatorTrace.output_eq_run (c := 1) (lanes := 1) (r := 2) embed rounds tables accumulator final decompositionA decompositionB holds 2 controls rotations external

-- The native scalar layout retains the coefficient, lane, row, and half.
example : (PackedAccumulatorTrace.polynomial 1 1 ((true,()),(1 : Fin 2))).val = 3 := by decide +kernel
example : 2*(FlatMatrixFold.index 4 (AccumulatorPackedQueries.coordinate (c := 1) (r := 2) (true,()) (true,(false,())) true)).val+1 =
    3+4*((FlatMatrixFold.index 2 (true,(false,()))).val+4) :=
  by
    have address := PackedAccumulatorTrace.scalar_address (c := 1) (lanes := 1) (r := 2) (true,()) (true,(false,())) true (1 : Fin 2)
    have coefficient : (PackedAccumulatorTrace.polynomial 1 1 ((true,()),(1 : Fin 2))).val = 3 := by decide +kernel
    rw [coefficient] at address
    exact address
example : tables.input (3 : Fin 4) = 0 := by decide +kernel
example : (controls (1 : Fin 3)).2 = 0 := by decide +kernel

-- Duplicating INPUT_ACC instead of EXTERNAL_INPUT must fail on this trace.
def wrongLinks := { sources with
  duplicateA := AccumulatorMatrixSoundness.copyHalf sources.input false
  duplicateB := AccumulatorMatrixSoundness.copyHalf sources.input true }
example : ¬AccumulatorEndpointSoundness.FullHolds wrongLinks := by
  intro hypothesis
  have zero := hypothesis.1 (2 : Fin 5)
  have nonzero : AccumulatorMatrixSoundness.residual wrongLinks 2 ≠ 0 := by decide +kernel
  exact nonzero zero

-- Honest multiplication stages cannot rescue an incorrect public output.
example : Pr{let query ← MatrixCompression.sample (b := 2^1) HasteBootsAccumulatorMatrixSmoke.nodes 4}[
    AccumulatorEndpointSoundness.FullCheck
      (PackedAccumulatorTrace.sources (c := 1) (lanes := 1) embed rounds tables accumulator 0 decompositionA decompositionB) query] ≤
    (36 : ENNReal)/289 := by
  have wrong : (0 : NativeBlindRotation.Cipher 17 4) ≠ NativeBlindRotation.run 2 (List.ofFn controls) accumulator := by decide +kernel
  have bound := PackedAccumulatorTrace.wrong_output_bound (c := 1) (lanes := 1)
    HasteBootsAccumulatorMatrixSmoke.nodes embed rounds tables accumulator 0 decompositionA decompositionB
    2 controls rotations external wrong
  norm_num [ZMod.card] at bound
  calc
    _ ≤ (4 : ENNReal)*((3 : ENNReal)/17)^2 := bound
    _ = _ := by norm_num [div_eq_mul_inv,mul_pow,← ENNReal.inv_pow,← mul_assoc]
end
end HasteBootsPackedAccumulatorTraceSmoke
