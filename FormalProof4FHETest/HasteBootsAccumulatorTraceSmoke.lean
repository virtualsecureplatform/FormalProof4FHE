module
import FormalProof4FHE.HasteBoots.AccumulatorTrace
import FormalProof4FHETest.HasteBootsHadamardBlindRotationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsHadamardBlindRotationSmoke
open NativeBlindRotation (Cipher Control StepTrace makeStep)
open scoped Matrix
namespace HasteBootsAccumulatorTraceSmoke
noncomputable section

def shape : AccumulatorTrace.Shape := ⟨3,4,by decide +kernel,by decide +kernel⟩
def firstStep : StepTrace 17 4 := makeStep 2 control 1 accumulator
def zeroStep : StepTrace 17 4 := makeStep 2 control 0 firstStep.output
def lastStep : StepTrace 17 4 := makeStep 2 control 5 zeroStep.output

def tables : AccumulatorTrace.Tables 17 4 4 where
  input := ![accumulator,firstStep.output,zeroStep.output,0]
  product := ![firstStep.product,zeroStep.product,lastStep.product,0]
  difference := ![firstStep.difference,zeroStep.difference,lastStep.difference,0]
  external := ![firstStep.external,zeroStep.external,lastStep.external,0]
  output := ![firstStep.output,zeroStep.output,lastStep.output,0]

def final : Cipher 17 4 := fun half => if half then polynomial 14 12 16 15 else polynomial 1 5 2 16
def controls : Fin 3 → Control 17 4 1 × ℕ := fun index => (control,(![1,0,5] : Fin 3 → ℕ) index)

theorem arithmetic : AccumulatorTrace.Arithmetic tables := by
  unfold AccumulatorTrace.Arithmetic
  decide +kernel

theorem linkage : AccumulatorTrace.Linkage shape tables accumulator final := by
  constructor
  · decide +kernel
  · decide +kernel
  · intro row
    fin_cases row <;> decide +kernel

theorem rotations : ∀ round, tables.product (AccumulatorTrace.active shape round) = fun half =>
    NativeBlindRotation.rotate (controls round).2 (tables.input (AccumulatorTrace.active shape round) half) := by
  intro round
  fin_cases round <;> rfl

theorem external : ∀ round, tables.external (AccumulatorTrace.active shape round) =
    NativeBlindRotation.externalProduct 2 (controls round).1 (tables.difference (AccumulatorTrace.active shape round)) := by
  intro round
  fin_cases round <;> rfl

-- All three original rounds execute; the fourth row stays only in the tables.
example : (List.ofFn (AccumulatorTrace.traceAt shape tables)).length = 3 := by decide +kernel
example : (AccumulatorTrace.traceAt shape tables (1 : Fin 3)).output = tables.input 1 := by decide +kernel
example : NativeBlindRotation.ValidTrace 2 (List.ofFn controls) accumulator
    (List.ofFn (AccumulatorTrace.traceAt shape tables)) final :=
  AccumulatorTrace.validTrace_tables shape tables accumulator final arithmetic linkage 2 controls rotations external
example : final = NativeBlindRotation.run 2 (List.ofFn controls) accumulator :=
  AccumulatorTrace.output_eq_run shape tables accumulator final arithmetic linkage 2 controls rotations external

-- The two separate boundary corrections are at rows 3 and 2, respectively.
example : tables.input (AccumulatorTrace.next shape (3 : Fin 4))-tables.output 3 = accumulator := by decide +kernel
example : tables.input (AccumulatorTrace.next shape (2 : Fin 4))-tables.output 2 = -final := by decide +kernel

-- With no padding the two boundary locations coincide, retaining both terms.
def tightShape : AccumulatorTrace.Shape := ⟨2,2,by decide +kernel,by decide +kernel⟩
def tight : AccumulatorTrace.Tables 17 4 2 where
  input := ![accumulator,firstStep.output]
  product := ![firstStep.product,zeroStep.product]
  difference := ![firstStep.difference,zeroStep.difference]
  external := ![firstStep.external,zeroStep.external]
  output := ![firstStep.output,zeroStep.output]
example : AccumulatorTrace.Linkage tightShape tight accumulator zeroStep.output := by
  constructor
  · decide +kernel
  · decide +kernel
  · intro row
    fin_cases row <;> decide +kernel
example : tight.input (AccumulatorTrace.next tightShape (1 : Fin 2))-tight.output 1 = accumulator-zeroStep.output := by decide +kernel

-- Each bad step is locally correct, but round 1 starts from an unrelated zero
-- input. Arithmetic and endpoints alone must not imply a correct full trace.
def badZero : StepTrace 17 4 := makeStep 2 control 0 0
def badLast : StepTrace 17 4 := makeStep 2 control 5 badZero.output
def bad : AccumulatorTrace.Tables 17 4 4 where
  input := ![accumulator,0,badZero.output,0]
  product := ![firstStep.product,badZero.product,badLast.product,0]
  difference := ![firstStep.difference,badZero.difference,badLast.difference,0]
  external := ![firstStep.external,badZero.external,badLast.external,0]
  output := ![firstStep.output,badZero.output,badLast.output,0]
example : AccumulatorTrace.Arithmetic bad := by
  unfold AccumulatorTrace.Arithmetic
  decide +kernel
example : bad.input (AccumulatorTrace.first shape) = accumulator ∧ bad.output (AccumulatorTrace.last shape) = 0 := by decide +kernel
example : ∀ round, NativeBlindRotation.ValidStep 2 (controls round).1 (controls round).2
    (bad.input (AccumulatorTrace.active shape round)) (AccumulatorTrace.traceAt shape bad round) := by
  intro round
  fin_cases round
  · exact NativeBlindRotation.makeStep_valid 2 control 1 accumulator
  · exact NativeBlindRotation.makeStep_valid 2 control 0 0
  · exact NativeBlindRotation.makeStep_valid 2 control 5 badZero.output
example : ¬AccumulatorTrace.Linkage shape bad accumulator 0 := by
  intro link
  let row : Fin shape.padded := ⟨0,by decide +kernel⟩
  have notWrap : row ≠ AccumulatorTrace.wrap shape := by
    intro equal
    have values := congrArg Fin.val equal
    change 0 = 3 at values
    omega
  have notLast : row ≠ AccumulatorTrace.last shape := by
    intro equal
    have values := congrArg Fin.val equal
    change 0 = 2 at values
    omega
  have identity := link.cyclic row
  rw [ite_eq_right notWrap, ite_eq_right notLast, sub_self] at identity
  have unequal : bad.input (AccumulatorTrace.next shape row)-bad.output row ≠ 0 := by decide +kernel
  exact unequal identity

example : (0 : Cipher 17 4) ≠ NativeBlindRotation.run 2 (List.ofFn controls) accumulator := by decide +kernel

-- A single active round has both endpoints at its only row.
def singleShape : AccumulatorTrace.Shape := ⟨1,1,by decide +kernel,by decide +kernel⟩
def single : AccumulatorTrace.Tables 17 4 1 where
  input := fun _ => accumulator
  product := fun _ => firstStep.product
  difference := fun _ => firstStep.difference
  external := fun _ => firstStep.external
  output := fun _ => firstStep.output
example : AccumulatorTrace.Linkage singleShape single accumulator firstStep.output := by
  constructor
  · rfl
  · rfl
  · intro row
    fin_cases row
    rfl
end
end HasteBootsAccumulatorTraceSmoke
