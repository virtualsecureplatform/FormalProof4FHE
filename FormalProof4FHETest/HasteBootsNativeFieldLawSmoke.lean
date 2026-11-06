module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFirstReadLaw
import all FormalProof4FHE.HasteBoots.CausalStreamExposure
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke
open FormalProof4FHE.HasteBoots
open OracleComp OracleSpec MeasureTheory ProbabilityTheory
namespace HasteBootsNativeFieldLawSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def root : NativeRootMessage.Digest := fun _ => 0
def parent := NativeTranscript.new [] root
def phase := (NativeTranscript.beginField parent [] 3 2).run.1
def world : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (_,offset) => if offset = 0 then 3 else if offset = 1 then 1 else 2

def initial := NativeFieldVector.initial phase 2
def pausedState := (NativeFieldVector.execute 3 2 initial world).1
def completed := (NativeFieldVector.execute 3 3 initial world).1
example : pausedState.remaining = 1 ∧ pausedState.values = [1] ∧ pausedState.chunks = [[3],[1]] := by decide +kernel
example : completed.remaining = 0 ∧ completed.values = [1,2] ∧ completed.chunks = [[3],[1],[2]] := by decide +kernel
example : NativeFieldVectorLaw.values 3 2 2 phase world = none := by decide +kernel
example : NativeFieldVectorLaw.values 3 3 2 phase world = some ![1,2] := by decide +kernel
example : (NativeFieldVector.execute 3 1 pausedState world).1.values = [1,2] := by decide +kernel
example : (NativeFieldVector.execute 3 3 initial world).2.map (fun entry => match entry with | .output _ offset _ => offset | _ => 99) = [0,1,2] := by decide +kernel
example : (NativeFieldVectorLaw.values 3 3 2 phase world,(NativeFieldVector.execute 3 3 initial world).2) =
    (OracleProgram.run (NativeFieldVectorProgram.program 3 3 2 phase) world).run :=
  by simpa only [NativeFieldVectorLaw.values,NativeFieldVector.run_collect,initial] using
    NativeFieldVectorProgram.collect_projection 3 3 2 phase world

-- One shared candidate budget, not a separate retry budget per coefficient.
example : BudgetedUniformSequence.mass (1/4) (3/4) 2 2 = (9/16 : ENNReal) := by
  norm_num [BudgetedUniformSequence.mass]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div]
example : BudgetedUniformSequence.mass (1/4) (3/4) 3 2 = (27/32 : ENNReal) := by
  norm_num [BudgetedUniformSequence.mass]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv]

example : BudgetedUniformSequence.mass (1/4) (3/4) 1 2 = 0 := by norm_num [BudgetedUniformSequence.mass]

-- Existing cache entries outside the unread tail are allowed.
def cold : NativeShakeCache.Cache := fun _ => none
def other : InputIndexedOracle.Input := [255]
def unrelated : NativeShakeCache.Cache := fun key => if key.1 = other then some 7 else none
theorem distinct : phase.pending.input ≠ other := by decide +kernel
example : FreshShakeTail.Fresh unrelated phase.pending.input 0 := by
  intro position beyond
  simp only [unrelated,distinct,ite_false]
def overlapping : NativeShakeCache.Cache := Function.update cold (phase.pending.input,1) (some 3)
example : ¬ FreshShakeTail.Fresh overlapping phase.pending.input 0 := by
  intro fresh
  have impossible := fresh 1 (by omega)
  simp [overlapping] at impossible

-- The native posterior is after a real read of a different input.
def past (oracle : InputIndexedOracle.World) := ObservationReplay.read oracle other 2 1
theorem replay : ObservationReplay.Replayable past := ObservationReplay.read_replay other 2 1
def shape : Unit → BinaryTree.Skeleton := fun _ => .leaf
def checkpoint : CheckpointExecution.State (Input := InputIndexedOracle.Input) (Digest := NativeRootMessage.Digest) shape := CheckpointExecution.empty shape
theorem hashStart : checkpoint.hash = JointHashCache.project (past world).run.2 := by rfl
theorem fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) phase.pending.input phase.consumed.length := by
  apply FreshShakeTail.observed_fresh
  intro position beyond
  have different : phase.pending.input ≠ other := distinct
  simp [past,ObservationReplay.read,ObservationReplay.footprint,ObservationReplay.coordinates,InputIndexedOracle.bytes,InputIndexedOracle.block,InputIndexedOracle.shake,different]

example (event : (Fin 2 → ZMod 3) → Prop) :
    (InputIndexedOracle.law[|{oracle | (past oracle).run = (past world).run}])
      {oracle | (NativeFieldVectorLaw.values 3 3 2 phase oracle).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar 3 1) 3 2 * Pr{let values ← $ᵗ (Fin 2 → ZMod 3)}[event values] :=
  NativeFieldVectorLaw.conditional_uniform replay world NativeGoldColumnAuthentication.encoding root shape checkpoint hashStart 3 (by decide) 3 2 phase fresh event
example (event : (Fin 2 → ZMod 3) → Prop) :
    (InputIndexedOracle.law[|{oracle | (past oracle).run = (past world).run}])
      {oracle | ∃ fuel, (NativeFieldVectorLaw.values 3 fuel 2 phase oracle).elim False event} ≤ Pr{let values ← $ᵗ (Fin 2 → ZMod 3)}[event values] :=
  NativeFieldVectorLaw.eventual_le_uniform replay world NativeGoldColumnAuthentication.encoding root shape checkpoint hashStart 3 (by decide) 2 phase fresh event

-- First stream exposure is eligible at any offset. Prior partial reads of
-- that same input exclude eligibility, while starts/empty reads/hashes do not.
def step (_ : Unit) : OracleMachine.Command Unit Unit := .read phase.pending.input 999 1 (fun _ => ())
def emptyStep (_ : Unit) : OracleMachine.Command Unit Unit := .read phase.pending.input 999 0 (fun _ => ())
example : CausalStreamExposure.firstRead step (.inl (),[.start phase.pending.input,.output phase.pending.input 17 [],.hash phase.pending.input (List.replicate 64 0)]) = some phase.pending.input := by decide +kernel
example : CausalStreamExposure.firstRead step (.inl (),[.output phase.pending.input 17 [0]]) = none := by decide +kernel
example : CausalStreamExposure.firstRead emptyStep (.inl (),[]) = none := by decide +kernel

def machinePast (oracle : InputIndexedOracle.World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← past oracle
  pure (.inl ())
theorem machineReplay : ObservationReplay.Replayable machinePast :=
  ObservationReplay.bind_replay replay (fun _ => ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit))
theorem machineHashStart : checkpoint.hash = JointHashCache.project (machinePast world).run.2 := by rfl
theorem firstSelected : CausalStreamExposure.firstRead step (machinePast world).run = some phase.pending.input := by decide +kernel
example (event : (Fin 1 → Fin 2 → ZMod 3) → Prop) :
    (InputIndexedOracle.law[|{oracle | (machinePast oracle).run = (machinePast world).run}])
      {oracle | ∃ fuel, (NativeFieldMatrixLaw.values 3 fuel 1 2 phase oracle).elim False event} ≤
        Pr{let matrix ← $ᵗ (Fin 1 → Fin 2 → ZMod 3)}[event matrix] :=
  CausalStreamExposure.eventual_le_uniform_at_first_read step machineReplay world NativeGoldColumnAuthentication.encoding root shape checkpoint machineHashStart 3 (by decide) 1 2 phase firstSelected event

example : NativeFieldMatrixLaw.reshape 3 2 2 ![0,1,2,0] 1 0 = 2 := by decide +kernel
example : CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 ∧ CanonicalByteSampler.byteCount NativeFields.babyBearModulus = 4 := by decide +kernel
example (event : (Fin 6 → Fin 12 → NativeFields.BabyBear) → Prop) :
    Pr{let vector ← $ᵗ (Fin (12*6) → NativeFields.BabyBear)}[event (NativeFieldMatrixLaw.reshape NativeFields.babyBearModulus 6 12 vector)] =
      Pr{let matrix ← $ᵗ (Fin 6 → Fin 12 → NativeFields.BabyBear)}[event matrix] :=
  NativeFieldMatrixLaw.uniform_reshape NativeFields.babyBearModulus 6 12 event

-- The checked native Goldilocks 3/4 batch uses exactly this sampled matrix.
section Batch
open HasteBootsBatchMeaningSmoke (ctx work prepared)
example : ctx.parameters.width.val = 3 ∧ ctx.parameters.code.blockWidth.val = 4 ∧ work.geometry.randomCount.val = 18 := by decide +kernel
example : NativeGoldBatchRandomLaw.rectangular ctx HasteBootsBatchMeaningSmoke.world work prepared HasteBootsBatchMeaningSmoke.world =
    some (NativeGoldBatchRectangularChecks.random ctx HasteBootsBatchMeaningSmoke.world work prepared) :=
  NativeGoldBatchRandomLaw.prepared_rectangular ctx HasteBootsBatchMeaningSmoke.world work prepared
def batchStep (_ : Unit) : OracleMachine.Command Unit Unit := .read (NativeGoldBatchRandomLaw.phase work).pending.input 17 1 (fun _ => ())
theorem batchHashStart : checkpoint.hash = JointHashCache.project (machinePast HasteBootsBatchMeaningSmoke.world).run.2 := by rfl
theorem batchSelected : CausalStreamExposure.firstRead batchStep (machinePast HasteBootsBatchMeaningSmoke.world).run = some (NativeGoldBatchRandomLaw.phase work).pending.input := by decide +kernel
example (event : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → NativeFields.Goldilocks) → Prop) :
    (InputIndexedOracle.law[|{oracle | (machinePast oracle).run = (machinePast HasteBootsBatchMeaningSmoke.world).run}])
      {oracle | (NativeGoldBatchRandomLaw.rectangular ctx HasteBootsBatchMeaningSmoke.world work prepared oracle).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar NativeFields.goldilocksModulus 1) ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) *
        Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → NativeFields.Goldilocks)}[event matrix] :=
  NativeGoldBatchFirstReadLaw.conditional_uniform ctx HasteBootsBatchMeaningSmoke.world work prepared batchStep machineReplay
    NativeGoldColumnAuthentication.encoding root shape checkpoint batchHashStart batchSelected event

end Batch
end
end HasteBootsNativeFieldLawSmoke
