module
import all FormalProof4FHE.HasteBoots.ClosedByteMachineGoldAllRisk
import all FormalProof4FHETest.HasteBootsCalibrationSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open ClosedByteMachine (Instruction Tape initialise take)
open OracleSpec OracleComp
namespace HasteBootsRootWorkSmoke
noncomputable section

def dummy : Digest := fun _ => 19
def digest : Digest := fun _ => 0
def zeroWorld : World := fun _ => 0

theorem cached_risk (input : Input) (value : Digest) :
    NativeRootFamilyHashStep.risk dummy input [.hash input (List.ofFn value)] = 0 := by
  simp only [NativeRootFamilyHashStep.risk,CheckpointCollision.hash_loss,
    NativeGoldBatchFamilyAvailability.reconstructed_hash,JointHashCache.project,List.foldl_cons,List.foldl_nil,
    JointHashCache.record,CachedHashHandler.observe,QueryCache.cacheQuery_self,Option.some_ne_none,ite_false]

example (before : List Observation) (input values : Input) (offset : ℕ) :
    NativeRootFamilyLifetime.Bad dummy (before++[.output input offset values]) ↔ NativeRootFamilyLifetime.Bad dummy before :=
  NativeRootFamilyHashStep.bad_read dummy before input offset values
example (before : List Observation) (input : Input) :
    NativeRootFamilyLifetime.Bad dummy (before++[.start input]) ↔ NativeRootFamilyLifetime.Bad dummy before :=
  NativeRootFamilyHashStep.bad_start dummy before input

-- A concrete exceptional world really can create a collision. It is not
-- assumed impossible; coverage locates an earlier real hash instruction.
def code : List Instruction := [.hash 0 1,.hash 1 2]
def privateData : Tape → Input := fun tape => if tape = 0 then [1] else []
theorem distinct : ([1] : Input) ≠ List.ofFn digest := by
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_cons,List.length_nil,List.length_ofFn] at lengths
  omega

theorem failed : NativeRootFamilyLifetime.Bad dummy
    (ClosedByteMachineGoldRisk.history code [] privateData 2 zeroWorld).run.2 := by
  apply Or.inr
  rw [NativeGoldBatchFamilyAvailability.reconstructed_hash,ClosedByteMachineGoldRisk.history_run]
  change CacheHasCollision (JointHashCache.project
    [.hash [1] (List.ofFn digest),.hash (List.ofFn digest) (List.ofFn digest)]).cache
  refine ⟨[1],List.ofFn digest,digest,digest,distinct,?_,?_,HEq.rfl⟩
  · simp only [JointHashCache.project,List.foldl_cons,List.foldl_nil,JointHashCache.record,
      JointHashCache.decode_ofFn,CachedHashHandler.observe]
    rw [QueryCache.cacheQuery_of_ne _ _ distinct,QueryCache.cacheQuery_self]
  · simp only [JointHashCache.project,List.foldl_cons,List.foldl_nil,JointHashCache.record,
      JointHashCache.decode_ofFn,CachedHashHandler.observe,QueryCache.cacheQuery_self]
example : ∃ index < 2, ClosedByteMachineRootFailure.event code [] dummy
    (ClosedByteMachineGoldRisk.history code [] privateData index zeroWorld).run zeroWorld :=
  ClosedByteMachineRootFailure.coverage code [] privateData dummy 2 zeroWorld failed

example (before : List Observation) :
    ClosedByteMachineRootFailure.risk [.halt] [] dummy
      (.inl (initialise [.halt] (fun _ => [])),before) = 0 := rfl
example : 1/((2^160 : ℕ) : ENNReal)+ClosedByteMachineRootWork.rate (2^160) ≤ 1/(2 : ENNReal)^159 :=
  ClosedByteMachineRootWork.rate_160

open HasteBootsCalibrationSmoke (ctx tables primitive constructed compatible)
open HasteBootsBatchMeaningSmoke (usize)
example (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    InputIndexedOracle.law {world | ClosedByteMachineGoldAllRisk.Failure code publicData dummy ctx primitive .helper dummy privateData world} ≤
      ClosedByteMachineGoldAllRisk.rate*ClosedByteMachineWork.expectedWork code publicData privateData :=
  ClosedByteMachineGoldAllRisk.lifetime_le_work code publicData dummy ctx tables (usize 2048) (usize 4) (usize 2)
    constructed primitive .helper compatible dummy privateData
example : (2 : ENNReal)^128*(64*4*ClosedByteMachineGoldAllRisk.rate) ≤ 9/16 :=
  ClosedByteMachineGoldAllRisk.shape_role_allowance
end
end HasteBootsRootWorkSmoke
