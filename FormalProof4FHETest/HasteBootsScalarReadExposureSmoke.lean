module
import all FormalProof4FHE.HasteBoots.AllocatedScalarExposure
import all FormalProof4FHETest.HasteBootsScalarCompletedSmoke

namespace FormalProof4FHE.HasteBoots.ScalarReadExposureSmoke
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ProgramFirstStreamRead (First)
noncomputable section

def input : Input := [21,22]
def world : World := fun _ => 0
def tail : Program Unit := .read input 0 8 (fun _ => .pure ())
def program : Program Unit := .start input (.read input 99 0 (fun _ => .hash input (fun _ => .read input 77 1 (fun _ => tail))))

def expected : First program world input where
  position := 3
  offset := 77
  count := 1
  next := fun _ => tail
  active := rfl
  history := rfl
  fresh := by
    change CausalStreamExposure.seen [Observation.start input,Observation.output input 99 [],Observation.hash input (List.ofFn (InputIndexedOracle.sha512 world input))] input = false
    simp [CausalStreamExposure.seen,CausalStreamExposure.touches]
  positive := by decide
  outputAt := rfl

def selected : First program world input := Classical.choice
  (ProgramFirstStreamRead.of_output program world input 77 (InputIndexedOracle.bytes world input 77 1)
    (by simp only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length]; decide)
    (List.mem_of_getElem? expected.outputAt))

/-- Starts, empty same-input reads and SHA-512 reads remain in the prefix;
the far-offset positive read is selected before the later offset-zero read. -/
theorem selected_position : selected.position = 3 := selected.position_unique expected

theorem selected_request : selected.offset = 77 ∧ selected.count = 1 := by
  have active := selected.active
  rw [selected_position] at active
  change Sum.inl (Program.read input 77 1 (fun _ => tail)) = Sum.inl (Program.read input selected.offset selected.count selected.next) at active
  have fields := Program.read.inj (Sum.inl.inj active)
  exact ⟨fields.2.1.symm,fields.2.2.1.symm⟩

theorem selected_actual : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix selected.position program world).run = some input := selected.selected

example : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 1 program world).run = none := by
  change (if 0 < (0 : ℕ) ∧ CausalStreamExposure.seen [Observation.start input] input = false then some input else none) = none
  simp

example : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 2 program world).run = none := rfl

section Native
open ScalarReplaySmoke (statement proof)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open ScalarCompletedSmoke (firstEntry firstMember)

def nativeProgram : Program NativeScalarBatchVerifier.Machine := NativeScalarBatchVerifier.verifyPrefix 9 child statement proof

theorem native_occurrence : ∃ position offset : ℕ, (run nativeProgram worldZero).run.2[position]? =
    some (Observation.output firstEntry.coefficients.phase.pending.input offset
      (InputIndexedOracle.bytes worldZero firstEntry.coefficients.phase.pending.input offset 8)) := by
  simpa only [nativeProgram,NativeScalarBatchVerifier.verifyPrefix,NativeScalarBatchVerifier.run_steps] using
    ScalarReadExposure.completed child statement proof 9 worldZero firstEntry firstMember

def enclosing : Program NativeScalarBatchVerifier.Machine := .read firstEntry.coefficients.phase.pending.input 93 1 (fun _ => nativeProgram)

theorem included : (run nativeProgram worldZero).run.2.Sublist (run enclosing worldZero).run.2 := List.sublist_append_right _ _

/-- The witness comes from a real completed native round's producing read,
then is embedded in a program with an earlier same-input prequery. -/
theorem enclosing_first : Nonempty (First enclosing worldZero firstEntry.coefficients.phase.pending.input) := by
  obtain ⟨position,offset,present⟩ := native_occurrence
  apply ProgramFirstStreamRead.of_output enclosing worldZero firstEntry.coefficients.phase.pending.input offset _ _
    (included.subset (List.mem_of_getElem? present))
  simp only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length]
  decide

def prequery : First enclosing worldZero firstEntry.coefficients.phase.pending.input where
  position := 0
  offset := 93
  count := 1
  next := fun _ => nativeProgram
  active := rfl
  history := rfl
  fresh := rfl
  positive := by decide
  outputAt := rfl

theorem native_reindexed (first : First enclosing worldZero firstEntry.coefficients.phase.pending.input) : first.position = 0 := first.position_unique prequery

end Native
end
end FormalProof4FHE.HasteBoots.ScalarReadExposureSmoke
