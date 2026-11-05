module

public import FormalProof4FHE.HasteBoots.OracleMachine
public import FormalProof4FHE.HasteBoots.OracleFirstExposure
public import FormalProof4FHE.HasteBoots.OracleSeedGuessing
@[expose] public section

/-! Earliest raw-seed exposure selects an actual replayable causal-machine
prefix. Before that prefix all64 logical seed coordinates are unobserved.
For any fixed target set this yields the exact512-bit guessing probability.
Native input/root classification and proof that a target set is selected
from the prior history remain required at protocol instantiation. -/
namespace FormalProof4FHE.HasteBoots.OracleMachineExposure
open InputIndexedOracle (World)
open OracleMachine (Command take)


private theorem pure_log {A : Type} (value : A) (world : World) :
    (OracleProgram.run (.pure value) world).run.2 = [] := rfl
private theorem start_log {A : Type} (input : InputIndexedOracle.Input) (next : OracleProgram.Program A) (world : World) :
    (OracleProgram.run (.start input next) world).run.2 = .start input :: (OracleProgram.run next world).run.2 := rfl
private theorem read_log {A : Type} (input : InputIndexedOracle.Input) (offset count : ℕ)
    (next : InputIndexedOracle.Input → OracleProgram.Program A) (world : World) :
    (OracleProgram.run (.read input offset count next) world).run.2 =
      .output input offset (InputIndexedOracle.bytes world input offset count) ::
        (OracleProgram.run (next (InputIndexedOracle.bytes world input offset count)) world).run.2 := rfl
private theorem hash_log {A : Type} (input : InputIndexedOracle.Input)
    (next : NativeRootMessage.Digest → OracleProgram.Program A) (world : World) :
    (OracleProgram.run (.hash input next) world).run.2 =
      .hash input (List.ofFn (InputIndexedOracle.sha512 world input)) ::
        (OracleProgram.run (next (InputIndexedOracle.sha512 world input)) world).run.2 := rfl

theorem log_take {S A : Type} (step : S → Command S A) (first later : ℕ) (bounded : first ≤ later)
    (state : S) (world : World) :
    (OracleProgram.run (take step first state) world).run.2 =
      (OracleProgram.run (take step later state) world).run.2.take first := by
  induction first generalizing later state with
  | zero => cases chosen : step state <;> simp only [take,chosen,pure_log,List.take_zero]
  | succ first ih =>
    cases later with
    | zero => omega
    | succ later =>
      have bounded : first ≤ later := by omega
      cases chosen : step state with
      | done value => simp only [take,chosen,pure_log,List.take_nil]
      | start input next =>
        simpa only [take,chosen,start_log,List.take_succ_cons,List.length_cons,List.cons.injEq] using
          congrArg (List.cons (.start input)) (ih later bounded next)
      | read input offset count next =>
        simpa only [take,chosen,read_log,List.take_succ_cons,List.length_cons,List.cons.injEq] using
          congrArg (List.cons (.output input offset (InputIndexedOracle.bytes world input offset count)))
            (ih later bounded (next (InputIndexedOracle.bytes world input offset count)))
      | hash input next =>
        simpa only [take,chosen,hash_log,List.take_succ_cons,List.length_cons,List.cons.injEq] using
          congrArg (List.cons (.hash input (List.ofFn (InputIndexedOracle.sha512 world input))))
            (ih later bounded (next (InputIndexedOracle.sha512 world input)))

theorem log_length_le {S A : Type} (step : S → Command S A) (fuel : ℕ) (state : S) (world : World) :
    (OracleProgram.run (take step fuel state) world).run.2.length ≤ fuel := by
  induction fuel generalizing state with
  | zero => cases chosen : step state <;> simp only [take,chosen,pure_log,List.length_nil,Nat.zero_le]
  | succ fuel ih =>
    cases chosen : step state with
    | done value => simp only [take,chosen,pure_log,List.length_nil,Nat.zero_le]
    | start input next =>
      simpa only [take,chosen,start_log,List.take_succ_cons,List.length_cons,List.cons.injEq] using
        Nat.succ_le_succ (ih next)
    | read input offset count next =>
      simpa only [take,chosen,read_log,List.take_succ_cons,List.length_cons,List.cons.injEq] using
        Nat.succ_le_succ (ih (next (InputIndexedOracle.bytes world input offset count)))
    | hash input next =>
      simpa only [take,chosen,hash_log,List.take_succ_cons,List.length_cons,List.cons.injEq] using
        Nat.succ_le_succ (ih (next (InputIndexedOracle.sha512 world input)))


theorem pre_exposure_fresh {S A : Type} (step : S → Command S A) (fuel index : ℕ)
    (state : S) (world : World) (input : InputIndexedOracle.Input)
    (first : OracleFirstExposure.locate (OracleProgram.run (take step fuel state) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some index) :
    ∀ position : Fin 64, (.inl (input,position.val) : InputIndexedOracle.Coordinate) ∉
      ObservationReplay.footprint (OracleProgram.run (take step index state) world).run.2 := by
  have bounded : index ≤ fuel := Nat.le_of_lt ((OracleFirstExposure.locate_lt _ _ index first).trans_le
    (log_length_le step fuel state world))
  rw [log_take step index fuel bounded state world]
  exact OracleFirstExposure.seed_before_fresh _ input index first

noncomputable section
open MeasureTheory ProbabilityTheory

theorem pre_exposure_targets {S A : Type} (step : S → Command S A) (fuel index : ℕ)
    (state : S) (world : World) (input : InputIndexedOracle.Input)
    (targets : Finset NativeRootMessage.Digest)
    (first : OracleFirstExposure.locate (OracleProgram.run (take step fuel state) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some index) :
    (InputIndexedOracle.law[|{other | (OracleProgram.run (take step index state) other).run =
      (OracleProgram.run (take step index state) world).run}])
      {other | InputIndexedOracle.block other input 0 64 ∈ targets} =
      (targets.card : ENNReal)/(2 : ENNReal)^512 :=
  OracleSeedGuessing.fresh_seed_targets (OracleProgram.run_replay _) world input targets
    (pre_exposure_fresh step fuel index state world input first)

end

end FormalProof4FHE.HasteBoots.OracleMachineExposure
