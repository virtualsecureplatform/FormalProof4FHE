module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteMachine
@[expose] public section

/-! A finite instruction horizon uses only its original finite coin prefix,
including on counterfactual oracle branches. The infinite tape is retained. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinProgramPrefix
open InputIndexedOracle (Input Byte)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State take tick initialise)
open OracleProgram (Program bind)
noncomputable section

theorem take_agrees (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (tape other : Tape)
    (agree : ∀ index, state.cursor ≤ index → index < state.cursor+fuel → other index = tape index) :
    take code publicData other fuel state = take code publicData tape fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases stopped : state.machine.stopped with
    | some reason => rw [PrivateCoinByteMachine.stopped_take _ _ _ _ _ reason stopped,PrivateCoinByteMachine.stopped_take _ _ _ _ _ reason stopped]
    | none =>
      cases selected : code[state.machine.pc]? with
      | none =>
        simp only [take,tick,stopped,selected,OracleProgram.bind]
        apply ih
        intro index lower upper
        dsimp only at lower upper
        exact agree index lower (by omega)
      | some chosen =>
        cases chosen with
        | coin dst =>
          have same : other state.cursor = tape state.cursor := agree _ le_rfl (by omega)
          simp only [take,tick,stopped,selected,same,OracleProgram.bind]
          apply ih
          intro index lower upper
          dsimp only at lower upper
          exact agree index (by omega) (by omega)
        | base instruction =>
          simp only [take,tick,stopped,selected,NativeProgramComposition.bind_assoc,OracleProgram.bind]
          congr 1
          funext machine
          apply ih
          intro index lower upper
          dsimp only at lower upper
          exact agree index lower (by omega)

def select (fuel : ℕ) (tape : Tape) : Fin fuel → Byte := fun index => tape index

def restore (fuel : ℕ) (values : Fin fuel → Byte) : Tape := fun index =>
  if bound : index < fuel then values ⟨index,bound⟩ else 0

theorem select_measurable (fuel : ℕ) : Measurable (select fuel) :=
  Measurable.of_eval (fun index => measurable_pi_apply index.val)

theorem selected_program (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (tape : Tape) :
    take code publicData (restore fuel (select fuel tape)) fuel (initialise code privateData) =
      take code publicData tape fuel (initialise code privateData) := by
  apply take_agrees
  intro index lower upper
  change index < 0+fuel at upper
  have inside : index < fuel := by omega
  simp [restore,select,inside]

end
end FormalProof4FHE.HasteBoots.PrivateCoinProgramPrefix
