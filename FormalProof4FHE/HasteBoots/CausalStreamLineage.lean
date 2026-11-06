module
public import FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
@[expose] public section

/-! Every newly touched stream has a real earlier machine packet and an
exact split of the complete history at its first positive read. Inherited
exposures remain explicit, including partial and far-offset reads. -/
namespace FormalProof4FHE.HasteBoots.CausalStreamLineage
open InputIndexedOracle (Input World)
open NativeTranscript (Observation Execution)
open CausalStreamExposure (seen touches firstRead)
open CausalStreamCoverage (locate)
open CausalExposureLifetime (history)
open OracleProgram (run)
noncomputable section

theorem coverage {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (history past initial step fuel world).run.2 input = true) :
    seen (past world).run.2 input = true ∨ ∃ index < fuel,
      firstRead step (history past initial step index world).run = some input ∧
      CausalFirstStreamPrefix.recover input (history past initial step fuel world).run.2 =
        some (history past initial step index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history past initial step fuel world).run.2 =
          (history past initial step index world).run.2 ++ .output input offset values :: after := by
  cases inherited : seen (past world).run.2 input with
  | true => exact Or.inl rfl
  | false =>
    have later : seen (run (OracleMachine.take step fuel (initial (past world).run.1)) world).run.2 input = true := by
      rw [CausalExposureLifetime.history_run,CausalStreamCoverage.seen_append,inherited] at touched
      exact touched
    cases found : locate input (run (OracleMachine.take step fuel (initial (past world).run.1)) world).run.2 with
    | none => rw [(CausalStreamCoverage.locate_none _ _).mp found] at later; contradiction
    | some index =>
      have bound := CausalStreamCoverage.locate_lt input _ index found
      have beforeFuel := bound.trans_le (OracleMachineExposure.log_length_le step fuel _ world)
      obtain ⟨before,entry,after,split,length,unseen,hit⟩ := (CausalStreamCoverage.locate_some input _ index).mp found
      have prefixLogEq : (history past initial step index world).run.2 = (past world).run.2++before := by
        rw [CausalExposureLifetime.history_run,OracleMachineExposure.log_take step index fuel (Nat.le_of_lt beforeFuel)]
        rw [split,← length,List.take_left]
      have full : (history past initial step fuel world).run.2 = (history past initial step index world).run.2++entry::after := by
        rw [CausalExposureLifetime.history_run,split,prefixLogEq,List.append_assoc]
      have earlier : seen (history past initial step index world).run.2 input = false := by
        rw [prefixLogEq,CausalStreamCoverage.seen_append,inherited,unseen]
        rfl
      have selected : firstRead step (history past initial step index world).run = some input := by
        rw [CausalExposureLifetime.history_run]
        exact CausalStreamCoverage.selected_at_first_exposure step fuel index _ world input _ inherited found
      refine Or.inr ⟨index,beforeFuel,selected,?_,?_⟩
      · rw [full]
        exact CausalFirstStreamPrefix.recover_at input _ _ entry earlier hit
      · cases entry with
        | start key => simp [touches] at hit
        | hash key digest => simp [touches] at hit
        | output key offset values =>
          have info : key = input ∧ 0 < values.length := of_decide_eq_true hit
          rcases info with ⟨rfl,positive⟩
          exact ⟨offset,values,after,List.ne_nil_of_length_pos positive,full⟩
end
end FormalProof4FHE.HasteBoots.CausalStreamLineage
