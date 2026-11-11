module
public import FormalProof4FHE.HasteBoots.ClosedByteScalarWork
@[expose] public section

/-! Observation-clock scalar charges are bounded by actual logged positive
read keys. This intermediate potential is accounted by interpreter work;
it is not itself a definition of attacker work. -/
namespace FormalProof4FHE.HasteBoots.ScalarLogWork
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run)
noncomputable section

def weight : Observation → ℕ
  | .output input _ values => if values = [] then 0 else input.length
  | _ => 0

def bytes (log : List Observation) : ℕ := (log.map weight).sum

theorem bytes_append (left right : List Observation) : bytes (left++right) = bytes left+bytes right := by
  simp [bytes]

theorem bytes_mono {left right : List Observation} (included : left.IsPrefix right) : bytes left ≤ bytes right := by
  obtain ⟨tail,rfl⟩ := included
  rw [bytes_append]
  omega

theorem next_bytes {S A : Type} (step : S → OracleMachine.Command S A)
    (packet : (S ⊕ A) × List Observation) (world : World) :
    ScalarEquationWork.selectedBytes step packet ≤ bytes (run (OracleMachine.resume step 1 packet.1) world).run.2 := by
  rcases packet with ⟨state,log⟩
  cases state with
  | inr value => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,OracleMachine.resume,run,bytes]
  | inl state =>
    cases chosen : step state with
    | read input offset count next =>
      simp only [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,chosen,
        OracleMachine.resume,OracleMachine.take,run,ObservationReplay.read,ObservationReplay.run_bind]
      cases count with
      | zero => simp [bytes,weight]
      | succ count =>
        have nonempty : InputIndexedOracle.bytes world input offset (count+1) ≠ [] := by
          intro empty
          have length := InputIndexedOracle.bytes_length world input offset (count+1)
          rw [empty] at length
          simp at length
        simp [bytes,weight,nonempty]
        split_ifs
        · change input.length ≤ _
          omega
        · exact Nat.zero_le _
    | _ => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,chosen,
        OracleMachine.resume,OracleMachine.take,run,ObservationReplay.start,ObservationReplay.hash,bytes]

theorem partial_bytes {S A : Type} (step : S → OracleMachine.Command S A) (state : S) (fuel : ℕ) (world : World) :
    (∑ index ∈ Finset.range fuel, ScalarEquationWork.selectedBytes step (run (OracleMachine.take step index state) world).run) ≤
      bytes (run (OracleMachine.take step fuel state) world).run.2 := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
    rw [Finset.sum_range_succ,OracleMachine.take_resume step fuel 1,OracleProgram.run_bind,ObservationReplay.run_bind,bytes_append]
    exact Nat.add_le_add ih (next_bytes step _ world)

theorem program_bytes {A : Type} (program : Program A) (world : World) :
    ScalarEquationWork.totalBytes program world ≤ (bytes (run program world).run.2 : ENNReal) := by
  rw [ScalarEquationWork.totalBytes,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro fuel
  have bounded := (partial_bytes OracleProgramMachine.step program fuel world).trans
    (bytes_mono (OracleProgramMachine.log_prefix_run fuel program world))
  simp only [OracleProgramMachine.take_run] at bounded
  exact_mod_cast bounded

theorem program_charge {A : Type} (program : Program A) (world : World) :
    ScalarLifetimeComposition.totalCharge program world ≤ (bytes (run program world).run.2 : ENNReal)*ScalarEquationWork.rate :=
  (ScalarEquationWork.charge_le_bytes program world).trans (mul_le_mul' (program_bytes program world) le_rfl)

end
end FormalProof4FHE.HasteBoots.ScalarLogWork
