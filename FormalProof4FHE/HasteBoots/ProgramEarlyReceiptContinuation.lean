module
public import FormalProof4FHE.HasteBoots.ProgramEarlyReceiptWork
@[expose] public section

/-! Early receipt events depend only on their selected raw view. Their
actual first-read packets persist through arbitrary program continuations. -/
namespace FormalProof4FHE.HasteBoots.ProgramEarlyReceiptContinuation
open InputIndexedOracle (World)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
noncomputable section

theorem select_congr {S A T B : Type} (step : S → OracleMachine.Command S A) (other : T → OracleMachine.Command T B)
    (packet : NativeIndexExposureRisk.Packet S A) (nextPacket : NativeIndexExposureRisk.Packet T B)
    (first : CausalStreamExposure.firstRead step packet = CausalStreamExposure.firstRead other nextPacket)
    (history : packet.2 = nextPacket.2) :
    NativeEarlyReceiptPrefixRisk.select step packet = NativeEarlyReceiptPrefixRisk.select other nextPacket := by
  unfold NativeEarlyReceiptPrefixRisk.select
  rw [first,history]

theorem event_congr {S A T B : Type} (step : S → OracleMachine.Command S A) (other : T → OracleMachine.Command T B)
    (packet : NativeIndexExposureRisk.Packet S A) (nextPacket : NativeIndexExposureRisk.Packet T B)
    (selected : NativeEarlyReceiptPrefixRisk.select step packet = NativeEarlyReceiptPrefixRisk.select other nextPacket)
    (profile : Digest) (world : World) :
    NativeEarlyReceiptBound.event profile step packet world ↔ NativeEarlyReceiptBound.event profile other nextPacket world := by
  simp only [NativeEarlyReceiptBound.event,NativeEarlyReceiptBound.finiteEvent,NativeFreshReceiptDigest.program,selected]

theorem absent {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A)
    (selected : NativeEarlyReceiptPrefixRisk.select step packet = none) (profile : Digest) (world : World) :
    ¬NativeEarlyReceiptBound.event profile step packet world := by
  rintro ⟨fuel,occurred⟩
  simp only [NativeEarlyReceiptBound.finiteEvent,NativeFreshReceiptDigest.run_none profile fuel step packet world selected,
    NativeEarlyReceiptBound.matching] at occurred

theorem event_extend {A B : Type} (program : Program A) (next : A → Program B) (position : ℕ) (profile : Digest) (world : World)
    (occurred : NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world) :
    NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position (OracleProgram.bind program next) world).run world := by
  cases chosen : NativeEarlyReceiptPrefixRisk.select OracleProgramMachine.step (runPrefix position program world).run with
  | none => exact False.elim (absent _ _ chosen profile world occurred)
  | some view =>
    obtain ⟨input,selected,_⟩ := NativeEarlyReceiptPrefixRisk.selected_link _ _ view chosen
    obtain ⟨first,atFirst⟩ := ProgramStreamReadCoverage.first program world position input selected
    let extended := ProgramContinuationPrefix.first first next
    have nextFirst := extended.selected
    change CausalStreamExposure.firstRead OracleProgramMachine.step
      (runPrefix first.position (OracleProgram.bind program next) world).run = some input at nextFirst
    rw [atFirst] at nextFirst
    have history : (runPrefix position program world).run.2 = (runPrefix position (OracleProgram.bind program next) world).run.2 := by
      rw [← atFirst]
      exact (congrArg Prod.snd (ProgramContinuationPrefix.active_bind program next first.position world _ first.active)).symm
    have selectEq := select_congr OracleProgramMachine.step OracleProgramMachine.step _ _ (selected.trans nextFirst.symm) history
    exact (event_congr OracleProgramMachine.step OracleProgramMachine.step _ _ selectEq profile world).mp occurred

theorem occurs_extend {A B : Type} (program : Program A) (next : A → Program B) (profile : Digest) (world : World)
    (occurred : ProgramEarlyReceiptWork.Occurs program profile world) :
    ProgramEarlyReceiptWork.Occurs (OracleProgram.bind program next) profile world := by
  obtain ⟨position,early⟩ := occurred
  exact ⟨position,event_extend program next position profile world early⟩

end
end FormalProof4FHE.HasteBoots.ProgramEarlyReceiptContinuation
