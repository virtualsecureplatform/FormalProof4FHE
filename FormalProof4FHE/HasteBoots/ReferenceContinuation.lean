module
public import FormalProof4FHE.HasteBoots.ReferenceLowProbability
@[expose] public section

/-! Non-root reference events persist under exact program continuation.
They keep the selecting request, original log and observation ordinal. -/
namespace FormalProof4FHE.HasteBoots.ReferenceContinuation
open InputIndexedOracle (World)
open OracleProgram (Program bind runPrefix)
noncomputable section

theorem packet {A B : Type} (program : Program A) (next : A → Program B) (position : ℕ) (world : World)
    (active : CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1 ≠ none) :
    (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 ∧
    CausalSeedExposure.request OracleProgramMachine.step (runPrefix position (bind program next) world).run.1 =
      CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1 := by
  cases chosen : (runPrefix position program world).run.1 with
  | inr value => simp only [chosen,CausalSeedExposure.request] at active; contradiction
  | inl tail =>
    cases tail with
    | pure value => simp only [chosen,CausalSeedExposure.request,OracleProgramMachine.step] at active; contradiction
    | start input rest =>
      have same := ProgramContinuationPrefix.active_bind program next position world _ chosen
      rw [same]
      exact ⟨rfl,rfl⟩
    | read input offset count rest =>
      have same := ProgramContinuationPrefix.active_bind program next position world _ chosen
      rw [same]
      exact ⟨rfl,rfl⟩
    | hash input rest =>
      have same := ProgramContinuationPrefix.active_bind program next position world _ chosen
      rw [same]
      exact ⟨rfl,rfl⟩

theorem event {A B : Type} (program : Program A) (next : A → Program B) (position : ℕ) (world : World)
    (occurred : ReferenceMaskedEvents.event OracleProgramMachine.step (runPrefix position program world).run world) :
    ReferenceMaskedEvents.event OracleProgramMachine.step (runPrefix position (bind program next) world).run world := by
  have active : CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1 ≠ none := by
    intro absent
    simp only [ReferenceMaskedEvents.event,ParentSeedCollisionRisk.event,ParentSeedCollisionRisk.select,
      ContextTargetRisk.event,ContextTargetRisk.select,FreshReceiptTargetRisk.event,FreshReceiptTargetRisk.select,
      ReceiptCollisionRisk.event,ReceiptCollisionRisk.select,CausalStreamExposure.firstRead,absent,
      Option.bind_none,false_or] at occurred
  obtain ⟨logEq,requestEq⟩ := packet program next position world active
  simpa only [ReferenceMaskedEvents.event,ParentSeedCollisionRisk.event,ParentSeedCollisionRisk.select,
    ContextTargetRisk.event,ContextTargetRisk.select,FreshReceiptTargetRisk.event,FreshReceiptTargetRisk.select,
    ReceiptCollisionRisk.event,ReceiptCollisionRisk.select,CausalStreamExposure.firstRead,logEq,requestEq] using occurred

theorem other {A B : Type} (program : Program A) (next : A → Program B) (world : World)
    (bad : GlobalReferenceBad.OtherBad program world) : GlobalReferenceBad.OtherBad (bind program next) world := by
  obtain ⟨position,occurred⟩ := (ReferenceLowProbability.other_iff program world).mp bad
  exact (ReferenceLowProbability.other_iff (bind program next) world).mpr ⟨position,event program next position world occurred⟩

end
end FormalProof4FHE.HasteBoots.ReferenceContinuation
