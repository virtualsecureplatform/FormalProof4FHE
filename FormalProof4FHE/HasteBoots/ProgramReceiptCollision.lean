module
public import FormalProof4FHE.HasteBoots.ReceiptCollisionOnset
public import FormalProof4FHE.HasteBoots.ReceiptProgramObservation
public import FormalProof4FHE.HasteBoots.ProgramReceiptCoverage
@[expose] public section

/-! Every collision among receipt keys named in a complete raw program log
is covered by one first-naming collision ledger. Partial reads and hash-only
naming are included. This ledger is separate from fresh receipt guessing and
the existing shared SHA-512 hash bad event. -/
namespace FormalProof4FHE.HasteBoots.ProgramReceiptCollision
open InputIndexedOracle (World law)
open OracleProgram (Program run runPrefix)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def Bad {A : Type} (program : Program A) (world : World) : Prop :=
  ∃ position, ReceiptCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, ReceiptCollisionRisk.risk OracleProgramMachine.step (runPrefix position program world).run

theorem covers {A : Type} (program : Program A) (world : World)
    (collision : ReceiptDigestFixation.Collision (run program world).run.2 world) : Bad program world := by
  obtain ⟨position,entry,raw,found,named,new,old,oldNamed,equal⟩ := ReceiptCollisionOnset.first _ world collision
  have chosen : ReceiptCollisionRisk.select OracleProgramMachine.step (runPrefix position program world).run = some raw := by
    unfold ReceiptCollisionRisk.select
    rw [← Option.bind_assoc,ReceiptProgramObservation.candidate program world position entry found,named]
    simp only [Option.bind_some,ReceiptProgramObservation.history,new,ite_false]
  refine ⟨position,?_⟩
  simp only [ReceiptCollisionRisk.event,chosen]
  exact ⟨old,by simpa only [ReceiptProgramObservation.history] using oldNamed,equal⟩

/-- Collisions in any posterior prefix are covered by the same full-program
ledger, including every round's receipt-candidate fixation alternative. -/
theorem prefix_covers {A : Type} (program : Program A) (world : World) (position : ℕ)
    (collision : ReceiptDigestFixation.Collision (runPrefix position program world).run.2 world) : Bad program world := by
  have included := (OracleProgramMachine.log_prefix_run position program world).sublist
  rw [OracleProgramMachine.take_run] at included
  exact covers program world (ReceiptCollisionOnset.mono _ _ world included collision)

theorem bad_le {A : Type} (program : Program A) :
    law {world | Bad program world} ≤ ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Bad program world} =
      ⋃ position : ℕ, {world | ReceiptCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Bad,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc _ ≤ ∑' position : ℕ, law {world | ReceiptCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
       _ ≤ ∑' position : ℕ, ∫⁻ world, ReceiptCollisionRisk.risk OracleProgramMachine.step (runPrefix position program world).run ∂law :=
         ENNReal.tsum_le_tsum (fun position => ReceiptCollisionRisk.averaged_bound OracleProgramMachine.step (OracleProgram.prefix_replay position program))
       _ = _ := (lintegral_tsum (fun position =>
         (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) (ReceiptCollisionRisk.risk OracleProgramMachine.step)).aemeasurable)).symm

theorem collision_le {A : Type} (program : Program A) :
    law {world | ReceiptDigestFixation.Collision (run program world).run.2 world} ≤ ∫⁻ world, totalCharge program world ∂law :=
  (measure_mono (fun world collision => covers program world collision)).trans (bad_le program)

/-- The root/hash event remains one inherited event; the two SHAKE receipt
risks are added explicitly once over the enclosing program lifetime. -/
theorem combined_le {A : Type} (program : Program A) (inherited : Set World) :
    law ((inherited ∪ {world | ProgramReceiptCoverage.Bad program world}) ∪ {world | Bad program world}) ≤
      (law inherited + ∫⁻ world, ProgramReceiptCoverage.totalCharge program world ∂law) +
        ∫⁻ world, totalCharge program world ∂law :=
  (measure_union_le _ _).trans (add_le_add (ProgramReceiptCoverage.inherited_le program inherited) (bad_le program))

end
end FormalProof4FHE.HasteBoots.ProgramReceiptCollision
