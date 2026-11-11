module
public import FormalProof4FHE.HasteBoots.ParentSeedCollisionOnset
public import FormalProof4FHE.HasteBoots.ParentSeedObservation
public import FormalProof4FHE.HasteBoots.ProgramReceiptCollision
@[expose] public section

/-! One program-wide lifetime charge covers collisions between recognized
parent-seed inputs. The seed, receipt and shared hash bad events stay distinct. -/
namespace FormalProof4FHE.HasteBoots.ProgramParentSeedCollision
open InputIndexedOracle (World law)
open OracleProgram (Program run runPrefix)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def Bad {A : Type} (program : Program A) (world : World) : Prop :=
  ∃ position, ParentSeedCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, ParentSeedCollisionRisk.risk OracleProgramMachine.step (runPrefix position program world).run

theorem covers {A : Type} (program : Program A) (world : World)
    (collision : ParentSeedCollisionRisk.Collision (run program world).run.2 world) : Bad program world := by
  obtain ⟨position,entry,raw,found,named,new,old,oldNamed,equal⟩ := ParentSeedCollisionOnset.first _ world collision
  have chosen : ParentSeedCollisionRisk.select OracleProgramMachine.step (runPrefix position program world).run = some raw := by
    unfold ParentSeedCollisionRisk.select
    rw [← Option.bind_assoc,ParentSeedObservation.candidate program world position entry found,named]
    simp only [Option.bind_some,ReceiptProgramObservation.history,new,ite_false]
  refine ⟨position,?_⟩
  simp only [ParentSeedCollisionRisk.event,chosen]
  exact ⟨old,by simpa only [ReceiptProgramObservation.history] using oldNamed,equal⟩

/-- Parent-seed collisions in any posterior prefix are covered by the same
full-program ledger, including earlier cross-world parent matching. -/
theorem prefix_covers {A : Type} (program : Program A) (world : World) (position : ℕ)
    (collision : ParentSeedCollisionRisk.Collision (runPrefix position program world).run.2 world) : Bad program world := by
  have included := (OracleProgramMachine.log_prefix_run position program world).sublist
  rw [OracleProgramMachine.take_run] at included
  exact covers program world (ParentSeedCollisionOnset.mono _ _ world included collision)

theorem bad_le {A : Type} (program : Program A) :
    law {world | Bad program world} ≤ ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Bad program world} =
      ⋃ position : ℕ, {world | ParentSeedCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Bad,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc _ ≤ ∑' position : ℕ, law {world | ParentSeedCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
       _ ≤ ∑' position : ℕ, ∫⁻ world, ParentSeedCollisionRisk.risk OracleProgramMachine.step (runPrefix position program world).run ∂law :=
         ENNReal.tsum_le_tsum (fun position => ParentSeedCollisionRisk.averaged_bound OracleProgramMachine.step (OracleProgram.prefix_replay position program))
       _ = _ := (lintegral_tsum (fun position =>
         (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) (ParentSeedCollisionRisk.risk OracleProgramMachine.step)).aemeasurable)).symm

theorem collision_le {A : Type} (program : Program A) :
    law {world | ParentSeedCollisionRisk.Collision (run program world).run.2 world} ≤ ∫⁻ world, totalCharge program world ∂law :=
  (measure_mono (fun world collision => covers program world collision)).trans (bad_le program)

/-- Add the parent-seed collision charge once, preserving the existing
combined root/hash and two receipt-event charges. -/
theorem combined_le {A : Type} (program : Program A) (inherited : Set World) :
    law (((inherited ∪ {world | ProgramReceiptCoverage.Bad program world}) ∪
      {world | ProgramReceiptCollision.Bad program world}) ∪ {world | Bad program world}) ≤
      ((law inherited + ∫⁻ world, ProgramReceiptCoverage.totalCharge program world ∂law) +
        ∫⁻ world, ProgramReceiptCollision.totalCharge program world ∂law) +
          ∫⁻ world, totalCharge program world ∂law :=
  (measure_union_le _ _).trans (add_le_add (ProgramReceiptCollision.combined_le program inherited) (bad_le program))

end
end FormalProof4FHE.HasteBoots.ProgramParentSeedCollision
