module
public import FormalProof4FHE.HasteBoots.AllocatedOpeningLifetimeBound
@[expose] public section

/-! One complete-history bad-event ledger excludes every prefix reference
bad event. Non-root lifetime charges stay separate so the full-history hash
event can be shared with PCS composition. -/
namespace FormalProof4FHE.HasteBoots.GlobalReferenceBad
open InputIndexedOracle (World law)
open OracleProgram (Program run runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def OtherBad {A : Type} (program : Program A) (world : World) : Prop :=
  ProgramParentSeedCollision.Bad program world ∨ ProgramContextTarget.Bad program world ∨
    ProgramReceiptCoverage.Bad program world ∨ ProgramReceiptCollision.Bad program world

def Bad {A : Type} (program : Program A) (dummy : Digest) (world : World) : Prop :=
  NativeRootFamilyLifetime.Bad dummy (run program world).run.2 ∨ OtherBad program world

theorem root_prefix {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World)
    (bad : NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2) :
    NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  have growing := OracleProgramMachine.log_prefix_run position program world
  rw [OracleProgramMachine.take_run] at growing
  exact NativeRootFamilyAudit.bad_persistent dummy world _ _ (OracleProgram.run_replay program |>.truthful world) growing bad

theorem good {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World)
    (safe : ¬Bad program dummy world) : JobReferenceFixation.Good program position world dummy := by
  constructor
  · intro bad; exact safe (Or.inr (Or.inl bad))
  · intro bad; exact safe (Or.inl (root_prefix program position dummy world bad))
  · intro bad; exact safe (Or.inr (Or.inr (Or.inl bad)))
  · intro bad; exact safe (Or.inr (Or.inr (Or.inr (Or.inl bad))))
  · intro bad; exact safe (Or.inr (Or.inr (Or.inr (Or.inr bad))))

theorem other_measurable {A : Type} (program : Program A) : MeasurableSet {world | OtherBad program world} := by
  simpa only [OtherBad,Set.ofPred_or] using (ReferenceBadLedger.parent_measurable program).union
    ((ProgramContextTarget.bad_measurable program).union ((ReferenceBadLedger.receipt_measurable program).union (ReferenceBadLedger.collision_measurable program)))

theorem root_measurable {A : Type} (program : Program A) (dummy : Digest) :
    MeasurableSet {world | NativeRootFamilyLifetime.Bad dummy (run program world).run.2} := by
  apply OracleProgramHistory.event_measurable (OracleProgram.run_replay program) (fun packet _ => NativeRootFamilyLifetime.Bad dummy packet.2)
  intro packet
  by_cases bad : NativeRootFamilyLifetime.Bad dummy packet.2 <;> simp [bad]

theorem measurable {A : Type} (program : Program A) (dummy : Digest) : MeasurableSet {world | Bad program dummy world} := by
  simpa only [Bad,Set.ofPred_or] using (root_measurable program dummy).union (other_measurable program)

def otherCharge {A : Type} (program : Program A) : ENNReal :=
  (∫⁻ world, ProgramParentSeedCollision.totalCharge program world ∂law) +
    ((∫⁻ world, ProgramContextTarget.totalCharge program world ∂law) +
      ((∫⁻ world, ProgramReceiptCoverage.totalCharge program world ∂law) + ∫⁻ world, ProgramReceiptCollision.totalCharge program world ∂law))

theorem other_le {A : Type} (program : Program A) : law {world | OtherBad program world} ≤ otherCharge program := by
  simp only [OtherBad,Set.ofPred_or,otherCharge]
  exact (measure_union_le _ _).trans (add_le_add (ProgramParentSeedCollision.bad_le program)
    ((measure_union_le _ _).trans (add_le_add (ProgramContextTarget.bad_le program)
      ((measure_union_le _ _).trans (add_le_add (ProgramReceiptCoverage.bad_le program) (ProgramReceiptCollision.bad_le program))))))

theorem bad_le {A : Type} (program : Program A) (dummy : Digest) : law {world | Bad program dummy world} ≤
    law {world | NativeRootFamilyLifetime.Bad dummy (run program world).run.2} + otherCharge program := by
  exact (measure_union_le _ _).trans (add_le_add le_rfl (other_le program))

end
end FormalProof4FHE.HasteBoots.GlobalReferenceBad
