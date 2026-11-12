module
public import FormalProof4FHE.HasteBoots.OffsetWorkPosition
public import FormalProof4FHE.HasteBoots.ByteScalarLogWork
@[expose] public section

/-! Adaptive reciprocal first-read positions compose after excluding the one
global bad ledger. Charges are selected by the actual original prefix and
selected key bytes; no query, retry, job-count or lifetime cutoff is imposed. -/
namespace FormalProof4FHE.HasteBoots.OffsetLifetimeWork
open InputIndexedOracle (Input World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event {A : Type} (program : Program A) (dummy : Digest) (world : World) : Prop :=
  ∃ position input ordinal cost, OffsetClassKernel.Event program position input ordinal cost dummy world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, OffsetWorkPosition.charge program position world

theorem safe_bound {A : Type} (program : Program A) (dummy : Digest) :
    law {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} =
      ⋃ position : ℕ, {world | OffsetWorkPosition.Event program position dummy world} := by
    ext world
    simp only [Event,OffsetWorkPosition.Event,OffsetPositionKernel.SafeEvent,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨position,input,ordinal,cost,occurred⟩,safe⟩
      exact ⟨position,input,ordinal,cost,occurred,safe⟩
    · rintro ⟨position,input,ordinal,cost,occurred,safe⟩
      exact ⟨⟨position,input,ordinal,cost,occurred⟩,safe⟩
  rw [union]
  have included := (measure_iUnion_le (fun position : ℕ => {world | OffsetWorkPosition.Event program position dummy world}) (μ := law)).trans
    (ENNReal.tsum_le_tsum (fun position => OffsetWorkPosition.bound program position dummy))
  unfold totalCharge
  rw [lintegral_tsum (fun position => (OffsetWorkPosition.charge_measurable program position).aemeasurable)]
  exact included

theorem bound {A : Type} (program : Program A) (dummy : Digest) :
    law {world | Event program dummy world} ≤
      law {world | NativeRootFamilyLifetime.Bad dummy (OracleProgram.run program world).run.2} +
        GlobalReferenceBad.otherCharge program + ∫⁻ world, totalCharge program world ∂law := by
  have included : {world | Event program dummy world} ⊆
      {world | GlobalReferenceBad.Bad program dummy world} ∪
        {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} := by
    intro world occurred
    by_cases bad : GlobalReferenceBad.Bad program dummy world
    · exact Or.inl bad
    · exact Or.inr ⟨occurred,bad⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans
    (add_le_add (GlobalReferenceBad.bad_le program dummy) (safe_bound program dummy)))

theorem charge_eq {A : Type} (program : Program A) (world : World) :
    totalCharge program world = ScalarEquationWork.totalBytes program world * LookupStreamWorkRate.rate := by
  simp only [totalCharge,OffsetWorkPosition.charge,OffsetWorkPosition.score,ScalarEquationWork.totalBytes,ENNReal.tsum_mul_right]

theorem program_charge {A : Type} (program : Program A) (world : World) :
    totalCharge program world ≤ (ScalarLogWork.bytes (OracleProgram.run program world).run.2 : ENNReal)*LookupStreamWorkRate.rate := by
  rw [charge_eq]
  exact mul_le_mul' (ScalarLogWork.program_bytes program world) le_rfl

theorem private_prefix_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (fuel : ℕ) (state : PrivateCoinByteMachine.State) (world : World) :
    totalCharge (PrivateCoinByteMachine.take code publicData tape fuel state) world ≤
      ((OracleProgram.run (PrivateCoinByteMachine.take code publicData tape fuel state) world).run.1.work : ENNReal)*LookupStreamWorkRate.rate :=
  (program_charge _ _).trans (mul_le_mul' (Nat.cast_le.mpr (ByteScalarLogWork.private_prefix_bytes _ _ _ _ _ _)) le_rfl)

theorem private_safe_probability (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) (dummy : Digest) :
    let program := PrivateCoinByteMachine.take code publicData tape fuel (PrivateCoinByteMachine.initialise code privateData)
    law {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * LookupStreamWorkRate.rate := by
  dsimp only
  apply (safe_bound _ dummy).trans
  calc
    _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * LookupStreamWorkRate.rate ∂law := by
      apply lintegral_mono
      intro world
      exact (private_prefix_charge _ _ _ _ _ _).trans
        (mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) le_rfl)
    _ = _ := lintegral_mul_const LookupStreamWorkRate.rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

end
end FormalProof4FHE.HasteBoots.OffsetLifetimeWork
