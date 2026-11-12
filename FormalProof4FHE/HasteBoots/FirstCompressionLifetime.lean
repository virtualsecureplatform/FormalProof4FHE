module
public import FormalProof4FHE.HasteBoots.FirstCompressionWorkPosition
public import FormalProof4FHE.HasteBoots.OffsetLifetimeWork
@[expose] public section

/-! Original first-compression events over all selecting positions pay the
same specified byte-work potential as reciprocal events, without recharging
shared parent table payloads or multiplying by request repetitions. -/
namespace FormalProof4FHE.HasteBoots.FirstCompressionLifetime
open InputIndexedOracle (Input World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event {A : Type} (program : Program A) (dummy : Digest) (world : World) : Prop :=
  ∃ position, FirstCompressionWorkPosition.Event program position dummy world

theorem safe_bound {A : Type} (program : Program A) (dummy : Digest) :
    law {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      ∫⁻ world, OffsetLifetimeWork.totalCharge program world ∂law := by
  have union : {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} =
      ⋃ position : ℕ, {world | FirstCompressionWorkPosition.SafeEvent program position dummy world} := by
    ext world
    simp only [Event,FirstCompressionWorkPosition.SafeEvent,Set.mem_ofPred_eq,Set.mem_iUnion,exists_and_right]
  rw [union]
  have included := (measure_iUnion_le (fun position : ℕ => {world | FirstCompressionWorkPosition.SafeEvent program position dummy world}) (μ := law)).trans
    (ENNReal.tsum_le_tsum (fun position => FirstCompressionWorkPosition.bound program position dummy))
  unfold OffsetLifetimeWork.totalCharge
  rw [lintegral_tsum (fun position => (OffsetWorkPosition.charge_measurable program position).aemeasurable)]
  exact included

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
      exact (OffsetLifetimeWork.private_prefix_charge _ _ _ _ _ _).trans
        (mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) le_rfl)
    _ = _ := lintegral_mul_const LookupStreamWorkRate.rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

end
end FormalProof4FHE.HasteBoots.FirstCompressionLifetime
