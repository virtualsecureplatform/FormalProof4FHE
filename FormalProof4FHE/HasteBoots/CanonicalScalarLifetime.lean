module
public import FormalProof4FHE.HasteBoots.CanonicalScalarPositionKernel
@[expose] public section

/-! Canonical healing over all actual raw positions has the existing
specified scalar work charge, outside one shared reference bad ledger. -/
namespace FormalProof4FHE.HasteBoots.CanonicalScalarLifetime
open InputIndexedOracle (Input World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event {A : Type} (program : Program A) (dummy : Digest) (world : World) : Prop :=
  ∃ position input ordinal, CanonicalAttainableEvent.Event program position input ordinal dummy world

abbrev totalCharge := @ScalarLifetimeComposition.totalCharge

theorem safe_bound {A : Type} (program : Program A) (dummy : Digest) :
    law {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} =
      ⋃ position : ℕ, {world | CanonicalScalarPositionKernel.Event program position dummy world} := by
    ext world
    simp only [Event,CanonicalScalarPositionKernel.Event,CanonicalSafeIdentityKernel.Event,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨position,input,ordinal,occurred⟩,safe⟩
      exact ⟨position,input,ordinal,occurred,safe⟩
    · rintro ⟨position,input,ordinal,occurred,safe⟩
      exact ⟨⟨position,input,ordinal,occurred⟩,safe⟩
  rw [union]
  have included := (measure_iUnion_le (fun position : ℕ => {world | CanonicalScalarPositionKernel.Event program position dummy world}) (μ := law)).trans
    (ENNReal.tsum_le_tsum (fun position => CanonicalScalarPositionKernel.bound program position dummy))
  unfold totalCharge ScalarLifetimeComposition.totalCharge
  rw [lintegral_tsum (fun position => (ScalarPositionKernel.charge_measurable program position).aemeasurable)]
  exact included


theorem private_safe_probability (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (dummy : Digest) :
    let program := InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel
    law {world | Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * ScalarEquationWork.rate := by
  dsimp only
  apply (safe_bound _ dummy).trans
  calc
    _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * ScalarEquationWork.rate ∂law := by
      apply lintegral_mono
      intro world
      exact (ByteScalarLogWork.private_prefix_charge _ _ _ _ _ _).trans
        (mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) le_rfl)
    _ = _ := lintegral_mul_const ScalarEquationWork.rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

end
end FormalProof4FHE.HasteBoots.CanonicalScalarLifetime
