module
import all FormalProof4FHE.HasteBoots.CalibratedReferencePcsLedger
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke

namespace FormalProof4FHE.HasteBoots.ReferenceProbabilitySmoke
open InputIndexedOracle (World)
open OracleProgram (Program runPrefix)
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

/-- The zero analysis threshold excludes low events, without constraining
any part of the actual program. -/
theorem zero_mask {A : Type} (program : Program A) (world : World) : ¬ReferenceLowProbability.Low program 0 world := by
  rintro ⟨position,small,_⟩
  exact Nat.not_lt_zero _ small.1

/-- Completion of a pure program cannot create any of the four reference
bad events, even though posterior completion is used in their proofs. -/
theorem pure_safe {A : Type} (value : A) (world : World) : ¬GlobalReferenceBad.OtherBad (.pure value) world := by
  rw [ReferenceLowProbability.other_iff]
  rintro ⟨position,occurred⟩
  have absent := ProgramObservationClock.request_after_length (.pure value) world position (Nat.zero_le _)
  simp only [ReferenceMaskedEvents.event,ParentSeedCollisionRisk.event,ParentSeedCollisionRisk.select,
    ContextTargetRisk.event,ContextTargetRisk.select,FreshReceiptTargetRisk.event,FreshReceiptTargetRisk.select,
    ReceiptCollisionRisk.event,ReceiptCollisionRisk.select,CausalStreamExposure.firstRead,absent,
    Option.bind_none,false_or] at occurred

/-- Starts, empty reads and hashes in the original selecting history are
retained by the strict low-prefix mask. It changes exactly at its boundary. -/
theorem strict_boundary :
    ReferenceMaskedEvents.small 4 (runPrefix 3 FactorFiberSmoke.program worldZero).run ∧
    ¬ReferenceMaskedEvents.small 3 (runPrefix 3 FactorFiberSmoke.program worldZero).run := by
  constructor
  · exact ⟨by decide +kernel,by decide +kernel⟩
  · intro eligible
    have impossible : 3 < 3 := eligible.1
    omega

end
end FormalProof4FHE.HasteBoots.ReferenceProbabilitySmoke
