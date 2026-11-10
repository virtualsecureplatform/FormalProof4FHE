module
import FormalProof4FHE.HasteBoots.ConstructedGoldAnyProfileSecurity
import all FormalProof4FHE.HasteBoots.ProfileMetadataErasure
import all FormalProof4FHE.HasteBoots.NativeFieldVector
import all FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler
import all FormalProof4FHE.HasteBoots.CanonicalByteSampler
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.InputIndexedOracle
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open NativeRootMessage (Digest)
namespace HasteBootsAnyProfileSmoke

def world : World := fun coordinate => match coordinate with
  | .inl (_,offset) => if offset % 2 = 0 then 255 else 7
  | .inr _ => 0

def initial : NativeFieldVector.State :=
  NativeFieldVector.initial ⟨⟨[42], fun _ => 0⟩, [3], []⟩ 2

-- Real rejection/suspension and resumption: only metadata changes; the same
-- bytes, candidate decisions, ordered values and observations survive.
/-- info: true -/
#guard_msgs in
#eval
  let first := NativeFieldVector.execute 251 1 initial world
  let later := NativeFieldVector.execute 251 3 first.1 world
  let changed := NativeFieldVector.execute 251 4 (ProfileMetadataErasure.state initial (fun _ => 9)) world
  first.1.remaining == 2 && first.1.values == [] && first.1.phase.consumed == [255] &&
    later.1.remaining == 0 && later.1.values == [7,7] &&
    changed.1.values == later.1.values && changed.1.phase.consumed == later.1.phase.consumed &&
    changed.2 == first.2 ++ later.2 && changed.1.phase.pending.profile 0 == 9

-- Zero fuel and a completed collector retain their states and issue no reads.
/-- info: true -/
#guard_msgs in
#eval
  let paused := NativeFieldVector.execute 251 0 (ProfileMetadataErasure.state initial (fun _ => 9)) world
  let completed := NativeFieldVector.execute 251 4 initial world
  let stopped := NativeFieldVector.execute 251 100 (ProfileMetadataErasure.state completed.1 (fun _ => 9)) world
  paused.1.phase.consumed == [] && paused.2 == [] && stopped.2 == [] &&
    stopped.1.values == [7,7] && stopped.1.phase.pending.profile 0 == 9

noncomputable section

-- The union over every profile is measurable, without a supplied selector.
example (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) :
    MeasurableSet {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} :=
  ConstructedGoldAnyProfileSecurity.failure_measurable Memory code publicData privateData dummy registered

example (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (descriptor : Input) :
    MeasurableSet {execution : Tape × World |
      ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered
        (InputIndexedOracle.sha512 execution.2 descriptor) execution} :=
  ConstructedGoldAnyProfileSecurity.selected_failure_measurable Memory code publicData privateData dummy registered
    (fun execution => InputIndexedOracle.sha512 execution.2 descriptor)
    ((InputIndexedOracle.hash_measurable descriptor).comp measurable_snd)

-- Even a profile derived from this oracle world's SHA-512 output fits the
-- same work allowance; independence of the profile from the world is absent.
example (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (descriptor : Input)
    (bounded : registered.registry.val.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution : Tape × World |
      ConstructedGoldRegisteredSecurity.Failure Memory code publicData privateData dummy registered
        (InputIndexedOracle.sha512 execution.2 descriptor) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  apply (mul_le_mul' le_rfl (measure_mono (fun execution failed =>
    (show ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution from
      ⟨InputIndexedOracle.sha512 execution.2 descriptor, failed⟩)))).trans
  exact ConstructedGoldAnyProfileSecurity.work_bound coins Memory code publicData privateData dummy registered bounded
end
end HasteBootsAnyProfileSmoke
