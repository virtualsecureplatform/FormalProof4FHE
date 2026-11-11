module
import all FormalProof4FHE.HasteBoots.CanonicalIdentityWork
import all FormalProof4FHETest.HasteBootsPrivateCoinScalarSmoke

namespace HasteBootsCanonicalScalarSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

theorem absent {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : NativeRootMessage.Digest)
    (none : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run = .none) :
    ¬∃ input ordinal, CanonicalAttainableEvent.Event program position input ordinal dummy world := by
  rintro ⟨input,ordinal,⟨packet,_⟩⟩
  have selected := packet.classed.val.first.selected
  rw [packet.classed.val.first_position,none] at selected
  cases selected

-- Completion cannot produce a new canonical healing event at any position.
theorem pure_empty {A : Type} (value : A) (world : World) (dummy : NativeRootMessage.Digest) :
    ¬CanonicalScalarLifetime.Event (Program.pure value) dummy world := by
  rintro ⟨position,input,ordinal,event⟩
  have none : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position (Program.pure value) world).run = .none := by
    cases position <;> rfl
  exact absent _ position world dummy none ⟨input,ordinal,event⟩

-- Consuming real private coins is silent in the original oracle clock.
theorem coin_only (dummy : NativeRootMessage.Digest) :
    ¬PrivateCoinCanonicalScalarProbability.Event PrivateCoinScalarSmoke.code [] (fun _ => []) dummy 2
      (PrivateCoinScalarSmoke.changed,worldZero) := by
  exact pure_empty _ worldZero dummy

def repeated : Program Unit := .read [17] 999 1 (fun _ => .read [17] 0 1 (fun _ => .pure ()))

-- A later positive read of an already exposed input is not charged again.
theorem repeat_excluded (dummy : NativeRootMessage.Digest) :
    ¬∃ input ordinal, CanonicalAttainableEvent.Event repeated 1 input ordinal dummy worldZero :=
  absent repeated 1 worldZero dummy (by decide +kernel)

def emptyFirst : Program Unit := .read [17] 9000 0 (fun _ => .read [17] 999 1 (fun _ => .pure ()))

-- Empty outputs do not create an attained canonical scalar candidate.
theorem empty_excluded (dummy : NativeRootMessage.Digest) :
    ¬∃ input ordinal, CanonicalAttainableEvent.Event emptyFirst 0 input ordinal dummy worldZero :=
  absent emptyFirst 0 worldZero dummy (by decide +kernel)

end
end HasteBootsCanonicalScalarSmoke
