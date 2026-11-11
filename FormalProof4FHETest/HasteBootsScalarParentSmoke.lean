module
import all FormalProof4FHE.HasteBoots.OriginalScalarReceiptPosition
import all FormalProof4FHETest.HasteBootsScalarCompletedSmoke

namespace FormalProof4FHE.HasteBoots.ScalarParentSmoke
open InputIndexedOracle (World)
open ScalarReplaySmoke (statement proof)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open ScalarExecutionRecoverySmoke (before decoded domain)
open ScalarCompletedSmoke (execution firstEntry secondEntry firstMember secondMember)
noncomputable section

def reader (fuel : ℕ) (world : World) (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (execution fuel world).1.completed) : ScalarParentRecovery.Completed where
  transcript := child
  statement := statement
  proof := proof
  world := world
  fuel := fuel
  entry := entry
  framed := ⟨before,decoded⟩
  accepted := ⟨NativeScalarBatchWire.bindStatement child statement,rfl⟩
  statementFits := by decide +kernel
  domain := domain
  member := member

def first := reader 9 worldZero firstEntry firstMember
def second := reader 9 worldZero secondEntry secondMember

/-- The recovered second-round parent is the original pre-statement child,
not the state after the first round and its completed receipt. -/
theorem second_parent : TranscriptFrame.encodeMany ScalarRecoverySmoke.recovered.view.history.before = child.input := by
  have input : second.entry.coefficients.phase.pending.input = ScalarReplaySmoke.target := by decide +kernel
  have found : ScalarRecoveredReplay.recover second.entry.coefficients.phase.pending.input = some ScalarRecoverySmoke.recovered := by
    rw [input]
    exact ScalarRecoverySmoke.found
  exact (ScalarParentRecovery.parent_of_found second ScalarRecoverySmoke.recovered found).1

/-- Changing every SHA-512 coordinate gives a different world while keeping
this native scalar reader's SHAKE-only history and completed input equal. -/
def clone : World
  | .inl _ => 0
  | .inr _ => 1

example : worldZero ≠ clone := by
  intro equal
  have byte := congrFun equal (.inr ([],0))
  change (0 : InputIndexedOracle.Byte) = 1 at byte
  contradiction

def cloneEntry := (execution 9 clone).1.completed[0]'(by decide +kernel)
def cloned := reader 9 clone cloneEntry (List.getElem_mem _)

theorem same_input : first.entry.coefficients.phase.pending.input = cloned.entry.coefficients.phase.pending.input := by decide +kernel

theorem cross_world_parent : first.transcript.input = cloned.transcript.input ∧
    first.statement = cloned.statement ∧ first.entry.packet = cloned.entry.packet :=
  ScalarParentRecovery.compare first cloned same_input

/-- Parent recovery is also derived for the retained mixed rejection record;
its consumed-byte count differs from the all-accepted fixture. -/
example : ∃ configuration : ScalarRecoveredReplay.Configuration,
    ScalarRecoveredReplay.recover ScalarCompletedSmoke.mixedEntry.coefficients.phase.pending.input = some configuration ∧
    TranscriptFrame.encodeMany configuration.view.history.before = child.input ∧
    configuration.view.history.statement = statement ∧ configuration.view.packet = ScalarCompletedSmoke.mixedEntry.packet :=
  ScalarParentRecovery.recover (reader 11 ScalarCompletedSmoke.worldOneReject ScalarCompletedSmoke.mixedEntry ScalarCompletedSmoke.mixedMember)

end
end FormalProof4FHE.HasteBoots.ScalarParentSmoke
