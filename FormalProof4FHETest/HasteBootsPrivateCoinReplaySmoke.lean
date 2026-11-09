module
import FormalProof4FHE.HasteBoots.PrivateCoinMachine
import all FormalProof4FHETest.HasteBootsLifetimeSoundnessSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (World)
open PrivateCoinReplay (Tape)
open OracleProgram (Program run)
namespace HasteBootsPrivateCoinReplaySmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (ctx root primitive usize)
open HasteBootsLifetimeSoundnessSmoke (nativePrelude)
local instance : NeZero ctx.parameters.code.blockWidth.val := ⟨by decide +kernel⟩

-- An actual native verifier prelude, followed by a private initial cursor.
def before (tape : Tape) : Program ℕ :=
  OracleProgram.bind nativePrelude (fun _ => .pure (tape 0).val)

-- Each oracle response selects a later private coordinate. The state can
-- grow forever; no fixed prefix of the tape fixes the whole strategy.
def step (tape : Tape) (cursor : ℕ) : OracleMachine.Command ℕ Unit :=
  .read [tape cursor] cursor 1 (fun output => cursor + 1 + (output.headD 0).val)

theorem before_finite : PrivateCoinMachine.FiniteResult (fun tape => run (before tape)) := by
  intro tape world
  refine ⟨1, ?_⟩
  intro other same
  have zero := same ⟨0, by decide⟩
  simp only [before, OracleProgram.run_bind, ObservationReplay.run_bind, OracleProgram.run]
  rw [zero]

theorem step_finite : PrivateCoinMachine.FiniteStep step := by
  intro tape cursor
  refine ⟨cursor + 1, ?_⟩
  intro other same
  have byte := same ⟨cursor, Nat.lt_succ_self cursor⟩
  simp only [step, byte]

-- There is no single finite tape prefix that fixes all commands.
example (count : ℕ) : ∃ left right : Tape,
    (∀ index : Fin count, left index = right index) ∧ step left count ≠ step right count := by
  refine ⟨(fun _ => 0), (fun index => if index = count then 1 else 0), ?_, ?_⟩
  · intro index
    simp [Nat.ne_of_lt index.isLt]
  · simp [step]

example (fuel : ℕ) : PrivateCoinReplay.FiniteUse
    (fun tape => CausalExposureLifetime.history (run (before tape)) id (step tape) fuel) :=
  PrivateCoinMachine.history_finiteUse before_finite step_finite fuel

example : MeasurableSet (PrivateCoinLifetime.failure Unit root ctx 0 before step) :=
  PrivateCoinMachine.failure_measurable Unit root ctx 0 before step before_finite step_finite

def tapeLaw : Measure Tape := Measure.infinitePi (fun _ : ℕ => InputIndexedOracle.byteLaw)
example : IsProbabilityMeasure tapeLaw := by unfold tapeLaw; infer_instance

-- The native lifetime bound on an infinite random byte tape now has no
-- external joint-measurability premise and no bound on total coin use.
example : (tapeLaw.prod InputIndexedOracle.law) (PrivateCoinLifetime.failure Unit root ctx 0 before step) ≤
    ∫⁻ tape, PrivateCoinLifetime.charge root ctx primitive 0 before step tape ∂tapeLaw :=
  PrivateCoinLifetime.prelude_bound tapeLaw Unit root ctx primitive ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchMeaningSmoke.constructed 0 (by decide +kernel) before step
    Fintype.card_pos (by rw [BlockCode.minDist _ _ _ (by decide +kernel)]; decide +kernel)
    (PrivateCoinMachine.failure_measurable Unit root ctx 0 before step before_finite step_finite)
end
end HasteBootsPrivateCoinReplaySmoke
