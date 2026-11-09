module
public import FormalProof4FHE.HasteBoots.PrivateCoinNativeMeasurable
@[expose] public section

/-! Finitary private-coin choices in causal machines. Each command may consult
an execution-dependent finite tape prefix. Successive commands can consult
arbitrarily many new coordinates; no global coin or execution cap is imposed.
This is a machine-model theorem, not a Rust randomness implementation bridge. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinMachine
open InputIndexedOracle (World)
open NativeTranscript (Execution)
open PrivateCoinReplay (Tape FiniteUse)
open OracleProgram (Program run)
noncomputable section

def FiniteResult {A : Type} (program : Tape → World → Execution A) : Prop :=
  ∀ tape world, ∃ count : ℕ, ∀ other : Tape,
    (∀ index : Fin count, other index = tape index) →
      (program other world).run = (program tape world).run

def FiniteStep {S A : Type} (step : Tape → S → OracleMachine.Command S A) : Prop :=
  ∀ tape state, ∃ count : ℕ, ∀ other : Tape,
    (∀ index : Fin count, other index = tape index) → step other state = step tape state

theorem agrees_mono {first later : ℕ} (bound : first ≤ later) {tape other : Tape}
    (same : ∀ index : Fin later, other index = tape index) :
    ∀ index : Fin first, other index = tape index :=
  fun index => same ⟨index.val, lt_of_lt_of_le index.isLt bound⟩

theorem finiteResult_finiteUse {A : Type} {program : Tape → World → Execution A}
    (finiteResult : FiniteResult program) : FiniteUse program := by
  intro tape world
  obtain ⟨count, fixed⟩ := finiteResult tape world
  exact ⟨count, fun other same => congrArg Prod.snd (fixed other same)⟩

theorem bind_finiteResult {A B : Type} {first : Tape → World → Execution A}
    {next : A → Tape → World → Execution B} (before : FiniteResult first)
    (after : ∀ value, FiniteResult (next value)) :
    FiniteResult (fun tape world => first tape world >>= fun value => next value tape world) := by
  intro tape world
  obtain ⟨firstCount, firstFixed⟩ := before tape world
  obtain ⟨nextCount, nextFixed⟩ := after (first tape world).run.1 tape world
  refine ⟨max firstCount nextCount, ?_⟩
  intro other same
  have firstSame := firstFixed other (agrees_mono (Nat.le_max_left _ _) same)
  have nextSame := nextFixed other (agrees_mono (Nat.le_max_right _ _) same)
  rw [ObservationReplay.run_bind, ObservationReplay.run_bind, firstSame, nextSame]

/-- Finite analysis prefixes use finitely many private coordinates even when
later command choices depend on all earlier oracle responses. -/
theorem take_finiteResult {S A : Type} {step : Tape → S → OracleMachine.Command S A}
    (finiteStep : FiniteStep step) (fuel : ℕ) (state : S) :
    FiniteResult (fun tape => run (OracleMachine.take (step tape) fuel state)) := by
  induction fuel generalizing state with
  | zero =>
    intro tape world
    obtain ⟨count, fixed⟩ := finiteStep tape state
    refine ⟨count, ?_⟩
    intro other same
    simp only [OracleMachine.take, fixed other same]
  | succ fuel ih =>
    intro tape world
    obtain ⟨count, fixed⟩ := finiteStep tape state
    cases chosen : step tape state with
    | done value =>
      refine ⟨count, ?_⟩
      intro other same
      simp only [OracleMachine.take, fixed other same, chosen]
    | start input next =>
      obtain ⟨nextCount, nextFixed⟩ := ih next tape world
      refine ⟨max count nextCount, ?_⟩
      intro other same
      have commandSame := (fixed other (agrees_mono (Nat.le_max_left _ _) same)).trans chosen
      have nextSame := nextFixed other (agrees_mono (Nat.le_max_right _ _) same)
      simp only [OracleMachine.take, commandSame, chosen, OracleProgram.run,
        ObservationReplay.run_bind, ObservationReplay.start, WriterT.run_mk]
      rw [nextSame]
    | read input offset size next =>
      obtain ⟨nextCount, nextFixed⟩ := ih (next (InputIndexedOracle.bytes world input offset size)) tape world
      refine ⟨max count nextCount, ?_⟩
      intro other same
      have commandSame := (fixed other (agrees_mono (Nat.le_max_left _ _) same)).trans chosen
      have nextSame := nextFixed other (agrees_mono (Nat.le_max_right _ _) same)
      simp only [OracleMachine.take, commandSame, chosen, OracleProgram.run,
        ObservationReplay.run_bind, ObservationReplay.read, WriterT.run_mk]
      rw [nextSame]
    | hash input next =>
      obtain ⟨nextCount, nextFixed⟩ := ih (next (InputIndexedOracle.sha512 world input)) tape world
      refine ⟨max count nextCount, ?_⟩
      intro other same
      have commandSame := (fixed other (agrees_mono (Nat.le_max_left _ _) same)).trans chosen
      have nextSame := nextFixed other (agrees_mono (Nat.le_max_right _ _) same)
      simp only [OracleMachine.take, commandSame, chosen, OracleProgram.run,
        ObservationReplay.run_bind, ObservationReplay.hash, WriterT.run_mk]
      rw [nextSame]

theorem history_finiteUse {S A : Type} {prelude : Tape → Program S}
    {step : Tape → S → OracleMachine.Command S A}
    (before : FiniteResult (fun tape => run (prelude tape))) (finiteStep : FiniteStep step)
    (fuel : ℕ) :
    FiniteUse (fun tape => CausalExposureLifetime.history (run (prelude tape)) id (step tape) fuel) := by
  exact finiteResult_finiteUse (bind_finiteResult before (fun state => take_finiteResult finiteStep fuel state))

theorem failure_measurable {S A : Type} (Memory : Type) (dummy : NativeRootMessage.Digest)
    (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (prelude : Tape → Program S)
    (step : Tape → S → OracleMachine.Command S A)
    (before : FiniteResult (fun tape => run (prelude tape))) (finiteStep : FiniteStep step) :
    MeasurableSet (PrivateCoinLifetime.failure Memory dummy ctx radius prelude step) :=
  PrivateCoinNativeMeasurable.failure_measurable Memory dummy ctx radius prelude step
    (history_finiteUse before finiteStep)
end
end FormalProof4FHE.HasteBoots.PrivateCoinMachine
