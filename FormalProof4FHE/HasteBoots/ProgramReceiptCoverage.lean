module
public import FormalProof4FHE.HasteBoots.LoggedLookupFactorSamples
public import FormalProof4FHE.HasteBoots.FreshReceiptTargetLifetime
@[expose] public section

/-! One fresh-receipt ledger for all prefixes of an enclosing oracle program.
Outside this event, every logged factor sample has its raw payload named by
its outer scalar first read. The ledger is a probability charge, not work. -/
namespace FormalProof4FHE.HasteBoots.ProgramReceiptCoverage
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def Bad {A : Type} (program : Program A) (world : World) : Prop :=
  ∃ position, FreshReceiptTargetRisk.event OracleProgramMachine.step (runPrefix position program world).run world

def totalCharge {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, FreshReceiptTargetRisk.risk OracleProgramMachine.step (runPrefix position program world).run

theorem bad_le {A : Type} (program : Program A) :
    law {world | Bad program world} ≤ ∫⁻ world, totalCharge program world ∂law := by
  have union : {world | Bad program world} =
      ⋃ position : ℕ, {world | FreshReceiptTargetRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Bad,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc _ ≤ ∑' position : ℕ, law {world | FreshReceiptTargetRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
       _ = ∑' position : ℕ, ∫⁻ world, FreshReceiptTargetRisk.risk OracleProgramMachine.step (runPrefix position program world).run ∂law := by
         congr 1
         funext position
         exact FreshReceiptTargetRisk.averaged_event OracleProgramMachine.step (OracleProgram.prefix_replay position program)
       _ = _ := (lintegral_tsum (fun position =>
         (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) (FreshReceiptTargetRisk.risk OracleProgramMachine.step)).aemeasurable)).symm

/-- One inherited bad event is charged once for the entire program. -/
theorem inherited_le {A : Type} (program : Program A) (inherited : Set World) :
    law (inherited ∪ {world | Bad program world}) ≤ law inherited + ∫⁻ world, totalCharge program world ∂law :=
  (measure_union_le _ _).trans (add_le_add le_rfl (bad_le program))

theorem named {A : Type} (sample : LookupFactorFixation.Sample) (program : Program A)
    (outer : ProgramFirstStreamRead.First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input)
    (receipt : NativeTranscript.Observation.output (NativeReceiptPrefixView.key sample.state.phase.consumed) 0
      (InputIndexedOracle.bytes sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64) ∈
        (OracleProgram.run program sample.view.reader.world).run.2)
    (safe : ¬ Bad program sample.view.reader.world) :
    sample.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix outer.position program sample.view.reader.world).run.2 := by
  rcases ReceiptFirstReadCoverage.named_or_event sample program outer receipt with known | ⟨first,_,hit⟩
  · exact known
  · exact False.elim (safe ⟨first.position,hit⟩)

/-- Transport only the reader's world and input, retaining the original
first-read witness and its exact position. -/
theorem named_at {A : Type} (sample : LookupFactorFixation.Sample) (program : Program A)
    {world : World} {input : InputIndexedOracle.Input}
    (outer : ProgramFirstStreamRead.First program world input)
    (sameWorld : sample.view.reader.world = world)
    (sameInput : sample.view.reader.entry.coefficients.phase.pending.input = input)
    (receipt : NativeTranscript.Observation.output (NativeReceiptPrefixView.key sample.state.phase.consumed) 0
      (InputIndexedOracle.bytes world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64) ∈
        (OracleProgram.run program world).run.2)
    (safe : ¬ Bad program world) :
    sample.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix outer.position program world).run.2 := by
  subst world
  subst input
  exact named sample program outer receipt safe

/-- All logged samples and outer reads share one event, including samples
chosen after the execution. This definition imposes no fixed job count. -/
def Unnamed {A : Type} (program : Program A) (world : World) : Prop :=
  ∃ sample : LookupFactorFixation.Sample, sample.view.reader.world = world ∧
    ∃ outer : ProgramFirstStreamRead.First program world sample.view.reader.entry.coefficients.phase.pending.input,
      NativeTranscript.Observation.output (NativeReceiptPrefixView.key sample.state.phase.consumed) 0
        (InputIndexedOracle.bytes world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64) ∈
          (OracleProgram.run program world).run.2 ∧
      sample.state.phase.consumed ∉ ReceiptPayloadView.payloads (runPrefix outer.position program world).run.2

theorem unnamed_subset {A : Type} (program : Program A) :
    {world | Unnamed program world} ⊆ {world | Bad program world} := by
  rintro world ⟨sample,rfl,outer,receipt,unnamed⟩
  by_contra safe
  exact unnamed (named sample program outer receipt safe)

/-- One lifetime bound covers every unnamed logged sample, without a
per-job, per-factor or collector-retry union multiplier. -/
theorem unnamed_le {A : Type} (program : Program A) :
    law {world | Unnamed program world} ≤ ∫⁻ world, totalCharge program world ∂law :=
  (measure_mono (unnamed_subset program)).trans (bad_le program)

end
end FormalProof4FHE.HasteBoots.ProgramReceiptCoverage
