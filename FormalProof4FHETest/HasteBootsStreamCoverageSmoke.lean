module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchStreamCoverage
import all FormalProof4FHE.HasteBoots.NativeIndexExposureRisk
import all FormalProof4FHETest.HasteBootsBatchOrderedSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law bytes)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsStreamCoverageSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx work world prepared)
open HasteBootsBatchMeaningSmoke (usize)

-- Starts, empty reads and SHA-512 calls precede the first far-offset SHAKE read.
def target : Input := [12]
def other : Input := [13]
def step : ℕ → OracleMachine.Command ℕ Unit
  | 0 => .start target 1
  | 1 => .read target 0 0 (fun _ => 2)
  | 2 => .hash target (fun _ => 3)
  | 3 => .read target 999 1 (fun _ => 4)
  | 4 => .read other 0 2 (fun _ => 5)
  | 5 => .read target 0 2 (fun _ => 6)
  | _ => .done ()
def packet (fuel : ℕ) := (run (OracleMachine.take step fuel 0) world).run
example : CausalStreamCoverage.locate target (packet 6).2 = some 3 := by decide +kernel
example : CausalStreamExposure.firstRead step (packet 3) = some target := by decide +kernel
example : CausalStreamExposure.firstRead step (packet 4) = some other := by decide +kernel
example : CausalStreamExposure.firstRead step (packet 5) = none := by decide +kernel
example : OracleFirstExposure.locate (packet 4).2 (OracleFirstExposure.seedCoordinates target) = none := by decide +kernel
example : FreshShakeTail.Fresh (NativeShakeKernel.observed (packet 3).2 world) target 0 :=
  CausalStreamExposure.firstRead_fresh step (packet 3) target (by decide +kernel) world 0
example : CausalStreamExposure.firstRead step ((packet 3).1,
    [NativeTranscript.Observation.output target 500 (bytes world target 500 1)] ++ (packet 3).2) = none := by decide +kernel
example : CausalStreamExposure.firstRead step ((packet 3).1,
    [NativeTranscript.Observation.output other 500 (bytes world other 500 1)] ++ (packet 3).2) = some target := by decide +kernel

-- The actual native preparation supplies the column read and checked positive quota.
example : 0 < ctx.parameters.queries.val := NativeGoldBatchStreamCoverage.prepared_positive_quota ctx world work prepared
example : NativeTranscript.Observation.output (NativeGoldBatchColumnRequestLaw.input ctx work world) 0
    (bytes world (NativeGoldBatchColumnRequestLaw.input ctx work world) 0 24) ∈
      (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 :=
  NativeGoldBatchStreamCoverage.prepared_column_read ctx world work prepared

def prelude (oracle : World) : NativeTranscript.Execution Unit := do
  let _ ← ObservationReplay.read oracle (NativeGoldBatchColumnRequestLaw.input ctx work world) 999 1
  pure ()
example : CausalStreamExposure.seen (prelude world).run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = true := by decide +kernel
example : CausalStreamExposure.seen (prelude world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = false := by decide +kernel
-- No supplied machine-log embedding and no fixed candidate budget is needed.
example : ∃ fuel,
    (CausalStreamExposure.seen (prelude world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true ∨
      ∃ index < fuel, CausalStreamExposure.firstRead OracleProgramMachine.step
        (CausalExposureLifetime.history prelude (fun _ => NativeGoldBatchPcsProgram.prepareProgram ctx) OracleProgramMachine.step index world).run =
          some (NativeGoldBatchRandomLaw.phase work).pending.input) ∧
    (CausalStreamExposure.seen (prelude world).run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = true ∨
      ∃ index < fuel, CausalStreamExposure.firstRead OracleProgramMachine.step
        (CausalExposureLifetime.history prelude (fun _ => NativeGoldBatchPcsProgram.prepareProgram ctx) OracleProgramMachine.step index world).run =
          some (NativeGoldBatchColumnRequestLaw.input ctx work world)) :=
  NativeGoldBatchStreamCoverage.native_after_coverage prelude (fun _ => ctx) world work prepared

def request : NativePrequeryIndexLaw.Request := ⟨NativeGoldBatchColumnRequestLaw.transcript ctx work world,
  NativeGoldBatchColumns.label,ctx.parameters.code.blocks,ctx.parameters.queries⟩
def next (_ : Unit) : OracleMachine.Command Unit Unit := .read (NativeGoldBatchColumnRequestLaw.input ctx work world) 999 1 (fun _ => ())
def select (_ : NativeIndexExposureRisk.Packet Unit Unit) := some request
def bad (_ : NativeIndexExposureRisk.Packet Unit Unit) (result : NativeIndexExposureRisk.Result) : Prop :=
  ∃ sample, result.1 = some sample ∧ sample.draws = [7,1,7]
def emptyPast (_ : World) : NativeTranscript.Execution (Unit ⊕ Unit) := pure (.inl ())
example : NativeIndexExposureRisk.event next select bad (emptyPast world).run world := by
  change NativeIndexExposureRisk.eligible next (emptyPast world).run request ∧ _
  constructor
  · unfold NativeIndexExposureRisk.eligible
    decide +kernel
  · refine ⟨work.sample,?_,by decide +kernel⟩
    exact NativeGoldBatchColumnRequestLaw.prepared_request ctx world work prepared
example : NativeIndexExposureRisk.eligible next (emptyPast world).run request := by
  unfold NativeIndexExposureRisk.eligible
  decide +kernel
example : (law[|{oracle | (emptyPast oracle).run = (emptyPast world).run}])
    {oracle | NativeIndexExposureRisk.event next select bad (emptyPast oracle).run oracle} =
      NativeIndexExposureRisk.risk next select bad (emptyPast world).run :=
  NativeIndexExposureRisk.conditional_event next select bad (ObservationReplay.pure_replay _) world

def repeated (oracle : World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← prelude oracle
  pure (.inl ())
example : ¬ NativeIndexExposureRisk.event next select bad (repeated world).run world := by
  have excluded : ¬ NativeIndexExposureRisk.eligible next (repeated world).run request := by
    unfold NativeIndexExposureRisk.eligible
    decide +kernel
  exact fun yes => excluded yes.1
example : NativeIndexExposureRisk.risk next select bad (repeated world).run = 0 := by
  have excluded : ¬ NativeIndexExposureRisk.eligible next (repeated world).run request := by
    unfold NativeIndexExposureRisk.eligible
    decide +kernel
  simp only [NativeIndexExposureRisk.risk,select,excluded,ite_false]

-- The quota really depends on private causal state; only its matching input is eligible.
def adaptiveRequest (state : ℕ) : NativePrequeryIndexLaw.Request := {request with count := if state = 0 then usize 3 else usize 1}
def adaptiveStep (state : ℕ) : OracleMachine.Command ℕ Unit :=
  .read (NativePrequeryIndexLaw.requestInput (adaptiveRequest state).transcript (adaptiveRequest state).label
    (adaptiveRequest state).domain (adaptiveRequest state).count) 99 1 (fun _ => state+1)
def adaptiveSelect (packet : NativeIndexExposureRisk.Packet ℕ Unit) :=
  match packet.1 with | .inl state => some (adaptiveRequest state) | .inr _ => none
example : (adaptiveRequest 0).count.val = 3 ∧ (adaptiveRequest 1).count.val = 1 := by decide +kernel
example : NativeIndexExposureRisk.eligible adaptiveStep (.inl 0,[]) (adaptiveRequest 0) ∧
    NativeIndexExposureRisk.eligible adaptiveStep (.inl 1,[]) (adaptiveRequest 1) := by
  unfold NativeIndexExposureRisk.eligible
  decide +kernel
example (past : World → NativeTranscript.Execution ℕ) (replay : ObservationReplay.Replayable past) :
    law {oracle | ∃ fuel, NativeIndexExposureRisk.event adaptiveStep adaptiveSelect (fun _ _ => True)
      (CausalExposureLifetime.history past id adaptiveStep fuel oracle).run oracle} ≤
      ∫⁻ oracle, NativeIndexExposureRisk.totalCharge past id adaptiveStep adaptiveSelect (fun _ _ => True) oracle ∂law := by
  simpa only [Set.empty_union,measure_empty,zero_add] using
    NativeIndexExposureRisk.lifetime_le replay id adaptiveStep adaptiveSelect (fun _ _ => True) ∅
-- Native checked byte-count overflow rejects before any draw is charged.
def overflow : NativePrequeryIndexLaw.Request := {request with count := usize (2^61)}
example : NativeIndexExposureRisk.risk next (fun _ => some overflow) bad (emptyPast world).run = 0 := by
  have invalid : ¬ NativeIndexExposureRisk.eligible next (emptyPast world).run overflow := by
    unfold NativeIndexExposureRisk.eligible
    decide +kernel
  simp only [NativeIndexExposureRisk.risk,invalid,ite_false]

abbrev Position := Fin (2^5)
def raw (_ : Fin 6) (_ : Position) : ℕ := 0
def claimed (test : Fin 6) (position : Position) : ℕ := if test.val = 5 ∧ position.val = 0 then 1 else 0
example : NativeIndexExposureRisk.risk next select
    (fun _ result => (result.1.bind (fun sample => NativeGoldPcsDraws.typed 5 request.count.val sample.draws)).elim False
      (fun draw => ∀ test : Fin 6, ColumnOpening.Agrees (raw test) (claimed test) draw)) (emptyPast world).run ≤
      ColumnOpening.missBound Position 3 1 := by
  apply NativeIndexExposureRisk.shared_risk_bound next select (emptyPast world).run request rfl
    (by unfold NativeIndexExposureRisk.eligible; decide +kernel) 5 (by decide +kernel) raw claimed 1
  exact ⟨5,by decide +kernel⟩

end
end HasteBootsStreamCoverageSmoke
