module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
import all FormalProof4FHETest.HasteBootsBatchOrderedSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law bytes)
open OracleComp OracleSpec MeasureTheory ProbabilityTheory
namespace HasteBootsNativeColumnLawSmoke
noncomputable section
open scoped Classical
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx world work prepared draw typed ordered constructed)
open HasteBootsBatchMeaningSmoke (usize root)

example : NativeGoldBatchColumnRequestLaw.values ctx work world = some draw := by
  rw [NativeGoldBatchColumnRequestLaw.values_original ctx world work prepared,typed]
example : work.sample.draws = [7,1,7] ∧ work.sample.indices = [1,7] ∧ work.jobs.length = 2 := by decide +kernel
example : (NativeGoldBatchColumnRequestLaw.input ctx work world).length ≠ 0 := by decide +kernel

-- This history learns the same receipt through two partial/cloned reads.
def receiptInput := NativeFieldReceipt.input work.state.phase
def past (oracle : World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← ObservationReplay.read oracle receiptInput 0 32
  let _ ← ObservationReplay.read oracle receiptInput 32 32
  pure (.inl ())
theorem replay : ObservationReplay.Replayable past :=
  ObservationReplay.bind_replay (ObservationReplay.read_replay receiptInput 0 32) (fun _ =>
    ObservationReplay.bind_replay (ObservationReplay.read_replay receiptInput 32 32) (fun _ =>
      ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit)))
theorem known : NativeFieldReceipt.Known (past world).run.2 work.state.phase := by
  apply NativeFieldReceipt.known_of_split (past world).run.2 work.state.phase 32 (by decide)
    (bytes world receiptInput 0 32) (bytes world receiptInput 32 32)
  · exact InputIndexedOracle.bytes_length _ _ _ _
  · exact InputIndexedOracle.bytes_length _ _ _ _
  · change NativeTranscript.Observation.output receiptInput 0 (bytes world receiptInput 0 32) ∈
      [NativeTranscript.Observation.output receiptInput 0 (bytes world receiptInput 0 32),NativeTranscript.Observation.output receiptInput 32 (bytes world receiptInput 32 32)]
    simp
  · change NativeTranscript.Observation.output receiptInput 32 (bytes world receiptInput 32 32) ∈
      [NativeTranscript.Observation.output receiptInput 0 (bytes world receiptInput 0 32),NativeTranscript.Observation.output receiptInput 32 (bytes world receiptInput 32 32)]
    simp
example : ¬ (NativeTranscript.finishField world work.state.phase).run.2.Sublist (past world).run.2 := by decide +kernel

-- A partial receipt alone is not treated as a fully known parent.
example : ¬ NativeFieldReceipt.Known [NativeTranscript.Observation.output receiptInput 0 (bytes world receiptInput 0 32)] work.state.phase := by
  intro complete
  have member := complete ⟨63,by decide⟩
  obtain ⟨entry,inLog,coordinate⟩ := Finset.mem_biUnion.mp member
  have same := List.mem_toFinset.mp inLog
  simp only [List.mem_singleton] at same
  subst entry
  have bound := (NativeShakeProjection.output_coordinate _ _ _ _).mp coordinate
  rw [InputIndexedOracle.bytes_length] at bound
  have impossible : (63 : ℕ) < 32 := bound.2.2
  omega

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read (NativeGoldBatchColumnRequestLaw.input ctx work world) 999 1 (fun _ => ())
theorem selected : CausalStreamExposure.firstRead step (past world).run = some (NativeGoldBatchColumnRequestLaw.input ctx work world) := by decide +kernel
example (other : World) (fiber : (past other).run = (past world).run) :
    NativeGoldBatchColumnRequestLaw.parent work other = NativeGoldBatchColumnRequestLaw.parent work world :=
  NativeGoldBatchColumnRequestLaw.parent_on_fiber_of_known replay world other work known fiber

example (event : (Fin ctx.parameters.queries.val → Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code))) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (NativeGoldBatchColumnRequestLaw.values ctx work other).elim False event} =
        Pr{let draws ← $ᵗ (Fin ctx.parameters.queries.val → Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)))}[event draws] :=
  NativeGoldBatchColumnRequestLaw.conditional_uniform ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2)
    constructed step replay known selected event

abbrev Position := Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code))
def raw (_ : Fin 6) (_ : Position) : ℕ := 0
def claimed (test : Fin 6) (position : Position) : ℕ := if test.val = 5 ∧ position.val < 2 then 1 else 0
theorem distance : 2 ≤ hammingDist (raw 5) (claimed 5) := by decide +kernel
example : ¬ (∀ test : Fin 6, ColumnOpening.Agrees (raw test) (claimed test) draw) := by
  intro agree
  have bad := agree 5 ⟨1,by decide⟩
  change (0 : ℕ) = 1 at bad
  contradiction
example : (law[|{other | (past other).run = (past world).run}])
    {other | (NativeGoldBatchColumnRequestLaw.values ctx work other).elim False
      (fun draws => ∀ test : Fin 6, ColumnOpening.Agrees (raw test) (claimed test) draws)} ≤
      ColumnOpening.missBound Position ctx.parameters.queries.val 2 :=
  NativeGoldBatchColumnRequestLaw.shared_bound ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2)
    constructed step replay known selected raw claimed 2 ⟨5,distance⟩

section TwoGroups
open HasteBootsBatchMeaningSmoke (zeros identity matrix prepared? prepared_get)
def third : NativeGoldPcsWire.Query := ⟨[(identity,identity),(identity,identity)],by decide⟩
def ctx : NativeGoldBatchPcsProgram.Context := {HasteBootsBatchOrderedSmoke.ctx with
  queries := ⟨[HasteBootsBatchMeaningSmoke.query,HasteBootsBatchMeaningSmoke.secondQuery,third],by decide⟩
  values := ⟨[zeros 3 (by decide),zeros 3 (by decide),zeros 3 (by decide)],by decide⟩
  opening := {HasteBootsBatchOrderedSmoke.ctx.opening with evaluations := ⟨[zeros 6 (by decide),zeros 6 (by decide)],by decide⟩}}
def result := (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1
theorem present : (prepared? result).isSome = true := by decide +kernel
def work := (prepared? result).get present
theorem prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work := prepared_get result present
example : work.groups.length = 2 ∧ work.binding.queries.val.length = 3 := by decide +kernel

def lazyRow : NativeLookupRequestWire.Row := ⟨[usize NativeFields.goldilocksModulus,0,0,0,0,0],by decide⟩
def changed : NativeGoldBatchOpening.Opening := {ctx.opening with evaluations := ⟨[zeros 6 (by decide),lazyRow],by decide⟩}
example : lazyRow.val.map NativeFieldRepresentation.goldValue = (zeros 6 (by decide)).val.map NativeFieldRepresentation.goldValue := by decide +kernel
example : NativeGoldBatchPcsProgram.finish ctx.parameters work.binding changed = .ok () := by decide +kernel
-- All raw response bytes are committed even for field-equal lazy aliases.
example : NativeGoldBatchResponseBinding.input (NativeGoldBatchColumnRequestLaw.parent work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries changed ≠
    NativeGoldBatchColumnRequestLaw.input ctx work world := by
  intro same
  have values := (NativeGoldBatchColumnRequestLaw.response_bound ctx work world changed).mp same
  have different : changed.evaluations ≠ ctx.opening.evaluations := by decide +kernel
  exact different values.2
-- Authentication rows/paths are later data and do not change the nonce.
example : NativeGoldBatchResponseBinding.input (NativeGoldBatchColumnRequestLaw.parent work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries
    {ctx.opening with columns := ⟨[],by decide⟩} = NativeGoldBatchColumnRequestLaw.input ctx work world := rfl
end TwoGroups
end
end HasteBootsNativeColumnLawSmoke
