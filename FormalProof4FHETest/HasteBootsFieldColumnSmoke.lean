module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFieldColumnBound
import all FormalProof4FHETest.HasteBootsEarlyReceiptSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsFieldColumnSmoke
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (world work)
open HasteBootsBatchMeaningSmoke (root)
open HasteBootsEarlyReceiptSmoke (view step columnInput receiptKey)
open NativeGoldBatchFieldColumnLaw (collected event extended)

theorem parsed : NativeGoldBatchChallengeLink.parse columnInput = some view := by
  obtain ⟨input,first,parsed⟩ := NativeEarlyReceiptPrefixRisk.selected_link step
    (HasteBootsEarlyReceiptSmoke.past world).run view HasteBootsEarlyReceiptSmoke.selected
  have actual : CausalStreamExposure.firstRead step (HasteBootsEarlyReceiptSmoke.past world).run = some columnInput := by decide +kernel
  have equal : input = columnInput := Option.some.inj (first.symm.trans actual)
  simpa only [equal] using parsed
theorem power : view.column.index.domain.val = 2^5 := by decide +kernel

theorem valid : NativeIndexRequest.check view.column.index.domain view.column.index.count = true :=
  (NativeGoldBatchColumnInputView.parse_sound columnInput view.column
    (NativeGoldBatchChallengeLink.parse_sound columnInput view parsed root).1 root).2.1

-- Field and receipt bytes are already partially cached. No complete receipt
-- or unexposed field stream is required by the column composition.
def past (oracle : World) : NativeTranscript.Execution (Unit ⊕ Unit) := do
  let _ ← ObservationReplay.read oracle (view.field.phase root).pending.input 0 1
  let _ ← ObservationReplay.read oracle receiptKey 63 1
  pure (.inl ())
theorem replay : ObservationReplay.Replayable past :=
  ObservationReplay.bind_replay (ObservationReplay.read_replay _ 0 1) (fun _ =>
    ObservationReplay.bind_replay (ObservationReplay.read_replay receiptKey 63 1) (fun _ =>
      ObservationReplay.pure_replay ((.inl ()) : Unit ⊕ Unit)))
theorem first : CausalStreamExposure.firstRead step (past world).run = some columnInput := by decide +kernel
example : CausalStreamExposure.seen (past world).run.2 (view.field.phase root).pending.input = true := by decide +kernel
example : ¬ NativeFieldReceipt.Known (past world).run.2 work.state.phase := by
  intro known
  have missing : (.inl (NativeFieldReceipt.input work.state.phase,0) : InputIndexedOracle.Coordinate) ∉
      ObservationReplay.footprint (past world).run.2 := by decide +kernel
  exact missing (known ⟨0,by decide⟩)
example : (view.field.phase root).pending.input.length < columnInput.length :=
  NativeGoldBatchChallengeScope.field_shorter columnInput view parsed root
example (fuel : ℕ) : CausalStreamExposure.seen (extended past root fuel view world).run.2 columnInput = false :=
  NativeGoldBatchFieldColumnLaw.unseen_extended past root fuel view columnInput parsed step world first
example (oracle : World) : (extended past root 18 view oracle).run.1.1 = (past oracle).run := by
  rw [NativeGoldBatchFieldColumnLaw.run_extended]
example : (collected root 17 view world).1.remaining = 1 := by decide +kernel
example : (collected root 18 view world).1.remaining = 0 := by decide +kernel
example : (collected root 18 view world).1.values.length = 18 := by decide +kernel
example : ((NativeIndexFirstReadLaw.values 5 (view.column.index.request root).transcript view.column.index.label
    view.column.index.domain view.column.index.count world).map (fun draw => (List.ofFn draw).map Fin.val)) = some [7,1,7] := by decide +kernel

def flag (state : NativeFieldVector.State) : Bool := decide ((state.values[0]?).getD 0 % 2 = 0)
def raw (state : NativeFieldVector.State) (_ : Fin 2) (_ : Fin (2^5)) : Bool := flag state
def claimed (state : NativeFieldVector.State) (test : Fin 2) (column : Fin (2^5)) : Bool :=
  if test.val = 0 ∧ column.val = 0 then !(flag state) else flag state

theorem one_distance (state : NativeFieldVector.State) : hammingDist (raw state 0) (claimed state 0) = 1 := by
  have count (value : Bool) : hammingDist (fun _ : Fin (2^5) => value)
      (fun column : Fin (2^5) => if (0 : ℕ) = 0 ∧ column.val = 0 then !value else value) = 1 := by
    cases value <;> decide +kernel
  exact count (flag state)
-- The functions really depend on the collected field value.
example : raw ⟨work.state.phase,0,[0],[]⟩ 0 0 ≠ raw ⟨work.state.phase,0,[1],[]⟩ 0 0 := by decide +kernel
-- Repeated ordered draws all miss column zero; both response checks pass.
example : event root 18 view 5 (NativeGoldBatchFieldColumnBound.agrees 5 view.column.index.count.val raw claimed) world := by
  unfold event
  rw [NativeIndexFirstReadLaw.values_run 5 _ _ _ _ valid power]
  simp only [Option.elim_some]
  unfold NativeGoldBatchFieldColumnBound.agrees ColumnOpening.Agrees
  decide +kernel
example : ¬ event root 17 view 5 (NativeGoldBatchFieldColumnBound.agrees 5 view.column.index.count.val raw claimed) world := by
  unfold event
  rw [NativeIndexFirstReadLaw.values_run 5 _ _ _ _ valid power]
  simp only [Option.elim_some]
  unfold NativeGoldBatchFieldColumnBound.agrees ColumnOpening.Agrees
  decide +kernel
example : ColumnOpening.missBound (Fin (2^5)) view.column.index.count.val 1 = ((31 : ENNReal)/32)^3 := by
  have quota : view.column.index.count.val = 3 := by decide +kernel
  rw [ColumnOpening.missBound,Fintype.card_fin,quota]
  rfl

-- Two state-dependent checks use one shared quota of three draws.
example : (law[|{oracle | (past oracle).run = (past world).run}])
    {oracle | ∃ fuel, event root fuel view 5 (NativeGoldBatchFieldColumnBound.agrees 5 view.column.index.count.val raw claimed) oracle} ≤
      ColumnOpening.missBound (Fin (2^5)) view.column.index.count.val 1 := by
  apply NativeGoldBatchFieldColumnBound.eventual_bound replay root view columnInput parsed step world first 5 power raw claimed 1
  intro fuel current _ _
  exact ⟨0,by rw [one_distance]⟩

-- Arbitrary field-result predicates have the exact retained-posterior law.
example (fuel : ℕ) (bad : NativeFieldVector.State → (Fin view.column.index.count.val → Fin (2^5)) → Prop) :
    (law[|{oracle | (past oracle).run = (past world).run}]) {oracle | event root fuel view 5 bad oracle} =
      ∫⁻ current, Pr{let draw ← $ᵗ (Fin view.column.index.count.val → Fin (2^5))}[bad (collected root fuel view current).1 draw]
        ∂law[|{oracle | (past oracle).run = (past world).run}] :=
  NativeGoldBatchFieldColumnLaw.conditional_uniform replay root fuel view columnInput parsed step world first 5 power bad
end
end HasteBootsFieldColumnSmoke
