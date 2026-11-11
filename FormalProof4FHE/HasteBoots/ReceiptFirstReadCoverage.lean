module
public import FormalProof4FHE.HasteBoots.LookupSampleReceiptTargets
public import FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
@[expose] public section

/-! An actual later receipt output selects a real first receipt read. If its
payload was unnamed at the earlier outer scalar first read, chronological
ordering and the fresh target-hit event follow from the actual program log. -/
namespace FormalProof4FHE.HasteBoots.ReceiptFirstReadCoverage
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ProgramFirstStreamRead (First)
open LookupFactorFixation (Sample)
noncomputable section

theorem before_of_unseen {A : Type} {program : Program A} {world : World} {input receipt : Input}
    (outer : First program world input) (later : First program world receipt) (apart : input ≠ receipt)
    (unseen : CausalStreamExposure.seen (runPrefix outer.position program world).run.2 receipt = false) :
    outer.position < later.position := by
  rcases Nat.lt_trichotomy outer.position later.position with earlier | same | backwards
  · exact earlier
  · have atOuter := outer.outputAt
    rw [same] at atOuter
    have equal := Option.some.inj (atOuter.symm.trans later.outputAt)
    exact False.elim (apart (Observation.output.inj equal).1)
  · have prior : ((run program world).run.2.take outer.position)[later.position]? =
        some (Observation.output receipt later.offset (InputIndexedOracle.bytes world receipt later.offset later.count)) := by
      rw [List.getElem?_take_of_lt backwards]
      exact later.outputAt
    have seen : CausalStreamExposure.seen ((run program world).run.2.take outer.position) receipt = true := by
      apply List.any_eq_true.mpr
      refine ⟨_,List.mem_of_getElem? prior,?_⟩
      simp only [CausalStreamExposure.touches,decide_eq_true_eq,true_and]
      simpa only [InputIndexedOracle.bytes_length] using later.positive
    rw [← outer.history,unseen] at seen
    contradiction

theorem output_before {A : Type} {program : Program A} {world : World} {input receipt : Input}
    (outer : First program world input) (later : First program world receipt) (ordered : outer.position < later.position) :
    Observation.output input outer.offset (InputIndexedOracle.bytes world input outer.offset outer.count) ∈ (runPrefix later.position program world).run.2 := by
  rw [later.history]
  apply List.mem_of_getElem?
  rw [List.getElem?_take_of_lt ordered]
  exact outer.outputAt

theorem sample_input_apart (sample : Sample) :
    sample.view.reader.entry.coefficients.phase.pending.input ≠ NativeReceiptPrefixView.key sample.state.phase.consumed := by
  intro same
  have member := LookupSampleReceiptTargets.in_reader sample
  rw [same] at member
  simp only [ReceiptFrameView.frames,
    show NativeReceiptPrefixView.key sample.state.phase.consumed = NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ sample.state.phase.consumed from rfl,
    NativeTranscript.receipt_decode_rejected,Option.getD_none,List.filter_nil,List.not_mem_nil] at member

/-- The known-payload branch and the fresh-hit branch exhaust a sample with
an actual native receipt output in the enclosing raw log. Starts and empty
reads remain in the prefix; earlier positive receipt prequeries are selected. -/
theorem named_or_event {A : Type} (sample : Sample) (program : Program A)
    (outer : First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input)
    (receipt : Observation.output (NativeReceiptPrefixView.key sample.state.phase.consumed) 0
      (InputIndexedOracle.bytes sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64) ∈
        (run program sample.view.reader.world).run.2) :
    sample.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix outer.position program sample.view.reader.world).run.2 ∨
      ∃ first : First program sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed),
        outer.position < first.position ∧ FreshReceiptTargetRisk.event OracleProgramMachine.step
          (runPrefix first.position program sample.view.reader.world).run sample.view.reader.world := by
  by_cases named : sample.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix outer.position program sample.view.reader.world).run.2
  · exact Or.inl named
  · apply Or.inr
    have unseen : CausalStreamExposure.seen (runPrefix outer.position program sample.view.reader.world).run.2
        (NativeReceiptPrefixView.key sample.state.phase.consumed) = false := by
      cases seen : CausalStreamExposure.seen (runPrefix outer.position program sample.view.reader.world).run.2
          (NativeReceiptPrefixView.key sample.state.phase.consumed) with
      | false => rfl
      | true => exact False.elim (named (ReceiptPayloadView.seen _ _ seen))
    obtain ⟨first⟩ := ProgramFirstStreamRead.of_output program sample.view.reader.world _ 0 _
      (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; contradiction) receipt
    have ordered := before_of_unseen outer first (sample_input_apart sample) unseen
    refine ⟨first,ordered,?_⟩
    apply LookupSampleReceiptTargets.event OracleProgramMachine.step _ sample outer.offset
      (InputIndexedOracle.bytes sample.view.reader.world _ outer.offset outer.count)
      (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; have positive := outer.positive; omega)
      (output_before outer first ordered)
    simp only [FreshReceiptTargetRisk.select,first.selected,Option.bind_some,ReceiptPayloadView.read_key]

end
end FormalProof4FHE.HasteBoots.ReceiptFirstReadCoverage
