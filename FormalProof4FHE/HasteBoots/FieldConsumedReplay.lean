module
public import FormalProof4FHE.HasteBoots.NativeFieldConsumedPrefix
@[expose] public section

/-! A native collector's accepted coefficients are determined by its complete
consumed byte string, including rejected candidates. Receipt keys expose that
string directly; receipt length encoding and fresh-digest risks are separate. -/
namespace FormalProof4FHE.HasteBoots.FieldConsumedReplay
open InputIndexedOracle (Input World)
open NativeTranscript (FieldPhase)
open NativeFieldVector (State)
noncomputable section

def values (p : ℕ) (chunks : List Input) : List ℕ :=
  chunks.filterMap (fun raw => if CanonicalTranscriptSampler.candidate p raw < p then some (CanonicalTranscriptSampler.candidate p raw) else none)

structure Traced (p : ℕ) (state : State) : Prop where
  widths : ∀ chunk ∈ state.chunks, chunk.length = CanonicalByteSampler.byteCount p
  consumed : state.phase.consumed = state.chunks.flatten
  accepted : state.values = values p state.chunks

theorem initial (p count : ℕ) (phase : FieldPhase) (empty : phase.consumed = []) :
    Traced p (NativeFieldVector.initial phase count) := ⟨by simp [NativeFieldVector.initial],empty,rfl⟩

theorem advance (p : ℕ) (state : State) (world : World) (traced : Traced p state) :
    Traced p (NativeFieldVector.advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1) := by
  let raw := InputIndexedOracle.bytes world state.phase.pending.input state.phase.consumed.length (CanonicalByteSampler.byteCount p)
  have length : raw.length = CanonicalByteSampler.byteCount p := InputIndexedOracle.bytes_length _ _ _ _
  by_cases good : CanonicalTranscriptSampler.candidate p (InputIndexedOracle.bytes world state.phase.pending.input state.phase.consumed.length (CanonicalByteSampler.byteCount p)) < p
  · simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk,good,ite_true,
      CanonicalTranscriptSampler.completed,NativeFieldVector.advance]
    constructor
    · intro chunk present
      rcases List.mem_append.mp present with old | added
      · exact traced.widths chunk old
      · obtain rfl := List.mem_singleton.mp added
        exact length
    · simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil] using congrArg (fun earlier => earlier ++ raw) traced.consumed
    · simpa only [values,raw,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,good,ite_true] using congrArg (fun earlier => earlier ++ [CanonicalTranscriptSampler.candidate p raw]) traced.accepted
  · simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk,good,ite_false,
      CanonicalTranscriptSampler.paused,CanonicalTranscriptSampler.prepend,NativeFieldVector.advance]
    constructor
    · intro chunk present
      rcases List.mem_append.mp present with old | added
      · exact traced.widths chunk old
      · obtain rfl := List.mem_singleton.mp added
        exact length
    · simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil] using congrArg (fun earlier => earlier ++ raw) traced.consumed
    · simpa only [values,raw,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,good,ite_false,List.append_nil] using traced.accepted

theorem execute (p fuel : ℕ) (state : State) (world : World) (traced : Traced p state) :
    Traced p (NativeFieldVector.execute p fuel state world).1 := by
  induction fuel generalizing state with
  | zero => exact traced
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simpa only [NativeFieldVector.execute,complete,ite_true] using traced
    · simpa only [NativeFieldVector.execute,complete,ite_false] using ih _ (advance p state world traced)

theorem drive (p fuel : ℕ) (state : State) (world : World) (traced : Traced p state) :
    Traced p (NativeFieldVector.stateOf (NativeFieldVector.driveExecute p fuel state world).1) := by
  change Traced p (NativeFieldVector.stateOf (NativeFieldVector.finishExecute world (NativeFieldVector.execute p fuel state world).1).1)
  rw [NativeFieldVector.finish_state]
  exact execute p fuel state world traced

theorem begin_scalar (p degree w : ℕ) (parent : NativeTranscript.Transcript) (label : Input) :
    Traced p (TypedFieldRequest.beginExecute p degree w parent label).1 := initial p degree _ rfl

theorem begin_vector (p degree w count : ℕ) (parent : NativeTranscript.Transcript) (label : Input) :
    Traced p (TypedFieldVector.beginExecute p degree w count parent label).1 := initial p (count*degree) _ rfl

/-- Equal flattened bytes uniquely identify fixed positive-width chunks.
No modulus, framing, canonical-value or receipt-length premise is needed. -/
theorem chunks_unique (width : ℕ) (positive : 0 < width) (left right : List Input)
    (leftWidths : ∀ chunk ∈ left, chunk.length = width) (rightWidths : ∀ chunk ∈ right, chunk.length = width)
    (same : left.flatten = right.flatten) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons chunk tail =>
      have empty : chunk = [] := (List.append_eq_nil_iff.mp same.symm).1
      have length := rightWidths chunk List.mem_cons_self
      rw [empty,List.length_nil] at length
      omega
  | cons chunk tail ih =>
    cases right with
    | nil =>
      have empty : chunk = [] := (List.append_eq_nil_iff.mp same).1
      have length := leftWidths chunk List.mem_cons_self
      rw [empty,List.length_nil] at length
      omega
    | cons other rest =>
      have leftLength := leftWidths chunk List.mem_cons_self
      have rightLength := rightWidths other List.mem_cons_self
      have equal : chunk = other := by
        have heads := congrArg (List.take width) same
        have leftHead : (chunk ++ tail.flatten).take width = chunk := by rw [← leftLength,List.take_left]
        have rightHead : (other ++ rest.flatten).take width = other := by rw [← rightLength,List.take_left]
        exact leftHead.symm.trans (heads.trans rightHead)
      subst other
      have tails : tail.flatten = rest.flatten := List.append_cancel_left same
      rw [ih rest (fun chunk present => leftWidths chunk (List.mem_cons_of_mem _ present))
        (fun chunk present => rightWidths chunk (List.mem_cons_of_mem _ present)) tails]

/-- Accepted coefficients are fixed by the raw receipt-key payload, even
when the records came from different worlds, inputs or analysis budgets. -/
theorem values_congr (p : ℕ) (positive : 0 < CanonicalByteSampler.byteCount p) (left right : State)
    (leftTrace : Traced p left) (rightTrace : Traced p right) (same : left.phase.consumed = right.phase.consumed) :
    left.values = right.values := by
  have chunks := chunks_unique _ positive left.chunks right.chunks leftTrace.widths rightTrace.widths
    (leftTrace.consumed.symm.trans (same.trans rightTrace.consumed))
  rw [leftTrace.accepted,rightTrace.accepted,chunks]

theorem receipt_key_values (p : ℕ) (positive : 0 < CanonicalByteSampler.byteCount p) (left right : State)
    (leftTrace : Traced p left) (rightTrace : Traced p right)
    (same : NativeFieldReceipt.input left.phase = NativeFieldReceipt.input right.phase) : left.values = right.values :=
  values_congr p positive left right leftTrace rightTrace (List.append_cancel_left same)

end
end FormalProof4FHE.HasteBoots.FieldConsumedReplay
