module

public import FormalProof4FHE.HasteBoots.NativeShakeReadLaw

@[expose] public section

/-! The observed byte cache is a deterministic function of a truthful native
history. Whole-read posterior laws therefore use the actual appended-history
cache, rather than a caller-supplied cache certificate. This normalizes state
for mixed-program probability composition; it is not that full theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeShakeProjection
open InputIndexedOracle (Byte Input World Coordinate law)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open NativeShakeCache (Key Cache)
open NativeTranscript (Observation)

noncomputable section

/-- Exact whole-byte interval exposed by a native output observation. -/
theorem output_coordinate (input : Input) (offset : ℕ) (values : Input) (key : Key) :
    (.inl key : Coordinate) ∈ ObservationReplay.coordinates (.output input offset values) ↔
      key.1 = input ∧ offset ≤ key.2 ∧ key.2 < offset+values.length := by
  simp only [ObservationReplay.coordinates,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨index,bounded,same⟩
    have first := (Prod.mk.inj (Sum.inl.inj same)).1
    have second := (Prod.mk.inj (Sum.inl.inj same)).2
    exact ⟨first.symm,by omega,by omega⟩
  · rintro ⟨first,lower,upper⟩
    refine ⟨key.2-offset,by omega, ?_⟩
    apply congrArg Sum.inl
    exact Prod.ext first.symm (by omega)

/-- A world read splits into its first coordinate and the remaining interval. -/
theorem bytes_cons (world : World) (input : Input) (offset count : ℕ) :
    InputIndexedOracle.bytes world input offset (count+1) =
      world (.inl (input,offset)) :: InputIndexedOracle.bytes world input (offset+1) count := by
  unfold InputIndexedOracle.bytes InputIndexedOracle.block InputIndexedOracle.shake
  rw [List.ofFn_succ]
  congr 1
  congr 1
  funext index
  have positions : offset+index.succ.val = offset+1+index.val := by
    change offset+(index.val+1) = offset+1+index.val
    omega
  rw [positions]

/-- World-backed interval writes change exactly their own complete-input coordinates. -/
theorem write_world_lookup (cache : Cache) (world : World) (input : Input)
    (offset count : ℕ) (key : Key) :
    NativeShakeHistory.writeBytes cache input offset (InputIndexedOracle.bytes world input offset count) key =
      if key.1 = input ∧ offset ≤ key.2 ∧ key.2 < offset+count then
        some (world (.inl key)) else cache key := by
  classical
  induction count generalizing cache offset with
  | zero => simp [NativeShakeHistory.writeBytes,InputIndexedOracle.bytes]
  | succ count ih =>
    rw [bytes_cons,NativeShakeHistory.writeBytes,ih]
    by_cases sameInput : key.1 = input
    · by_cases samePosition : key.2 = offset
      · have sameKey : key = (input,offset) := Prod.ext sameInput samePosition
        subst key
        simp
      · have different : key ≠ (input,offset) := by
          intro same
          exact samePosition (congrArg Prod.snd same)
        rw [Function.update_of_ne different]
        by_cases inside : offset+1 ≤ key.2 ∧ key.2 < offset+1+count
        · have full : offset ≤ key.2 ∧ key.2 < offset+(count+1) := by omega
          simp [sameInput,inside,full]
        · have outside : ¬ (offset ≤ key.2 ∧ key.2 < offset+(count+1)) := by omega
          have outsideTail : ¬ (offset < key.2 ∧ key.2 < offset+1+count) := by omega
          simp [sameInput,outsideTail,outside]
    · have different : key ≠ (input,offset) := by
        intro same
        exact sameInput (congrArg Prod.fst same)
      simp [sameInput,Function.update_of_ne different]

/-- One native read extends the observed cache by exactly the returned interval. -/
theorem observed_append_read (log : List Observation) (world : World) (input : Input)
    (offset count : ℕ) :
    NativeShakeKernel.observed (log++[.output input offset (InputIndexedOracle.bytes world input offset count)]) world =
      NativeShakeHistory.writeBytes (NativeShakeKernel.observed log world) input offset
        (InputIndexedOracle.bytes world input offset count) := by
  classical
  have appendSet : ObservationReplay.footprint
      (log++[.output input offset (InputIndexedOracle.bytes world input offset count)]) =
      ObservationReplay.footprint log ∪ ObservationReplay.coordinates
        (.output input offset (InputIndexedOracle.bytes world input offset count)) := by
    simp [ObservationReplay.footprint,List.toFinset_append,Finset.union_comm]
  funext key
  rw [write_world_lookup]
  simp only [NativeShakeKernel.observed,appendSet,Finset.mem_union,output_coordinate,
    InputIndexedOracle.bytes_length]
  by_cases inside : key.1 = input ∧ offset ≤ key.2 ∧ key.2 < offset+count <;> simp [inside]


/-- Starting a reader reveals no byte. -/
theorem observed_append_start (log : List Observation) (world : World) (input : Input) :
    NativeShakeKernel.observed (log++[.start input]) world = NativeShakeKernel.observed log world := by
  funext key
  simp [NativeShakeKernel.observed,ObservationReplay.footprint,List.toFinset_append,ObservationReplay.coordinates]

/-- SHA-512 observations reveal no SHAKE coordinate. -/
theorem observed_append_hash (log : List Observation) (world : World) (input digest : Input) :
    NativeShakeKernel.observed (log++[.hash input digest]) world = NativeShakeKernel.observed log world := by
  funext key
  simp [NativeShakeKernel.observed,ObservationReplay.footprint,List.toFinset_append,ObservationReplay.coordinates]

/-- A truthful observation has exactly the retained cache-recording effect. -/
theorem record_observed (log : List Observation) (world : World) (entry : Observation)
    (truthful : ObservationReplay.Matches world entry) :
    NativeShakeHistory.record (NativeShakeKernel.observed log world) entry =
      NativeShakeKernel.observed (log++[entry]) world := by
  cases entry with
  | start input => exact (observed_append_start log world input).symm
  | hash input digest => exact (observed_append_hash log world input digest).symm
  | output input offset values =>
    change InputIndexedOracle.bytes world input offset values.length = values at truthful
    have normalized := observed_append_read log world input offset values.length
    rw [truthful] at normalized
    exact normalized.symm

/-- Folding a truthful whole history from empty reconstructs exactly its observed cache. -/
theorem fold_observed (log : List Observation) (world : World) (truthful : ObservationReplay.Agrees world log) :
    log.foldl NativeShakeHistory.record NativeShakeCache.empty = NativeShakeKernel.observed log world := by
  revert truthful
  induction log using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton log entry ih =>
    intro truthful
    have split := (ObservationReplay.agrees_append world log [entry]).mp truthful
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil,ih split.1]
    exact record_observed log world entry (split.2 entry (by simp))


/-- The observed cache is fixed by the whole result/log fiber, without full-reader conditioning. -/
theorem observed_of_fiber {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world other : World)
    (same : (past other).run = (past world).run) :
    NativeShakeKernel.observed (past other).run.2 other =
      NativeShakeKernel.observed (past world).run.2 world := by
  have otherTruth : ObservationReplay.Agrees other (past world).run.2 := by
    rw [← same]
    exact replay.truthful other
  have seenSame := ObservationReplay.same_of_agrees world other (past world).run.2
    (replay.truthful world) otherTruth
  rw [same]
  funext key
  by_cases seen : (.inl key : Coordinate) ∈ ObservationReplay.footprint (past world).run.2
  · simp only [NativeShakeKernel.observed,seen,ite_true,seenSame _ seen]
  · simp only [NativeShakeKernel.observed,seen,ite_false]


/-- Conditional events need only agree on the complete observed history fiber. -/
theorem conditional_event_congr {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (left right : World → Prop)
    (agree : ∀ other, (past other).run = (past world).run → (left other ↔ right other)) :
    (law[|{other | (past other).run = (past world).run}]) {other | left other} =
      (law[|{other | (past other).run = (past world).run}]) {other | right other} := by
  have sameSet : {other | (past other).run = (past world).run} ∩ {other | left other} =
      {other | (past other).run = (past world).run} ∩ {other | right other} := by
    ext other
    constructor
    · rintro ⟨same,yes⟩
      exact ⟨same,(agree other same).mp yes⟩
    · rintro ⟨same,yes⟩
      exact ⟨same,(agree other same).mpr yes⟩
  rw [cond_apply (ObservationReplay.fiber_measurable replay world),
    cond_apply (ObservationReplay.fiber_measurable replay world),sameSet]

/-- The physical read law includes the actual appended-history cache. -/
theorem read_event_observed {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input) (offset count : ℕ)
    (event : Input × Cache → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (InputIndexedOracle.bytes other input offset count,
        NativeShakeKernel.observed ((past other).run.2 ++
          [.output input offset (InputIndexedOracle.bytes other input offset count)]) other)} =
      Pr{let result ← (NativeShakeReadLaw.sample input offset count
        (NativeShakeKernel.observed (past world).run.2 world))}[event result] := by
  calc _ = (law[|{other | (past other).run = (past world).run}])
        {other | event (NativeShakeReadLaw.outcome (NativeShakeKernel.observed (past world).run.2 world)
          input offset (InputIndexedOracle.block other input offset count))} := by
        apply conditional_event_congr replay world
        intro other same
        rw [observed_append_read,observed_of_fiber replay world other same]
        rfl
       _ = _ := NativeShakeReadLaw.read_event replay world input offset count event

end
end FormalProof4FHE.HasteBoots.NativeShakeProjection
