module

public import FormalProof4FHE.HasteBoots.NativeShakeHistory

@[expose] public section

/-! Whole-read sampling for the interpreter-owned SHAKE cache.
A cached byte never consumes a new random answer. Distributional comparison
with an eager finite generator is separate from literal program equality. -/
namespace FormalProof4FHE.HasteBoots.NativeShakeReadLaw

open InputIndexedOracle (Byte Input World law)
open NativeTranscript (Observation)
open NativeShakeCache (Cache Key)
open NativeRootMessage (Digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory

noncomputable section

def sample (input : Input) (offset : ℕ) : ℕ → Cache → ProbComp (Input × Cache)
  | 0,cache => pure ([],cache)
  | count+1,cache => do
    let first ← NativeShakeKernel.step cache (input,offset)
    let rest ← sample input (offset+1) count first.2
    pure (first.1::rest.1,rest.2)

/-- Actual shared execution uses this private sampler and preserves all shared
hash/checkpoint fields, even when a read partially overlaps earlier reads. -/
theorem shared_read {Cfg Payload : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (cache : Cache) (input : Input) (offset count : ℕ) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      ((NativeShakeCache.read (Cfg := Cfg) input offset count).run cache)).run state =
      (fun result => (result,state)) <$> sample input offset count cache := by
  induction count generalizing offset cache state with
  | zero => simp only [NativeShakeCache.read,StateT.run_pure,simulateQ_pure,sample,map_pure]
  | succ count ih =>
    simp only [NativeShakeCache.read,StateT.run_bind,simulateQ_bind,StateT.run_bind,
      NativeShakeKernel.shared_step,simulateQ_pure,StateT.run_pure,sample]
    simp only [map_bind,ih,bind_map_left,map_pure]

/-- Eager deterministic replay, supplied one independent raw byte per position.
Known answers override those raw bytes; this is not a resampling interpreter. -/
def eager (input : Input) (offset : ℕ) : {count : ℕ} → (Fin count → Byte) → Cache → Input × Cache
  | 0,_,cache => ([],cache)
  | count+1,raw,cache =>
    let value := (cache (input,offset)).getD (raw 0)
    let rest := eager input (offset+1) (fun index : Fin count => raw index.succ)
      (NativeShakeKernel.install cache (input,offset) value)
    (value::rest.1,rest.2)

def split (count : ℕ) : (Fin (count+1) → Byte) ≃ Byte × (Fin count → Byte) where
  toFun raw := (raw 0,fun index => raw index.succ)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv raw := by funext index; exact Fin.cases rfl (fun _ => rfl) index
  right_inv pair := by cases pair; rfl


/-- Cached answers are a mask of a uniform raw byte, as an equality of
probability laws rather than an equality of computations or query counts. -/
theorem answer_dist (cache : Cache) (key : Key) :
    NativeShakeKernel.answer cache key =ᵈ
      (fun raw : Byte => (cache key).getD raw) <$> ($ᵗ Byte) := by
  classical
  apply EvalDistEq.of_evalDist_eq
  cases known : cache key with
  | some value =>
    simp only [NativeShakeKernel.answer,known,Option.getD_some,evalDist_pure,
      evalDist_map_of_discrete,SampleableType.evalDist_uniformSample,MeasureTheory.Measure.map_const,
      MeasureTheory.measure_univ,one_smul]
  | none =>
    simp only [NativeShakeKernel.answer,known,Option.getD_none,evalDist_liftM_unifSpec_query]
    change uniformOn (Set.univ : Set Byte) = 𝒟[id <$> ($ᵗ Byte)]
    rw [id_map,SampleableType.evalDist_uniformSample]

/-- The eager mask also preserves the complete owned cache transition. -/
theorem step_dist (cache : Cache) (key : Key) :
    NativeShakeKernel.step cache key =ᵈ
      (fun raw : Byte =>
        let value := (cache key).getD raw
        (value,NativeShakeKernel.install cache key value)) <$> ($ᵗ Byte) := by
  simpa only [NativeShakeKernel.step,Functor.map_map] using
    (answer_dist cache key).map (fun value => (value,NativeShakeKernel.install cache key value))

/-- A finite uniform vector can be supplied in head/tail order. -/
theorem eager_uniform_succ (cache : Cache) (input : Input) (offset count : ℕ) :
    (do
      let head ← $ᵗ Byte
      let tail ← $ᵗ (Fin count → Byte)
      pure (eager input offset (Fin.cons head tail) cache)) =ᵈ
      (fun raw : Fin (count+1) → Byte => eager input offset raw cache) <$> ($ᵗ (Fin (count+1) → Byte)) := by
  apply EvalDistEq.of_forall_prEvent_eq
  intro event
  have law := SampleableType.prEvent_uniformSample_equiv (split count).symm
    (fun raw => event (eager input offset raw cache))
  change Pr{let pair ← $ᵗ (Byte × (Fin count → Byte))}[
    event (eager input offset (Fin.cons pair.1 pair.2) cache)] = _ at law
  rw [SampleableType.uniformSample_prod_eq_bind] at law
  simpa only [prEvent_norm] using law


/-- The complete lazy read has the eager finite-vector law, including its
final cache. Wasted eager coins are analytical and do not count as native work. -/
theorem sample_dist (cache : Cache) (input : Input) (offset count : ℕ) :
    sample input offset count cache =ᵈ
      (fun raw : Fin count → Byte => eager input offset raw cache) <$> ($ᵗ (Fin count → Byte)) := by
  induction count generalizing offset cache with
  | zero =>
    let : MeasurableSpace (Input × Cache) := ⊤
    apply EvalDistEq.of_evalDist_eq
    simp only [sample,eager,evalDist_pure,evalDist_map_of_discrete,
      SampleableType.evalDist_uniformSample,MeasureTheory.Measure.map_const,
      MeasureTheory.measure_univ,one_smul]
  | succ count ih =>
    have composed : sample input offset (count+1) cache =ᵈ (do
        let head ← $ᵗ Byte
        let tail ← $ᵗ (Fin count → Byte)
        pure (eager input offset (Fin.cons head tail) cache)) := by
      have law := (step_dist cache (input,offset)).bind (fun first =>
        (ih first.2 (offset+1)).map (fun rest : Input × Cache => (first.1::rest.1,rest.2)))
      simpa only [sample,bind_pure_comp,bind_map_left,Functor.map_map,
        eager,Fin.cons_zero,Fin.cons_succ] using law
    exact composed.trans (eager_uniform_succ cache input offset count)


/-- Deterministic eager replay has the exact same observation-defined cache
writes as the physical native reader. -/
theorem eager_records (cache : Cache) (input : Input) (offset count : ℕ) (raw : Fin count → Byte) :
    (eager input offset raw cache).2 =
      NativeShakeHistory.writeBytes cache input offset (eager input offset raw cache).1 := by
  induction count generalizing offset cache with
  | zero => rfl
  | succ count ih =>
    simp only [eager,NativeShakeHistory.writeBytes]
    rw [← NativeShakeKernel.install_masked]
    exact ih _ _ _

/-- The returned vector masks precisely the coordinates present before the
read. Earlier positions of this read cannot alter its later coordinates. -/
theorem eager_bytes (cache : Cache) (input : Input) (offset count : ℕ) (raw : Fin count → Byte) :
    (eager input offset raw cache).1 =
      List.ofFn (fun index => (cache (input,offset+index.val)).getD (raw index)) := by
  induction count generalizing offset cache with
  | zero => rfl
  | succ count ih =>
    simp only [eager,List.ofFn_succ]
    rw [ih]
    congr 1
    congr 1
    funext index
    have different : (input,offset+1+index.val) ≠ (input,offset) := by
      intro same
      have positions := congrArg Prod.snd same
      omega
    rw [NativeShakeKernel.install_other _ _ _ _ different]
    have positions : offset+1+index.val = offset+index.succ.val := by
      change offset+1+index.val = offset+(index.val+1)
      omega
    rw [positions]


/-- The complete read result reconstructed from its finite byte vector. -/
def outcome (cache : Cache) (input : Input) (offset : ℕ) {count : ℕ} (raw : Fin count → Byte) :
    Input × Cache :=
  (List.ofFn raw,NativeShakeHistory.writeBytes cache input offset (List.ofFn raw))

/-- A finite cached interval is exactly the whole-history posterior mask. -/
theorem observed_mask (log : List Observation) (world : World) (input : Input)
    (offset count : ℕ) (raw : Fin count → Byte) :
    (fun index => ((NativeShakeKernel.observed log world) (input,offset+index.val)).getD (raw index)) =
      CachedOracleResponse.mask (ObservationReplay.footprint log) world
        (CachedOracleResponse.shakeCoordinates input offset count) raw := by
  funext index
  by_cases known : (.inl (input,offset+index.val) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.footprint log
  · simp only [NativeShakeKernel.observed,CachedOracleResponse.mask,CachedOracleResponse.shakeCoordinates,
      known,ite_true,Option.getD_some]
  · simp only [NativeShakeKernel.observed,CachedOracleResponse.mask,CachedOracleResponse.shakeCoordinates,
      known,ite_false,Option.getD_none]

/-- Eager replay retains exactly the masked output and its reconstructed cache. -/
theorem eager_observed (log : List Observation) (world : World) (input : Input)
    (offset count : ℕ) (raw : Fin count → Byte) :
    eager input offset raw (NativeShakeKernel.observed log world) =
      outcome (NativeShakeKernel.observed log world) input offset
        (CachedOracleResponse.mask (ObservationReplay.footprint log) world
          (CachedOracleResponse.shakeCoordinates input offset count) raw) := by
  apply Prod.ext
  · rw [eager_bytes,observed_mask]
    rfl
  · rw [eager_records,eager_bytes,observed_mask]
    rfl

/-- Conditional on the complete mixed past, the actual private sampler has
precisely the native read law, including the returned bytes and final cache.
No disjointness, successful-verification or new-reader premise is used. -/
theorem read_event {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (input : Input) (offset count : ℕ) (event : Input × Cache → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (outcome (NativeShakeKernel.observed (past world).run.2 world) input offset
        (InputIndexedOracle.block other input offset count))} =
      Pr{let result ← sample input offset count (NativeShakeKernel.observed (past world).run.2 world)}[
        event result] := by
  rw [(sample_dist (NativeShakeKernel.observed (past world).run.2 world) input offset count).prEvent_eq event,
    prEvent_map]
  simp only [eager_observed]
  rw [prEvent_eq_evalDist_of_discrete,SampleableType.evalDist_uniformSample]
  have response := congrArg (fun measure => measure {raw | event
      (outcome (NativeShakeKernel.observed (past world).run.2 world) input offset raw)})
    (CachedOracleResponse.shake_response replay world input offset count)
  rw [Measure.map_apply (InputIndexedOracle.block_measurable _ _ _) MeasurableSet.of_discrete,
    Measure.map_apply (CachedOracleResponse.mask_measurable _ _ _) MeasurableSet.of_discrete] at response
  simpa only [Set.preimage_ofPred_eq] using response


/-- The complete real shared read has the joint-world conditional law, with
all byte-cache and shared hash/checkpoint state retained in the event. -/
theorem shared_read_event {A Cfg Payload : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (input : Input) (offset count : ℕ)
    (event : (Input × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (outcome (NativeShakeKernel.observed (past world).run.2 world) input offset
        (InputIndexedOracle.block other input offset count),state)} =
      Pr{let result ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        ((NativeShakeCache.read (Cfg := Cfg) input offset count).run
          (NativeShakeKernel.observed (past world).run.2 world))).run state}[event result] := by
  rw [shared_read,prEvent_map]
  exact read_event replay world input offset count (fun result => event (result,state))

end
end FormalProof4FHE.HasteBoots.NativeShakeReadLaw
