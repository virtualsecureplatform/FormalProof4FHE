module

public import FormalProof4FHE.HasteBoots.JointHashCache
public import FormalProof4FHE.HasteBoots.CachedHashCollision
public import FormalProof4FHE.HasteBoots.CachedHashCheckpoint

@[expose] public section

/-!
# Joint-world SHA-512 steps refine the existing cached hash handler

Conditioning includes the complete mixed-oracle history, not only the hash
projection. A new hash input receives the canonical uniform digest; a cached
input receives its recorded digest. The same cache/log/key update then
permits reuse of the existing collision charge with exact alphabet 2^512.
Rust byte serialization, backend/scheduler refinement, and whole-protocol
placement remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.JointHashKernel

open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open InputIndexedOracle (Input World law sha512)
open NativeTranscript (Execution Observation)
open JointHashCache (Digest State project record)

noncomputable section

def answer (state : State) (input : Input) : ProbComp Digest :=
  Prod.fst <$> (CachedHashHandler.handler input).run state

theorem answer_cached (state : State) (input : Input) (digest : Digest)
    (known : state.cache input = some digest) : answer state input = pure digest := by
  rw [answer, CachedHashHandler.run_cached state input digest known, map_pure]

theorem answer_fresh (state : State) (input : Input) (fresh : state.cache input = none) :
    answer state input = $ᵗ Digest := by
  rw [answer, CachedHashHandler.run_fresh state input fresh, Functor.map_map]
  change id <$> ($ᵗ Digest) = $ᵗ Digest
  exact id_map _

/-- The entire preceding SHAKE/hash transcript conditions this digest law. -/
theorem reply_law {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) :
    (law[|{other | (past other).run = (past world).run}]).map (fun other => sha512 other input) =
      𝒟[answer (project (past world).run.2) input] := by
  have valid := JointHashCache.project_valid world (past world).run.2 (replay.truthful world)
  cases known : (project (past world).run.2).cache input with
  | none =>
    have fresh : input ∉ (project (past world).run.2).keys := by
      intro present
      obtain ⟨digest, cached⟩ := (valid.1.mem_keys_iff input).mp present
      rw [known] at cached
      contradiction
    rw [answer_fresh _ _ known, SampleableType.evalDist_uniformSample,
      ObservationReplay.fiber_eq_assignment replay world]
    exact CachedOracleResponse.fresh_response _ world (CachedOracleResponse.hashCoordinates input)
      (CachedOracleResponse.hash_distinct input) (fun i member =>
        fresh ((JointHashCache.hash_coordinate_seen _ input i).mp member))
  | some digest =>
    have same := valid.2 input digest known
    have seen : input ∈ (project (past world).run.2).keys := (valid.1.mem_keys_iff input).mpr ⟨digest, known⟩
    rw [answer_cached _ _ _ known, evalDist_pure, same,
      ObservationReplay.fiber_eq_assignment replay world]
    exact CachedOracleResponse.repeated_response _ world (CachedOracleResponse.hashCoordinates input)
      (CachedOracleResponse.hash_distinct input)
      (fun i => (JointHashCache.hash_coordinate_seen _ input i).mpr seen)

def normalize (state : State) (input : Input) (result : Digest × State) : Digest × State :=
  (result.1, record state (.hash input (List.ofFn result.1)))

/-- Reconstructing the updated cache from the actual recorded digest is
exactly the old handler state, on both hits and misses. -/
theorem handler_normalize (state : State) (input : Input) :
    normalize state input <$> (CachedHashHandler.handler input).run state =
      (CachedHashHandler.handler input).run state := by
  cases known : state.cache input with
  | none =>
    rw [CachedHashHandler.run_fresh state input known, Functor.map_map]
    congr 1
    funext digest
    simp only [normalize, record, JointHashCache.decode_ofFn]
  | some digest =>
    rw [CachedHashHandler.run_cached state input digest known, map_pure]
    congr 1
    simp only [normalize, record, JointHashCache.decode_ofFn, JointHashCache.cacheQuery_known state input digest known]

theorem reply_event {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) (event : Digest → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | event (sha512 other input)} =
      Pr{let result ← (CachedHashHandler.handler input).run (project (past world).run.2)}[event result.1] := by
  rw [← prEvent_map]
  rw [prEvent_eq_evalDist_of_discrete]
  change _ = 𝒟[answer (project (past world).run.2) input] {x | event x}
  rw [← reply_law replay world input]
  exact (Measure.map_apply (InputIndexedOracle.hash_measurable input) MeasurableSet.of_discrete).symm

/-- Any predicate on the entire actual updated hash state has the old
handler's event probability, with repeated entries preserved. -/
theorem step_event {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) (event : Digest × State → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (sha512 other input, record (project (past world).run.2)
        (.hash input (List.ofFn (sha512 other input))))} =
      Pr{let result ← (CachedHashHandler.handler input).run (project (past world).run.2)}[event result] := by
  rw [reply_event replay world input (fun digest => event (digest,
    record (project (past world).run.2) (.hash input (List.ofFn digest))))]
  change Pr{let result ← (CachedHashHandler.handler input).run (project (past world).run.2)}[
    event (normalize (project (past world).run.2) input result)] = _
  rw [← prEvent_map, handler_normalize]

set_option exponentiation.threshold 1024 in
theorem digest_card : Fintype.card Digest = 2 ^ 512 := by
  simp only [JointHashCache.Digest, Fintype.card_fun, Fintype.card_fin]
  norm_num

/-- Concrete collision hazard in the joint world, without assuming XOF
freshness or bounding the number of earlier calls. Existing collisions are
an inherited event and must not be discarded by later composition. -/
theorem collision_step {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input)
    (safe : ¬CacheHasCollision (project (past world).run.2).cache) :
    (law[|{other | (past other).run = (past world).run}])
      {other | CacheHasCollision (record (project (past world).run.2)
        (.hash input (List.ofFn (sha512 other input)))).cache} ≤
      if (project (past world).run.2).cache input = none then
        ((project (past world).run.2).keys.card : ENNReal) / (2 : ENNReal) ^ 512 else 0 := by
  rw [step_event replay world input (fun result => CacheHasCollision result.2.cache)]
  have bound := CachedHashCollision.step_loss_bound (project (past world).run.2)
    (JointHashCache.project_valid world _ (replay.truthful world)).1 safe input
  simpa only [CachedHashCollision.loss, digest_card, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- The existing root-wide payload checkpoint charge remains valid after
conditioning on the complete mixed-oracle history. Earlier instability
must be retained separately when composing these conditional steps. -/
theorem checkpoint_step {A Cfg Payload : Type} {past : World → Execution A}
    (replay : ObservationReplay.Replayable past) (world : World) (input : Input)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints
      (project (past world).run.2).log) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ¬MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints
        (record (project (past world).run.2)
          (.hash input (List.ofFn (sha512 other input)))).log} ≤
      if (project (past world).run.2).cache input = none then
        ((min checkpoints.totalNodeBudget
          (2 * (project (past world).run.2).keys.card + checkpoints.checkpoints.length) : ℕ) : ENNReal) /
          (2 : ENNReal) ^ 512 else 0 := by
  rw [step_event replay world input (fun result =>
    ¬MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints result.2.log)]
  have bound := CachedHashCheckpoint.step_loss_bound enc dummy shape checkpoints
    (project (past world).run.2)
    (JointHashCache.project_valid world _ (replay.truthful world)).1 stable input
  simpa only [digest_card, Nat.cast_pow, Nat.cast_ofNat] using bound

end

end FormalProof4FHE.HasteBoots.JointHashKernel
