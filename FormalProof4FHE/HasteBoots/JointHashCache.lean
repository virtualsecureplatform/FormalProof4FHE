module

public import FormalProof4FHE.HasteBoots.CachedOracleResponse
public import FormalProof4FHE.HasteBoots.CachedHashHandler

@[expose] public section

/-!
# SHA-512 cache projection of the joint SHAKE/hash history

The projection reads hash observations only, preserves repeated entries,
and reconstructs each complete digest from its recorded bytes. SHAKE
starts/outputs never populate this cache. Coherence is derived from the
truthful mixed history, without collision freedom or fresh-input premises.
-/

namespace FormalProof4FHE.HasteBoots.JointHashCache

open InputIndexedOracle (Byte Input World sha512)
open NativeTranscript (Observation)
open ObservationReplay (Agrees)
open OracleSpec

abbrev Digest := Fin 64 → Byte
abbrev State := CachedHashHandler.State Input Digest

def decode (bytes : Input) : Digest := fun i => bytes[i.val]?.getD 0

theorem decode_ofFn (digest : Digest) : decode (List.ofFn digest) = digest := by
  funext i
  unfold decode
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [Option.getD_some, List.getElem_ofFn]

def record (state : State) : Observation → State
  | .hash input digest =>
      CachedHashHandler.observe state input (decode digest) (state.cache.cacheQuery input (decode digest))
  | _ => state

def project (log : List Observation) : State := log.foldl record CachedHashHandler.empty

def AgreesWorld (world : World) (state : State) : Prop :=
  ∀ input answer, state.cache input = some answer → answer = sha512 world input

theorem empty_agrees (world : World) : AgreesWorld world CachedHashHandler.empty := by
  intro input answer known
  cases known

theorem cacheQuery_known (state : State) (input : Input) (answer : Digest)
    (known : state.cache input = some answer) : state.cache.cacheQuery input answer = state.cache := by
  apply QueryCache.ext
  intro other
  by_cases same : other = input
  · subst other
    rw [QueryCache.cacheQuery_self, known]
  · exact QueryCache.cacheQuery_of_ne _ _ same

theorem record_valid (world : World) (state : State) (entry : Observation)
    (coherent : CachedHashHandler.Coherent state) (agrees : AgreesWorld world state)
    (truthful : ObservationReplay.Matches world entry) :
    CachedHashHandler.Coherent (record state entry) ∧ AgreesWorld world (record state entry) := by
  cases entry with
  | start => exact ⟨coherent, agrees⟩
  | output => exact ⟨coherent, agrees⟩
  | hash input digest =>
    change List.ofFn (sha512 world input) = digest at truthful
    subst digest
    simp only [record, decode_ofFn]
    constructor
    · cases known : state.cache input with
      | none => exact CachedHashHandler.coherent_fresh state coherent input _ known
      | some answer =>
        have same := agrees input answer known
        subst answer
        rw [cacheQuery_known state input _ known]
        exact CachedHashHandler.coherent_cached state coherent input _ known
    · intro other answer known
      by_cases same : other = input
      · subst other
        rw [CachedHashHandler.observe, QueryCache.cacheQuery_self] at known
        exact (Option.some.inj known).symm
      · change (state.cache.cacheQuery input (sha512 world input)) other = some answer at known
        rw [QueryCache.cacheQuery_of_ne _ _ same] at known
        exact agrees other answer known

theorem fold_valid (world : World) (log : List Observation) (state : State)
    (truthful : Agrees world log) (coherent : CachedHashHandler.Coherent state) (agrees : AgreesWorld world state) :
    CachedHashHandler.Coherent (log.foldl record state) ∧ AgreesWorld world (log.foldl record state) := by
  induction log generalizing state with
  | nil => exact ⟨coherent, agrees⟩
  | cons entry tail ih =>
    have updated := record_valid world state entry coherent agrees (truthful entry (by simp))
    exact ih (record state entry) (fun next member => truthful next (by simp [member])) updated.1 updated.2

theorem project_valid (world : World) (log : List Observation) (truthful : Agrees world log) :
    CachedHashHandler.Coherent (project log) ∧ AgreesWorld world (project log) :=
  fold_valid world log _ truthful CachedHashHandler.coherent_empty (empty_agrees world)

theorem project_append (log : List Observation) (entry : Observation) :
    project (log ++ [entry]) = record (project log) entry := by simp [project]

def hashInputs : List Observation → List Input
  | [] => []
  | .hash input _ :: tail => input :: hashInputs tail
  | _ :: tail => hashInputs tail

theorem keys_record (state : State) (entry : Observation) :
    (record state entry).keys = state.keys ∪ (hashInputs [entry]).toFinset := by
  cases entry <;> simp [record, CachedHashHandler.observe, hashInputs]

theorem hashInputs_append (first last : List Observation) :
    hashInputs (first ++ last) = hashInputs first ++ hashInputs last := by
  induction first with
  | nil => rfl
  | cons entry tail ih => cases entry <;> simp [hashInputs, ih]

theorem project_keys (log : List Observation) : (project log).keys = (hashInputs log).toFinset := by
  induction log using List.reverseRecOn with
  | nil => rfl
  | append_singleton entry log ih =>
    rw [project_append, keys_record, ih, hashInputs_append, List.toFinset_append]

theorem mem_hashInputs (log : List Observation) (input : Input) :
    input ∈ hashInputs log ↔ ∃ digest, Observation.hash input digest ∈ log := by
  induction log with
  | nil => simp [hashInputs]
  | cons entry tail ih => cases entry <;> simp [hashInputs, ih, exists_or]

/-- Every recorded hash reveals all 64 digest coordinates; SHAKE reveals
none of them, even when its complete input byte string is equal. -/
theorem hash_coordinate_seen (log : List Observation) (input : Input) (i : Fin 64) :
    (.inr (input, i) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.footprint log ↔ input ∈ (project log).keys := by
  rw [project_keys, List.mem_toFinset, mem_hashInputs]
  simp only [ObservationReplay.footprint, Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro ⟨entry, member, coordinate⟩
    cases entry with
    | start => simp [ObservationReplay.coordinates] at coordinate
    | output => simp [ObservationReplay.coordinates] at coordinate
    | hash other digest =>
      obtain ⟨index, _, equal⟩ := Finset.mem_image.mp coordinate
      have same := (Prod.mk.inj (Sum.inr.inj equal)).1
      subst other
      exact ⟨digest, member⟩
  · rintro ⟨digest, member⟩
    exact ⟨.hash input digest, member, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

end FormalProof4FHE.HasteBoots.JointHashCache
