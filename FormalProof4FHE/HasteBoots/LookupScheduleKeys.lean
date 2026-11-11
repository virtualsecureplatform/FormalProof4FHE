module
public import FormalProof4FHE.HasteBoots.NativeSharedLookupStatement
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.OfFn
@[expose] public section

/-! Unique native request/repetition keys identify completed batch records.
Equal request tables and repeated source addresses do not merge scheduled jobs. -/
namespace FormalProof4FHE.HasteBoots.LookupScheduleKeys
open InputIndexedOracle (World)
open NativeSharedLookupStatement (Request Tagged tags)
noncomputable section

def keys {count : ℕ} (repetitions : Fin count → ℕ) : List (ℕ × ℕ) :=
  (List.ofFn (fun index : Fin count => List.ofFn (fun repetition : Fin (repetitions index) => (index.val,repetition.val)))).flatten

def tagKey (tag : Tagged) : ℕ × ℕ := (tag.ordinal.val,tag.repetition)
def jobKey {p : ℕ} (job : NativeLookupBatch.Job p) : ℕ × ℕ := (job.ordinal.val,job.repetition)

theorem keys_nodup {count : ℕ} (repetitions : Fin count → ℕ) : (keys repetitions).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro entries member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    apply List.nodup_ofFn.mpr
    intro left right same
    exact Fin.ext (congrArg Prod.snd same)
  · apply List.pairwise_ofFn.mpr
    intro left right ordered
    apply List.disjoint_left.mpr
    intro entry inLeft inRight
    obtain ⟨first,firstEq⟩ := List.mem_ofFn.mp inLeft
    obtain ⟨second,secondEq⟩ := List.mem_ofFn.mp inRight
    have equal := congrArg Prod.fst (firstEq.trans secondEq.symm)
    have less : left.val < right.val := ordered
    omega

theorem tags_keys {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) :
    (tags fits requests).map tagKey = keys (fun index => (requests index).repetitions) := by
  simp only [tags,keys,List.map_flatten,List.map_ofFn,Function.comp_def,tagKey]

theorem tags_nodup {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) :
    ((tags fits requests).map tagKey).Nodup := by rw [tags_keys]; exact keys_nodup _

/-- Successful native completion supplies a unique-key list, including all
original repetitions in their actual order. -/
theorem completed_nodup {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (w fuel : ℕ) (transcript : NativeTranscript.Transcript) (world : World) (final : NativeTranscript.Transcript)
    (finished : (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis w fuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.control = .finished final) :
    ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis w fuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed.map
        (fun entry => jobKey entry.job)).Nodup := by
  have ordered := NativeSharedLookupStatement.finished_jobs fits requests w fuel transcript world final finished
  have mapped := congrArg (List.map jobKey) ordered
  simp only [List.map_map,Function.comp_def] at mapped
  rw [mapped]
  exact tags_nodup fits requests

/-- A member's unique key identifies the literal record at an indexed slot.
Neither an equality of records nor a supplied record index is assumed. -/
theorem get_of_key {α β : Type} (entries : List α) (key : α → β) (unique : (entries.map key).Nodup)
    (index : ℕ) (entry : α) (member : entry ∈ entries)
    (keyAt : (entries.map key)[index]? = some (key entry)) : entries[index]? = some entry := by
  cases found : entries[index]? with
  | none =>
    simp only [List.getElem?_map,found,Option.map_none] at keyAt
    contradiction
  | some actual =>
    have sameKey : key actual = key entry := by simpa only [List.getElem?_map,found,Option.map_some,Option.some.injEq] using keyAt
    have same := List.inj_on_of_nodup_map unique (List.mem_of_getElem? found) member sameKey
    exact congrArg some same

end
end FormalProof4FHE.HasteBoots.LookupScheduleKeys
