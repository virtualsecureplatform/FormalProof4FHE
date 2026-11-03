module

public import FormalProof4FHE.HasteBoots.MerkleOracle

@[expose] public section

/-!
# Payload recovery from the frozen hash transcript

The resolver scans only the supplied prefix log. A matching response whose
input decodes as a leaf supplies its entire column payload. Collision-freedom
of that prefix makes the recovered payload unique. These deterministic facts
do not assert a bound on hash collisions or on later target hits.
-/

namespace FormalProof4FHE.HasteBoots.MerklePayload

noncomputable section

variable {Input Digest Payload : Type} [DecidableEq Digest]

/-- Payload candidates in prefix-log order, retaining repeated inputs. -/
def candidates (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) : List Payload :=
  log.filterMap (fun entry => if entry.2 = label then
    (MerkleTreeHashing.RoleDecoder.ofInjective (enc.leaf ())
      (enc.leaf_injective ())).decode entry.1 else none)

/-- One fixed payload resolver for the entire committed word. -/
def resolve (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) : Option Payload :=
  (candidates enc log label).head?

/-- Candidate membership is exactly the corresponding complete leaf query in the log. -/
theorem mem_candidates_iff (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) (payload : Payload) :
    payload ∈ candidates enc log label ↔
      (⟨enc.leaf () payload, label⟩ : (_input : Input) × Digest) ∈ log := by
  classical
  simp only [candidates, List.mem_filterMap]
  constructor
  · rintro ⟨⟨input, output⟩, member, decoded⟩
    split_ifs at decoded with equal
    dsimp only at equal decoded
    subst output
    have original := (MerkleTreeHashing.RoleDecoder.ofInjective (enc.leaf ())
      (enc.leaf_injective ())).encode_decode input payload decoded
    simpa only [← original] using member
  · intro member
    refine ⟨⟨enc.leaf () payload, label⟩, member, ?_⟩
    simp only [ite_true, (MerkleTreeHashing.RoleDecoder.ofInjective (enc.leaf ())
      (enc.leaf_injective ())).decode_encode]

/-- Every resolved payload has a supporting query in the same frozen prefix. -/
theorem resolve_spec (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) (payload : Payload)
    (resolved : resolve enc log label = some payload) :
    (⟨enc.leaf () payload, label⟩ : (_input : Input) × Digest) ∈ log := by
  apply (mem_candidates_iff enc log label payload).mp
  exact List.mem_of_mem_head? resolved

/-- In a collision-free prefix, an available leaf payload is recovered exactly,
independently of other query roles, log repetitions, or earlier candidates. -/
theorem resolve_of_mem (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) (payload : Payload)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (member : (⟨enc.leaf () payload, label⟩ : (_input : Input) × Digest) ∈ log) :
    resolve enc log label = some payload := by
  have available := (mem_candidates_iff enc log label payload).mpr member
  have unique : ∀ other ∈ candidates enc log label, other = payload := by
    intro other candidate
    have same := injective _ ((mem_candidates_iff enc log label other).mp candidate) _ member rfl
    exact enc.leaf_injective () same
  cases values : candidates enc log label with
  | nil => simp only [values, List.not_mem_nil] at available
  | cons head tail =>
    have same : head = payload := unique head (by simp only [values, List.mem_cons, true_or])
    simp only [resolve, values, List.head?_cons, same]

end

end FormalProof4FHE.HasteBoots.MerklePayload
