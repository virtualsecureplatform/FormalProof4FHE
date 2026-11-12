module
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
public import FormalProof4FHE.HasteBoots.NTTLoopProbability
@[expose] public section

/-! Original complete-PBS root slots instantiate the ordered concrete NTT
loop. Its trusted child list and both public roots come from the same original
reference family; retained root binding follows from actual loop support. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSNTTLoop
open OracleSpec OracleComp
open NativeRootMessage (Digest)
noncomputable section
variable {q log count b c r k front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family count)
  (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)

/-- Factories retain their calls/private memory but cannot substitute public
coefficient/evaluation roots or the concrete proved NTT transform. -/
def factory (slot : Fin (count+1)) (memory : Memory) :=
  CallerBoundStageRoots.ntt (family.coefficients slot) (family.evaluations slot)
    (PackedNTT.scheme length psi primitive (base slot memory))

def program (memory : Memory) :=
  NTTSequence.program (factory length psi primitive family base) (List.finRange (count+1)) memory

def witness (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :=
  NTTSequence.witness (factory length psi primitive family base) enc dummy (List.finRange (count+1)) memory initial

/-- The original reference list instantiates actual NTT child programs,
including early return, private memory handoff and the exact final history. -/
theorem project_witness (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    (fun outcome => (NTTSequence.erase outcome.1,outcome.2)) <$>
      witness length psi primitive family base enc dummy memory initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (RecordedSourceCoherence.Shape Cfg height)) (program length psi primitive family base memory)).run initial :=
  NTTSequence.project_witness _ enc dummy (List.finRange (count+1)) memory initial

variable (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (outcome : NTTSequenceSoundness.Trace (F := ZMod q) (Index := Fin (count+1)) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (supported : outcome ∈ support (witness length psi primitive family base enc dummy memory initial))

include supported in
/-- Every retained child used exactly its original public root pair, derived
from actual reached support at an actual incoming state. -/
theorem retained_roots
    (entry : Fin (count+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results) :
    entry.2.2.1.1.1 = (fun side : Bool => if side then family.evaluations entry.1 else family.coefficients entry.1) := by
  obtain ⟨before,childSupported⟩ := NTTSequenceSoundness.retained_child_support
    (factory length psi primitive family base) enc dummy (List.finRange (count+1)) memory initial outcome supported entry member
  exact HadamardNTTSourceAssociation.fixed_roots enc dummy
    (fun side : Bool => if side then family.evaluations entry.1 else family.coefficients entry.1)
    (base entry.1 entry.2.1).commit
    (CommittedJointMatrixOpening.requests (factory length psi primitive family base entry.1 entry.2.1).tag [false,true])
    (AuthenticatedNTT.continuation (factory length psi primitive family base entry.1 entry.2.1)) before entry.2.2 childSupported

include supported in
/-- An accepted packed loop covers the trusted native child order exactly. -/
theorem accepted_slots (accepted : outcome.1.accepted = true) :
    outcome.1.results.map Prod.fst = List.finRange (count+1) :=
  NTTSequenceSoundness.accepted_indices (factory length psi primitive family base) enc dummy
    (List.finRange (count+1)) memory initial outcome supported accepted

include supported in
/-- Every original slot, including the final result, has a retained child
with its exact public coefficient/evaluation roots in an accepted loop. -/
theorem all_slots_bound (accepted : outcome.1.accepted = true) (slot : Fin (count+1)) :
    ∃ incoming child, (slot,(incoming,child)) ∈ outcome.1.results ∧
      child.1.1.1 false = family.coefficients slot ∧ child.1.1.1 true = family.evaluations slot := by
  have covered := accepted_slots length psi primitive family base enc dummy memory initial outcome supported accepted
  have present : slot ∈ outcome.1.results.map Prod.fst := by rw [covered]; exact List.mem_finRange slot
  obtain ⟨entry,member,equal⟩ := List.mem_map.mp present
  have roots := retained_roots length psi primitive family base enc dummy memory initial outcome supported entry member
  rcases entry with ⟨index,incoming,child⟩
  change index = slot at equal
  subst index
  exact ⟨incoming,child,member,congrFun roots false,congrFun roots true⟩


include supported in
/-- The retained child evaluation root and both collected views refer to
one original parameter-store entry, rather than a newly matched geometry. -/
theorem retained_evaluation_alias
    (entry : Fin (count+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results)
    (entries : List NativeGoldParameterStore.Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (nttRegistry hadamardRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : NativeGoldParameterStore.collect entries (PackedPBSOriginalReferences.ntt family entry.1) = some nttRegistry)
    (hadamardCollected : NativeGoldParameterStore.collect entries (PackedPBSOriginalReferences.hadamard family) = some hadamardRegistry) :
    ∃ original, entries[family.evaluationHandle]? = some original ∧ NativeGoldParameterStore.GoodEntry original ∧
      nttRegistry[1]? = some ⟨original.initialized.parameters,entry.2.2.1.1.1 true⟩ ∧
      hadamardRegistry[(PBSHadamard.address (PackedPBSOriginalReferences.evaluationFactor entry.1)).val]? =
        some ⟨original.initialized.parameters,entry.2.2.1.1.1 true⟩ := by
  have roots := retained_roots length psi primitive family base enc dummy memory initial outcome supported entry member
  have evaluation : entry.2.2.1.1.1 true = family.evaluations entry.1 := congrFun roots true
  obtain ⟨original,stored,good,nttOracle,hadamardOracle⟩ := PackedPBSOriginalReferences.original_evaluation_alias
    family entry.1 entries reachable nttRegistry hadamardRegistry nttCollected hadamardCollected
  rw [←evaluation] at nttOracle hadamardOracle
  exact ⟨original,stored,good,nttOracle,hadamardOracle⟩

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- The fixed original-slot loop inherits the summed NTT arithmetic/PCS
rates and ONE collision charge on its actual concrete child execution. -/
theorem original_risk_bound [Fintype Digest] [NeZero m] [NeZero b]
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (basis : Module.Basis (Fin b) (ZMod q) K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = enc)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot)
    (memory : Memory) :
    Pr{let result ← (witness length psi primitive family base enc dummy memory
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      NTTLoopProbability.AnyRisk (factory length psi primitive family base) dummy capacity radius result.1] ≤
    ((List.finRange (count+1)).map epsilon).sum +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (program length psi primitive family base memory)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  exact NTTLoopProbability.native_original_risk_bound (factory length psi primitive family base) enc dummy
    (List.finRange (count+1)) basis enough capacity radius epsilon
    (fun slot _ incoming => encoding slot incoming)
    (fun slot _ incoming => small slot incoming)
    (fun slot _ incoming => calibrated slot incoming) memory

end
end FormalProof4FHE.HasteBoots.PackedPBSNTTLoop
