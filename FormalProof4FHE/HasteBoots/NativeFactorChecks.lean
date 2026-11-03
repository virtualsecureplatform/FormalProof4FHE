module

public import FormalProof4FHE.HasteBoots.JointMatrixOpening
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout

@[expose] public section

/-!
# Literal factor checks and the supplied terminal values

Coverage, both coordinate families and the final claimed-value comparison are
source-independent Boolean checks. Enforcing them in the short-circuit loop
makes them hold for every successful factor. Together with native worker replay,
a wrong supplied factor gives the exact joint PCS bad-opening event for one
fixed decoded source. Worker replay is the operational authentication interface;
this module does not assume commitment security or Fiat--Shamir security.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.NativeFactorChecks

noncomputable section

variable {F Digest Response : Type} {leftCount b m size queries height : ℕ}

/-- Executable coverage check on the original draws, before deduplication. -/
def coversCheck (columns : Columns F Digest leftCount b height) (draw : Fin queries → Fin (2 ^ height)) : Bool :=
  (List.ofFn draw).all (fun position => columns.any (fun column => column.position == position))

theorem coversCheck_iff (columns : Columns F Digest leftCount b height) (draw : Fin queries → Fin (2 ^ height)) :
    coversCheck columns draw = true ↔ NativeColumnLayout.Covers columns draw := by
  simp [coversCheck, NativeColumnLayout.Covers, List.all_eq_true, List.any_eq_true, List.mem_ofFn]

variable [Field F] [DecidableEq F]

/-- The native response checks and the claimed terminal factor value. -/
def check (domain : Fin (2 ^ height) ↪ F)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (value : Fin b → F)
    (testResponse structuredResponse : TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (data : JointMatrixOpening.Data F Digest Response leftCount b height queries) : Bool :=
  coversCheck data.2 data.1.2 &&
  NativeColumnLayout.allCoordinates data.2
    (NativeColumnLayout.flattenWeights data.1.1.1)
    (NativeColumnLayout.flattenWeights (MatrixResponse.weights left))
    (NativeColumnLayout.flattenResponse
      (MatrixOpeningSecurity.encodeMessages (m := m) domain (testResponse data.1.1.1 data.1.1.2)))
    (NativeColumnLayout.flattenResponse
      (MatrixOpeningSecurity.encodeMessages (m := m) domain (structuredResponse data.1.1.1 data.1.1.2))) &&
  decide (MatrixResponse.finishMessage right (structuredResponse data.1.1.1 data.1.1.2) = value)

theorem check_iff (domain : Fin (2 ^ height) ↪ F)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (value : Fin b → F)
    (testResponse structuredResponse : TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (data : JointMatrixOpening.Data F Digest Response leftCount b height queries) :
    check (m := m) domain left right value testResponse structuredResponse data = true ↔
      NativeColumnLayout.Covers data.2 data.1.2 ∧
      NativeColumnLayout.allCoordinates data.2
        (NativeColumnLayout.flattenWeights data.1.1.1)
        (NativeColumnLayout.flattenWeights (MatrixResponse.weights left))
        (NativeColumnLayout.flattenResponse
          (MatrixOpeningSecurity.encodeMessages (m := m) domain (testResponse data.1.1.1 data.1.1.2)))
        (NativeColumnLayout.flattenResponse
          (MatrixOpeningSecurity.encodeMessages (m := m) domain (structuredResponse data.1.1.1 data.1.1.2))) = true ∧
      MatrixResponse.finishMessage right (structuredResponse data.1.1.1 data.1.1.2) = value := by
  simp only [check, Bool.and_eq_true_iff, coversCheck_iff, decide_eq_true_eq, and_assoc]

variable {Factor Cfg Input Memory : Type} [DecidableEq Input] [DecidableEq Digest]
  {front suffix : ℕ}

omit [DecidableEq Input] in
/-- Native successful coverage and value checks turn a wrong supplied factor
into the joint PCS event on the same query-independent decoded sources.
The replay premise is discharged by completed native workers on the final cache. -/
theorem wrong_values_imply_bad_opening
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg)
    (checkpoint : ∀ factor, Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor))
    (domain : Fin (2 ^ height) ↪ F) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (query : PackedSumcheckSubclaim.Query F b (front + suffix)) (values : Factor → Fin b → F)
    (testResponse structuredResponse : Factor → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (indices : List Factor) (complete : ∀ factor, factor ∈ indices)
    (opened : ShortCircuitSequence.Outcome Factor
      (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (covered : opened.results.map Prod.fst = indices)
    (checked : ∀ entry ∈ opened.results,
      check (m := m) domain (SubclaimSourceLayout.leftWeights query) (SubclaimSourceLayout.rightWeights query)
        (values entry.1) (testResponse entry.1) (structuredResponse entry.1) entry.2 = true)
    (replays : ∀ entry ∈ opened.results, ∀ column ∈ entry.2.2,
      ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
        (AuthenticatedColumnChecks.request (fun _ : Cfg => height) (tag entry.1) (checkpoint entry.1).root column)
        state.hash.cache)
    (different : ∃ factor, values factor ≠ query.fold
      (SubclaimSourceLayout.decodedSource domain capacity radius
        (JointMatrixOpening.frozen enc dummy tag checkpoint factor))) :
    JointMatrixOpening.AnyAcceptedWrong enc dummy tag checkpoint domain capacity radius
      (fun _ => SubclaimSourceLayout.leftWeights query) (fun _ => SubclaimSourceLayout.rightWeights query)
      testResponse structuredResponse ((opened.results, opened.memory), state) := by
  obtain ⟨factor, wrong⟩ := different
  have occurs : factor ∈ opened.results.map Prod.fst := by rw [covered]; exact complete factor
  obtain ⟨entry, member, sameFactor⟩ := List.mem_map.mp occurs
  subst factor
  obtain ⟨columnsCovered, coordinates, finished⟩ :=
    (check_iff domain (SubclaimSourceLayout.leftWeights query) (SubclaimSourceLayout.rightWeights query)
      (values entry.1) (testResponse entry.1) (structuredResponse entry.1) entry.2).mp (checked entry member)
  refine ⟨entry, member, ?_, columnsCovered, replays entry member, coordinates⟩
  rw [finished, ← SubclaimSourceLayout.fold_decodedSource]
  exact wrong

variable [SampleableType Digest]

/-- In an actual successful short-circuit execution, factor coverage and the
native response/value checks follow from the program. Only the independent
native worker replay interface remains to instantiate authentication. -/
theorem successful_wrong_values_imply_bad_opening
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg)
    (checkpoint : ∀ factor, Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor))
    (domain : Fin (2 ^ height) ↪ F) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (query : PackedSumcheckSubclaim.Query F b (front + suffix)) (values : Factor → Fin b → F)
    (testResponse structuredResponse : Factor → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (indices : List Factor) (complete : ∀ factor, factor ∈ indices)
    (opened : ShortCircuitSequence.Outcome Factor
      (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (raw : Factor → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (ShortCircuitSequence.StepResult
        (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory))
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (supported : (opened, state) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun _ : Cfg => Skeleton.perfect height))
      (ShortCircuitSequence.program (ShortCircuitSequence.enforce (fun factor => check (m := m) domain (SubclaimSourceLayout.leftWeights query)
          (SubclaimSourceLayout.rightWeights query) (values factor) (testResponse factor) (structuredResponse factor)) raw)
        indices memory)).run initial))
    (accepted : opened.accepted = true)
    (replays : ∀ entry ∈ opened.results, ∀ column ∈ entry.2.2,
      ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
        (AuthenticatedColumnChecks.request (fun _ : Cfg => height) (tag entry.1) (checkpoint entry.1).root column)
        state.hash.cache)
    (different : ∃ factor, values factor ≠ query.fold
      (SubclaimSourceLayout.decodedSource domain capacity radius
        (JointMatrixOpening.frozen enc dummy tag checkpoint factor))) :
    JointMatrixOpening.AnyAcceptedWrong enc dummy tag checkpoint domain capacity radius
      (fun _ => SubclaimSourceLayout.leftWeights query) (fun _ => SubclaimSourceLayout.rightWeights query)
      testResponse structuredResponse ((opened.results, opened.memory), state) := by
  let checkFactors : Factor → JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries → Bool :=
    (fun factor => check (m := m) domain (SubclaimSourceLayout.leftWeights query)
          (SubclaimSourceLayout.rightWeights query) (values factor) (testResponse factor) (structuredResponse factor))
  have covered := ShortCircuitSequence.accepted_indices enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (ShortCircuitSequence.enforce checkFactors raw) indices memory initial (opened, state) supported accepted
  have checked := ShortCircuitSequence.enforced_results enc dummy (fun _ : Cfg => Skeleton.perfect height)
    checkFactors raw indices memory initial (opened, state) supported accepted
  exact wrong_values_imply_bad_opening enc dummy tag checkpoint domain capacity radius query values
    testResponse structuredResponse indices complete opened state covered checked replays different

end

end FormalProof4FHE.HasteBoots.NativeFactorChecks
