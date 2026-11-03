module

public import FormalProof4FHE.HasteBoots.RejectionSampling
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# Reciprocal offset retries: exact ideal law and expected candidate count

The loop tests the same zero and public-table pole exclusions as the native
challenge routine. Its unbounded output law is proved from all operational
prefixes. Every attempted candidate is retained, and the expected count has
an exact cardinality formula and the public worst-case domain bound.

This counts fresh ideal extension-field candidates, not transcript bytes or
primitive hashes. The byte sampler, child transcript and Rust refinement are
still required to transfer this result to native hash work.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.ReciprocalRejection

noncomputable section

variable {K Cfg Input Digest Payload : Type} [Field K] [DecidableEq K] [Fintype K] [SampleableType K]
  {size : ℕ}

/-- `none` is a suspended analysis prefix, retaining all candidates. -/
def runPrefix (table : Fin size → K) (fuel : ℕ) : ProbComp (RejectionSampling.Result K) :=
  RejectionSampling.runPrefix (ReciprocalDetection.allowed table) fuel

/-- The unbounded ideal retry law is exactly the accepted-domain law already
used by the complete staged private lookup theorem. -/
theorem law (table : Fin size → K) (event : K → Prop) :
    RejectionSampling.eventProbability (ReciprocalDetection.allowed table) event =
      Pr{let candidate ← ReciprocalDetection.sample table}[event candidate] :=
  RejectionSampling.eventProbability_eq_uniform _ _

/-- The exact number of distinct excluded poles is respected, so repeated
public hashes do not inflate the actual expected cost. -/
theorem expected_candidates (table : Fin size → K) :
    RejectionSampling.totalExpectedAttempts (ReciprocalDetection.allowed table) =
      (Fintype.card K : ENNReal) / (ReciprocalDetection.allowed table).card :=
  RejectionSampling.totalExpectedAttempts_fraction _

/-- The public table-size estimate bounds the unbounded expected count; it
is not a pathwise cap on the number of retries. -/
theorem expected_candidates_bound (table : Fin size → K) :
    RejectionSampling.totalExpectedAttempts (ReciprocalDetection.allowed table) ≤
      (Fintype.card K : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal) := by
  rw [expected_candidates]
  gcongr
  exact_mod_cast ReciprocalDetection.allowed_card_lower table

/-- Nonemptiness gives almost-sure completion, without a retry budget. -/
theorem suspension_tends_to_zero (table : Fin size → K) (enough : size + 1 < Fintype.card K) :
    Filter.Tendsto (fun fuel => Pr{let result ← runPrefix table fuel}[result.1 = none])
      Filter.atTop (nhds 0) :=
  RejectionSampling.suspension_tends_to_zero _ (ReciprocalDetection.allowed_nonempty table enough)

/-- Private retries preserve every preexisting hash/cache/checkpoint component
on each real operational prefix, even when the prefix suspends. -/
theorem runPrefix_state [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (table : Fin size → K) (fuel : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PrivateSampling.embed Cfg Input Digest (runPrefix table fuel))).run state =
      (fun result => (result, state)) <$> runPrefix table fuel :=
  PrivateSampling.run_probComp enc dummy shape _ state

end

end FormalProof4FHE.HasteBoots.ReciprocalRejection
