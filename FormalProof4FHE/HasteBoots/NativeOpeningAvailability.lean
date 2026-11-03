module

public import FormalProof4FHE.HasteBoots.NativeMerkleExecution

@[expose] public section

/-!
# Accepted native openings agree with recorded sources

An arbitrary adaptive private/hash/checkpoint program returns a typed opening.
The native whole-column and bottom-up sibling verifier then runs through the
same shared hash. Accepted disagreement with any matching recorded root reduces
to the root-wide availability event, so it inherits the same expected-charge
bound. All prefix and verification work remains in the actual execution.
This is the authentication component, not the complete PCS or protocol theorem.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeExtractability MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.NativeOpeningAvailability

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

/-- Well-formed native path geometry. Raw vector decoding is a later refinement. -/
structure Request (height : Cfg → ℕ) where
  tag : Cfg
  root : Digest
  position : Fin (2 ^ height tag)
  payload : Payload
  leaf : Digest
  siblings : List.Vector Digest (height tag)

variable {ι : Type} {base : OracleSpec ι}

/-- Whole-payload hash followed by the native sibling loop, on the shared hash. -/
def verify (base : OracleSpec ι) (enc : MerkleOracle.Encoding Input Digest Payload)
    (height : Cfg → ℕ) (request : Request (Digest := Digest) (Payload := Payload) height) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Bool :=
  NativeMerkleExecution.embed base Cfg (NativeMerkleVerifier.verifyPayload enc (height request.tag)
    request.position.val request.payload request.leaf request.root request.siblings)

/-- The adaptive prefix may issue private draws, arbitrary hashes and any number
of root snapshots before choosing its opening. Rejection still retains this work. -/
def checked (base : OracleSpec ι) (enc : MerkleOracle.Encoding Input Digest Payload)
    (height : Cfg → ℕ)
    (front : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (Request (Digest := Digest) (Payload := Payload) height)) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (Request (Digest := Digest) (Payload := Payload) height × Bool) := do
  let request ← front
  let accepted ← verify base enc height request
  pure (request, accepted)

/-- Acceptance for a recorded root with a different or unavailable frozen
payload. A wrong total-word value is a subevent, for every chosen fallback. -/
def FalseAcceptance (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height : Cfg → ℕ) (output : Request (Digest := Digest) (Payload := Payload) height × Bool)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag))) : Prop :=
  output.2 = true ∧ ∃ checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) output.1.tag,
    ⟨output.1.tag, checkpoint⟩ ∈ state.checkpoints.checkpoints ∧
    checkpoint.root = output.1.root ∧
    MerkleAvailability.payloadAt enc dummy checkpoint.cumulativeLog checkpoint.root
      (SkeletonLeafIndex.perfectEquiv (height output.1.tag) output.1.position) ≠ some output.1.payload


omit [DecidableEq Input] in
/-- Disagreement with the single frozen total word implies the stronger event
above, for any fallback used at unavailable payloads. -/
theorem false_acceptance_of_word_disagreement
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (output : Request (Digest := Digest) (Payload := Payload) height × Bool)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag))) (accepted : output.2 = true)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) output.1.tag)
    (recorded : ⟨output.1.tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : checkpoint.root = output.1.root) (fallback : Payload)
    (different : MerkleAvailability.word enc dummy fallback (height output.1.tag)
      checkpoint.cumulativeLog checkpoint.root output.1.position ≠ output.1.payload) :
    FalseAcceptance enc dummy height output state := by
  refine ⟨accepted, checkpoint, recorded, sameRoot, ?_⟩
  intro recovered
  apply different
  simp only [MerkleAvailability.word, recovered, Option.getD_some]

section Runtime

variable [SampleableType Digest]

/-- Native acceptance establishes the exact cache premises of root-wide
availability in the same execution. No path or leaf-binding premise is assumed. -/
theorem disagreement_of_false_acceptance (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (front : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (Request (Digest := Digest) (Payload := Payload) height))
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (output : Request (Digest := Digest) (Payload := Payload) height × Bool)
    (supported : (output, after) ∈ support ((simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (checked base enc height front)).run before))
    (incorrect : FalseAcceptance enc dummy height output after) :
    CheckpointAvailability.Disagreement enc dummy (fun tag => Skeleton.perfect (height tag)) after := by
  rw [checked, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨request, middle⟩, _, remaining⟩ := supported
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at remaining
  obtain ⟨⟨accepted, finalState⟩, verified, returned⟩ := remaining
  rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at returned
  obtain ⟨equalOutput, equalState⟩ := Prod.mk.inj returned
  subst output
  subst after
  obtain ⟨acceptedTrue, checkpoint, recorded, rootEqual, different⟩ := incorrect
  change accepted = true at acceptedTrue
  subst accepted
  have authenticated := NativeMerkleExecution.payload_of_accepted implBase enc dummy
    (fun tag => Skeleton.perfect (height tag)) (height request.tag) request.position.val
      request.payload request.leaf request.root request.siblings middle finalState verified
  refine ⟨request.tag, checkpoint, recorded,
    SkeletonLeafIndex.perfectEquiv (height request.tag) request.position,
    NativeMerklePath.typedProof (height request.tag) request.position.val request.siblings,
    request.leaf, request.payload, ?_, authenticated.1, different⟩
  rw [rootEqual]
  exact authenticated.2

variable [Fintype Digest]

/-- Accepted native false openings inherit the single root-wide bound over the
complete adaptive prefix and actual verifier calls. No query cutoff or per-leaf
union bound is introduced. -/
theorem false_acceptance_le_charge (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (front : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (Request (Digest := Digest) (Payload := Payload) height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe enc dummy (fun tag => Skeleton.perfect (height tag)) state) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (checked base enc height front)).run state}[FalseAcceptance enc dummy height result.1 result.2] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag)))
        (checked base enc height front) state := by
  apply le_trans (prEvent_mono_of_support _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge implBase enc dummy
      (fun tag => Skeleton.perfect (height tag)) (checked base enc height front) state safe)
  intro result supported incorrect
  exact disagreement_of_false_acceptance implBase enc dummy height front state result.2 result.1 supported incorrect

/-- Empty shared-cache initialization discharges all initial safety premises. -/
theorem false_acceptance_from_empty_le_charge (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (front : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (Request (Digest := Digest) (Payload := Payload) height)) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (checked base enc height front)).run (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))}[
          FalseAcceptance enc dummy height result.1 result.2] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag)))
        (checked base enc height front) (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) :=
  false_acceptance_le_charge implBase enc dummy height front _
    (CheckpointCollision.safe_empty enc dummy (fun tag => Skeleton.perfect (height tag)))

end Runtime

end

end FormalProof4FHE.HasteBoots.NativeOpeningAvailability
