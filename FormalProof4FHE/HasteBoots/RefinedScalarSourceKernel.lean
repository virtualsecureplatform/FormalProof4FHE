module
public import FormalProof4FHE.HasteBoots.ReferenceBadLedger
public import FormalProof4FHE.HasteBoots.ScalarSourceChallengeBound
@[expose] public section

/-! The source-derived all-budget scalar agreement bound holds on the joint
parent/receipt completion fiber. A retained-state wrapper adapts the existing
fresh-stream lemma; it executes no new query and makes no physical-work claim. -/
namespace FormalProof4FHE.HasteBoots.RefinedScalarSourceKernel
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution Observation)
open NativeRootMessage (Digest)
open OracleProgram (Program runPrefix)
open JobReferenceCandidate (Candidate)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def retained {T : Type} (past : World → Execution T) (world : World) : Execution (T ⊕ Unit) :=
  WriterT.mk (.inl (past world).run.1,(past world).run.2)

theorem retained_replay {T : Type} {past : World → Execution T} (old : ObservationReplay.Replayable past) :
    ObservationReplay.Replayable (retained past) := by
  constructor
  · exact old.truthful
  · intro world other agrees
    have same := old.replay world other agrees
    simp only [retained,WriterT.run_mk,same]

theorem retained_packet {T : Type} (past : World → Execution T) (world other : World) :
    (retained past other).run = (retained past world).run ↔ (past other).run = (past world).run := by
  constructor
  · intro same
    have parts := Prod.mk.inj same
    exact Prod.ext (Sum.inl.inj parts.1) parts.2
  · intro same
    simp only [retained,WriterT.run_mk,same]

/-- This describes eligibility of an already unseen logical stream. It is
not executed and adds no observation to the retained history. -/
def pending {T : Type} (input : Input) (state : T) : OracleMachine.Command T Unit := .read input 0 1 (fun _ => state)

theorem unseen {A : Type} (program : Program A) (position : ℕ) (world : World) (candidate : Candidate program position world) :
    CausalStreamExposure.seen (ParentFactorFiber.extend (runPrefix position program) world).run.2 candidate.selection.family.input = false := by
  let first := PositionedFactorSamples.reindex candidate.first _ _ candidate.compression.world_eq candidate.compression.input_eq
  have fresh := ParentFactorFiber.unseen candidate.compression.value.toSample program first
  change CausalStreamExposure.seen (ParentFactorFiber.extend (runPrefix candidate.first.position program) candidate.compression.value.view.reader.world).run.2
    candidate.compression.value.view.reader.entry.coefficients.phase.pending.input = false at fresh
  rw [candidate.first_position,candidate.compression.world_eq,candidate.compression.input_eq] at fresh
  exact fresh

theorem selected {A : Type} (program : Program A) (position : ℕ) (world : World) (candidate : Candidate program position world) :
    CausalStreamExposure.firstRead (pending candidate.selection.family.input)
      (retained (ParentFactorFiber.extend (runPrefix position program)) world).run = some candidate.selection.family.input := by
  simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,retained,WriterT.run_mk,pending,unseen program position world candidate,
    show 0 < (1 : ℕ) from by decide,and_self,ite_true]

theorem source_bound {A Factor Term : Type} [Fintype Term] (program : Program A) (position : ℕ) (world : World)
    (candidate : Candidate program position world) (dummy profile : Digest)
    (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover candidate.selection.family.input = some configuration)
    (info : NativeScalarBatchWire.Info) (message : NativeScalarBatchWire.Message)
    (arity : Term → ℕ) (coefficient : Term → NativeExtensionFields.Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ)
    (tables : Factor → MatrixFold.Cube n → NativeExtensionFields.Goldilocks3) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | ScalarRecoveredUnboundedLaw.event candidate.selection.family.input configuration profile
        (ScalarSourceChallengeBound.test info message arity coefficient indices n tables) other} ≤
          (info.maxMultiplicands.val : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  have bound := ScalarSourceChallengeBound.bound (retained_replay (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)))
    (pending candidate.selection.family.input) world dummy profile candidate.selection.family.input configuration found
    (selected program position world candidate) info message arity coefficient indices n tables
  simpa only [retained_packet] using bound

end
end FormalProof4FHE.HasteBoots.RefinedScalarSourceKernel
