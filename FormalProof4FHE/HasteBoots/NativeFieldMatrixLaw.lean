module
public import FormalProof4FHE.HasteBoots.NativeFieldVectorLaw
@[expose] public section

/-! The native lane-major coefficient order is a joint uniform matrix,
including the shared-candidate-budget completion mass. The field modulus,
test-row count and source-row count are independent parameters. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldMatrixLaw
open InputIndexedOracle (Input World law)
open NativeTranscript (FieldPhase)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
noncomputable section

def index (width rows : ℕ) : Fin width × Fin rows ≃ Fin (rows*width) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm width rows))

def reshape (p width rows : ℕ) : (Fin (rows*width) → ZMod p) ≃ (Fin width → Fin rows → ZMod p) :=
  (Equiv.arrowCongr (index width rows).symm (Equiv.refl (ZMod p))).trans (Equiv.curry _ _ _)

theorem reshape_apply (p width rows : ℕ) (vector : Fin (rows*width) → ZMod p) (lane : Fin width) (row : Fin rows) :
    reshape p width rows vector lane row = vector ⟨lane.val*rows+row.val,by
      have a := lane.isLt; have b := row.isLt; nlinarith⟩ := by
  change vector ⟨row.val+rows*lane.val,_⟩ = _
  congr 1
  apply Fin.ext
  ring

theorem uniform_reshape (p width rows : ℕ) [NeZero p] (event : (Fin width → Fin rows → ZMod p) → Prop) :
    Pr{let vector ← $ᵗ (Fin (rows*width) → ZMod p)}[event (reshape p width rows vector)] =
      Pr{let matrix ← $ᵗ (Fin width → Fin rows → ZMod p)}[event matrix] :=
  SampleableType.prEvent_uniformSample_equiv (reshape p width rows) event

def values (p fuel width rows : ℕ) (phase : FieldPhase) (world : World) :=
  (NativeFieldVectorLaw.values p fuel (rows*width) phase world).map (reshape p width rows)

theorem conditional_uniform {Cfg Payload P : Type}
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (fuel width rows : ℕ) (phase : FieldPhase)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) phase.pending.input phase.consumed.length)
    (event : (Fin width → Fin rows → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values p fuel width rows phase other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar p 1) fuel (rows*width) *
        Pr{let matrix ← $ᵗ (Fin width → Fin rows → ZMod p)}[event matrix] := by
  have result := NativeFieldVectorLaw.conditional_uniform replay world enc dummy shape state hashStart p valid fuel (rows*width) phase fresh
    (fun vector => event (reshape p width rows vector))
  rw [uniform_reshape] at result
  simpa only [values,Option.elim_map,Function.comp_def] using result

/-- The entire increasing family of native candidate prefixes, not a fixed
retry limit, is bounded by the joint uniform matrix law. -/
theorem eventual_le_uniform {Cfg Payload P : Type}
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (width rows : ℕ) (phase : FieldPhase)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) phase.pending.input phase.consumed.length)
    (event : (Fin width → Fin rows → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, (values p fuel width rows phase other).elim False event} ≤
        Pr{let matrix ← $ᵗ (Fin width → Fin rows → ZMod p)}[event matrix] := by
  have result := NativeFieldVectorLaw.eventual_le_uniform replay world enc dummy shape state hashStart p valid (rows*width) phase fresh
    (fun vector => event (reshape p width rows vector))
  rw [uniform_reshape] at result
  simpa only [values,Option.elim_map,Function.comp_def] using result
end
end FormalProof4FHE.HasteBoots.NativeFieldMatrixLaw
