module
public import FormalProof4FHE.HasteBoots.NativeFieldVectorProgram
public import FormalProof4FHE.HasteBoots.FreshShakeTail
public import FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw
public import FormalProof4FHE.HasteBoots.CanonicalCoefficientVector
@[expose] public section

/-! The actual native shared-budget collector on a fresh unread SHAKE tail.
The initial cache is arbitrary outside that tail. Rejections/suspensions stay
in the experiment, and the scalar uniform law is derived from canonical bytes.
Causal first-exposure/lineage must still supply freshness at the right history. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldVectorFresh
open InputIndexedOracle (Input World Byte law)
open NativeRootMessage (Digest)
open NativeTranscript (FieldPhase Observation)
open NativeShakeCache (Cache)
open NativeFieldVectorProgram (program nextPhase)
open FreshShakeTail (Fresh)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

theorem lazy_map {Cfg Payload A B : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (code : OracleProgram.Program A) (f : A → B) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    NativeLazyExecution.execute enc dummy shape (OracleProgram.bind code (fun value => .pure (f value))) cache state =
      (fun result => (f result.1,result.2)) <$> NativeLazyExecution.execute enc dummy shape code cache state := by
  induction code generalizing cache state with
  | pure value => simp only [OracleProgram.bind,NativeLazyExecution.execute_pure,map_pure]
  | start input code ih =>
    simp only [OracleProgram.bind,NativeLazyExecution.execute_start,ih,Functor.map_map]
    rfl
  | read input offset count next ih =>
    simp only [OracleProgram.bind,NativeLazyExecution.execute_read,ih,map_bind,bind_map_left,map_pure]
    rfl
  | hash input next ih =>
    simp only [OracleProgram.bind,NativeLazyExecution.execute_hash,ih,map_bind,bind_map_left,map_pure]
    rfl

def candidate (p : ℕ) (raw : CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p)) : Option (ZMod p) :=
  if CanonicalTranscriptSampler.candidate p (List.ofFn raw) < p then
    some (CanonicalTranscriptSampler.candidate p (List.ofFn raw) : ZMod p) else none

theorem scalar_eq (p : ℕ) : CanonicalCoefficientVector.scalar p 1 =
    candidate p <$> ($ᵗ (CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p))) := by
  simp only [CanonicalCoefficientVector.scalar,CanonicalByteSampler.runPrefix,map_bind]
  conv_rhs => rw [← bind_pure_comp]
  congr 1
  funext raw
  rw [candidate,CanonicalTranscriptSampler.candidate_ofFn]
  split <;> simp [CanonicalCoefficientVector.value]

/-- Fresh bytes are supplied by the real owned-cache interpreter, not by
resampling cached coordinates or assuming independent native calls. -/
theorem lazy_probability {Cfg Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (p fuel count : ℕ) (phase : FieldPhase) (cache : Cache) (fresh : Fresh cache phase.pending.input phase.consumed.length)
    (event : (Fin count → ZMod p) → Prop) :
    Pr{let result ← NativeLazyExecution.execute enc dummy shape (program p fuel count phase) cache state}[result.1.elim False event] =
      Pr{let values ← BudgetedUniformSequence.program (CanonicalCoefficientVector.scalar p 1) fuel count}[values.elim False event] := by
  induction fuel generalizing count phase cache with
  | zero => cases count <;> simp [program,NativeLazyExecution.execute_pure,BudgetedUniformSequence.program,prEvent_norm]
  | succ fuel ih =>
    cases count with
    | zero => simp [program,NativeLazyExecution.execute_pure,BudgetedUniformSequence.program,prEvent_norm]
    | succ count =>
      rw [program,NativeLazyExecution.execute_read]
      let next := fun raw : Input => if CanonicalTranscriptSampler.candidate p raw < p then
        OracleProgram.bind (program p fuel count (nextPhase phase raw)) (fun result =>
          .pure (Option.map (Fin.cons (CanonicalTranscriptSampler.candidate p raw : ZMod p)) result))
        else program p fuel (count+1) (nextPhase phase raw)
      have changed := (NativeShakeReadLaw.sample_dist cache phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p)).bind_left
        (fun first => do
          let rest ← NativeLazyExecution.execute enc dummy shape (next first.1) first.2 state
          pure (NativeCheckpointProgram.prepend (.output phase.pending.input phase.consumed.length first.1) rest))
      rw [changed.prEvent_eq,bind_map_left,BudgetedUniformSequence.program]
      rw (occs := .pos [1]) [scalar_eq]
      rw [bind_map_left]
      apply prEvent_bind_congr
      intro raw
      have bytesEq := FreshShakeTail.eager_values cache phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p) fresh raw
      have laterFresh : Fresh (NativeShakeReadLaw.eager phase.pending.input phase.consumed.length raw cache).2
          (nextPhase phase (List.ofFn raw)).pending.input (nextPhase phase (List.ofFn raw)).consumed.length := by
        simpa only [nextPhase,List.length_append,List.length_ofFn] using
          FreshShakeTail.eager_fresh cache phase.pending.input phase.consumed.length (CanonicalByteSampler.byteCount p) fresh raw
      simp only [prEvent_norm,bytesEq,next,candidate]
      by_cases accepted : CanonicalTranscriptSampler.candidate p (List.ofFn raw) < p
      · simp only [accepted,ite_true,lazy_map,prEvent_map]
        have tail := ih count (nextPhase phase (List.ofFn raw)) _ laterFresh (fun values => event (Fin.cons (CanonicalTranscriptSampler.candidate p (List.ofFn raw) : ZMod p) values))
        simpa only [prEvent_map,Option.elim_map,NativeCheckpointProgram.prepend,Function.comp_def] using tail
      · simp only [accepted,ite_false]
        simpa only [NativeCheckpointProgram.prepend] using ih (count+1) (nextPhase phase (List.ofFn raw)) _ laterFresh event

/-- Exact scaled uniform law for the compiled collector on an unread tail. -/
theorem lazy_uniform {Cfg Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (p : ℕ) (valid : 1 < p) [NeZero p] (fuel count : ℕ) (phase : FieldPhase) (cache : Cache)
    (fresh : Fresh cache phase.pending.input phase.consumed.length) (event : (Fin count → ZMod p) → Prop) :
    Pr{let result ← NativeLazyExecution.execute enc dummy shape (program p fuel count phase) cache state}[result.1.elim False event] =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar p 1) fuel count * Pr{let values ← $ᵗ (Fin count → ZMod p)}[event values] := by
  rw [lazy_probability enc dummy shape state p fuel count phase cache fresh event]
  exact BudgetedUniformSequence.probability _ (CanonicalCoefficientVector.completion p 1) (CanonicalCoefficientVector.scalar_law p valid 1) fuel count event
end
end FormalProof4FHE.HasteBoots.NativeFieldVectorFresh
