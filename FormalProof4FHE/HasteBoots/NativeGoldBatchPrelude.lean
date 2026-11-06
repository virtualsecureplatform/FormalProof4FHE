module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchOpening
public import FormalProof4FHE.HasteBoots.NativeGoldBatchBinding
public import FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude
@[expose] public section

/-! Checked native batch binding precedes proof-shape checking and one shared
random-test matrix request. Rejections retain the actual mutated parent and
observations; analysis suspension is not native rejection. Arithmetic freshness,
physical work, strict proof decoding and native refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude
open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Description Geometry)
open NativeGoldPcsWire (Query)
open NativeGoldBatchOpening (Opening)
open NativeGoldBatchBinding (Bound)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativePrefixCodec (Vector)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

inductive Error where
  | parameters | binding | proofShape
  deriving DecidableEq
inductive Outcome where
  | rejected (reason : Error) (parent : Transcript)
  | sampling (geometry : Geometry) (bound : Bound) (field : NativeFieldVector.Status)

def randomLabel : InputIndexedOracle.Input := NativeTranscript.utf8 "mw batch random linear test"
def sample (geometry : Geometry) (fuel : ℕ) (parent : Transcript) : Program NativeFieldVector.Status :=
  NativePrimeRequest.request NativeFields.goldilocksModulus fuel parent .vector randomLabel geometry.randomCount

/-- Native bind_many precedes opening-shape checks and the single shared random matrix. -/
def protocol {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) : Program Outcome :=
  match NativeBrakedownParameters.build description parameters with
  | none => .pure (.rejected .parameters parent)
  | some geometry => bind (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) (fun bound => match bound with
    | none => .pure (.rejected .binding parent)
    | some bound => if NativeGoldBatchOpening.check geometry parameters.queries
        (NativeGoldQueryGroups.groupCount parameters.leftVariables.val bound.queries) opening then
        bind (sample geometry fuel bound.parent) (fun field => .pure (.sampling geometry bound field))
      else .pure (.rejected .proofShape bound.parent))

theorem run_protocol {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol description parameters parent root queries values opening fuel) world).run =
      match NativeBrakedownParameters.build description parameters with
      | none => (.rejected .parameters parent,[])
      | some geometry =>
        let bound := (run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run
        match bound.1 with
        | none => (.rejected .binding parent,bound.2)
        | some binding => if NativeGoldBatchOpening.check geometry parameters.queries
            (NativeGoldQueryGroups.groupCount parameters.leftVariables.val binding.queries) opening then
            let field := (run (sample geometry fuel binding.parent) world).run
            (.sampling geometry binding field.1,bound.2 ++ field.2)
          else (.rejected .proofShape binding.parent,bound.2) := by
  cases constructed : NativeBrakedownParameters.build description parameters with
  | none => simp only [protocol,constructed,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | some geometry =>
    simp only [protocol,constructed,OracleProgram.run_bind,ObservationReplay.run_bind]
    cases (run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run.1 with
    | none => simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
    | some bound =>
      dsimp only
      split <;> simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem sampling_origin {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (bound : Bound) (field : NativeFieldVector.Status)
    (executed : (run (protocol description parameters parent root queries values opening fuel) world).run.1 = .sampling geometry bound field) :
    NativeBrakedownParameters.build description parameters = some geometry ∧
      (run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run.1 = some bound ∧
      NativeGoldBatchOpening.check geometry parameters.queries (NativeGoldQueryGroups.groupCount parameters.leftVariables.val bound.queries) opening = true ∧
      (run (sample geometry fuel bound.parent) world).run.1 = field := by
  rw [run_protocol] at executed
  cases constructed : NativeBrakedownParameters.build description parameters with
  | none => simp only [constructed] at executed; contradiction
  | some actual =>
    simp only [constructed] at executed
    cases read : (run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run.1 with
    | none => simp only [read] at executed; contradiction
    | some binding =>
      simp only [read] at executed
      split at executed
      next shape =>
        obtain ⟨rfl,rfl,same⟩ := Outcome.sampling.inj executed
        exact ⟨rfl,rfl,shape,same⟩
      next rejected => contradiction

theorem sampling_log {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (bound : Bound) (field : NativeFieldVector.Status)
    (executed : (run (protocol description parameters parent root queries values opening fuel) world).run.1 = .sampling geometry bound field) :
    (run (protocol description parameters parent root queries values opening fuel) world).run.2 =
      (run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run.2 ++
        (run (sample geometry fuel bound.parent) world).run.2 := by
  obtain ⟨constructed,binding,shape,_⟩ := sampling_origin description parameters parent root queries values opening fuel world geometry bound field executed
  rw [run_protocol]
  simp only [constructed,binding,ite_eq_left shape]

theorem finished_values {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (bound : Bound) (state : NativeFieldVector.State) (next : Transcript)
    (executed : (run (protocol description parameters parent root queries values opening fuel) world).run.1 = .sampling geometry bound (.finished state next)) :
    state.values.length = geometry.rows*parameters.width.val ∧
      ∀ value ∈ state.values, (NativePrimeRequest.goldWord value).val = value ∧ value < NativeFields.goldilocksModulus := by
  obtain ⟨constructed,_,_,sampled⟩ := sampling_origin description parameters parent root queries values opening fuel world geometry bound (.finished state next) executed
  have fields := NativePrimeRequest.finished_gold_exact fuel bound.parent .vector randomLabel geometry.randomCount world state next sampled
  have sizes := NativeBrakedownParameters.computed_sizes description parameters geometry constructed
  refine ⟨fields.1.trans sizes.2.2.2.2.2.2.2.2,?_⟩
  intro value member
  have known := fields.2 value member
  exact ⟨known.1,by rw [← known.1]; exact known.2⟩

/-- Malformed proof shape retains the already-bound parent and context observations. -/
theorem proofShape_rejected {C : Type} (description : Description C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (bound : Bound) (constructed : NativeBrakedownParameters.build description parameters = some geometry)
    (binding : (run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run.1 = some bound)
    (invalid : NativeGoldBatchOpening.check geometry parameters.queries (NativeGoldQueryGroups.groupCount parameters.leftVariables.val bound.queries) opening ≠ true) :
    (run (protocol description parameters parent root queries values opening fuel) world).run =
      (.rejected .proofShape bound.parent,(run (NativeGoldBatchBinding.protocol description.row parameters parent root queries values) world).run.2) := by
  rw [run_protocol]
  simp only [constructed,binding,ite_eq_right invalid]
end FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude
