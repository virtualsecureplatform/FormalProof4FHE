module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsOpening
public import FormalProof4FHE.HasteBoots.NativeGoldPcsBinding
public import FormalProof4FHE.HasteBoots.NativePrimeRequest

@[expose] public section

/-! Checked parameter initialization followed by the actual single-opening
shape/binding/random-test prefix. No constructed geometry, bound transcript
or challenge certificate is supplied. This prefix is not PCS acceptance. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude

open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Description Geometry)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

inductive Error where
  | parameters | proofShape | binding
  deriving DecidableEq

inductive Outcome where
  | rejected (reason : Error)
  | sampling (geometry : Geometry) (field : NativeFieldVector.Status)

def randomLabel : InputIndexedOracle.Input := NativeTranscript.utf8 "mw random linear test"

def sample (geometry : Geometry) (fuel : ℕ) (transcript : Transcript) : Program NativeFieldVector.Status :=
  NativePrimeRequest.request NativeFields.goldilocksModulus fuel transcript .vector randomLabel geometry.randomCount

def protocol {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) : Program Outcome :=
  match NativeBrakedownParameters.build description parameters with
  | none => .pure (.rejected .parameters)
  | some geometry =>
    if NativeGoldPcsOpening.check geometry parameters.queries opening then
      bind (NativeGoldPcsBinding.protocol description.row parameters transcript root query values) (fun bound =>
        match bound with
        | none => .pure (.rejected .binding)
        | some bound => bind (sample geometry fuel bound) (fun field => .pure (.sampling geometry field)))
    else .pure (.rejected .proofShape)

theorem run_protocol {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol description parameters transcript root query values opening fuel) world).run =
      match NativeBrakedownParameters.build description parameters with
      | none => (.rejected .parameters,[])
      | some geometry =>
        if NativeGoldPcsOpening.check geometry parameters.queries opening then
          let bound := (run (NativeGoldPcsBinding.protocol description.row parameters transcript root query values) world).run
          match bound.1 with
          | none => (.rejected .binding,bound.2)
          | some boundTranscript =>
            let field := (run (sample geometry fuel boundTranscript) world).run
            (.sampling geometry field.1,bound.2 ++ field.2)
        else (.rejected .proofShape,[]) := by
  cases constructed : NativeBrakedownParameters.build description parameters with
  | none => simp only [protocol,constructed,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | some geometry =>
    by_cases shape : NativeGoldPcsOpening.check geometry parameters.queries opening = true
    · simp only [protocol,constructed,ite_eq_left shape,OracleProgram.run_bind,ObservationReplay.run_bind]
      cases (run (NativeGoldPcsBinding.protocol description.row parameters transcript root query values) world).run.1 <;>
        simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,OracleProgram.run_bind,ObservationReplay.run_bind,List.append_nil]
    · simp only [protocol,constructed,ite_eq_right shape,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem sampling_origin {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (field : NativeFieldVector.Status)
    (success : (run (protocol description parameters transcript root query values opening fuel) world).run.1 = .sampling geometry field) :
    NativeBrakedownParameters.build description parameters = some geometry ∧
      NativeGoldPcsOpening.check geometry parameters.queries opening = true ∧
      ∃ bound, (run (NativeGoldPcsBinding.protocol description.row parameters transcript root query values) world).run.1 = some bound ∧
        (run (sample geometry fuel bound) world).run.1 = field := by
  rw [run_protocol] at success
  cases constructed : NativeBrakedownParameters.build description parameters with
  | none => simp only [constructed] at success; contradiction
  | some actual =>
    simp only [constructed] at success
    by_cases shape : NativeGoldPcsOpening.check actual parameters.queries opening = true
    · rw [ite_eq_left shape] at success
      cases boundRead : (run (NativeGoldPcsBinding.protocol description.row parameters transcript root query values) world).run.1 with
      | none => simp only [boundRead] at success; contradiction
      | some bound =>
        simp only [boundRead] at success
        obtain ⟨rfl,same⟩ := Outcome.sampling.inj success
        exact ⟨rfl,shape,bound,rfl,same⟩
    · rw [ite_eq_right shape] at success; contradiction

/-- Every completed random test is canonical and has the constructor's
computed matrix size, even after arbitrary candidate rejection. -/
theorem finished_values {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (next : Transcript)
    (success : (run (protocol description parameters transcript root query values opening fuel) world).run.1 = .sampling geometry (.finished state next)) :
    state.values.length = geometry.rows*parameters.width.val ∧
      ∀ value ∈ state.values, (NativePrimeRequest.goldWord value).val = value ∧ value < NativeFields.goldilocksModulus := by
  obtain ⟨constructed,_,bound,_,sampled⟩ := sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) success
  have fields := NativePrimeRequest.finished_gold_exact fuel bound .vector randomLabel geometry.randomCount world state next sampled
  have sizes := NativeBrakedownParameters.computed_sizes description parameters geometry constructed
  refine ⟨fields.1.trans sizes.2.2.2.2.2.2.2.2,?_⟩
  intro value member
  have known := fields.2 value member
  exact ⟨known.1,by rw [← known.1]; exact known.2⟩

theorem proofShape_rejected {C : Type} (description : Description C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (geometry : Geometry)
    (constructed : NativeBrakedownParameters.build description parameters = some geometry)
    (invalid : NativeGoldPcsOpening.check geometry parameters.queries opening ≠ true) :
    (run (protocol description parameters transcript root query values opening fuel) world).run = (.rejected .proofShape,[]) := by
  rw [run_protocol]
  simp only [constructed,ite_eq_right invalid]

end FormalProof4FHE.HasteBoots.NativeGoldPcsPrelude
