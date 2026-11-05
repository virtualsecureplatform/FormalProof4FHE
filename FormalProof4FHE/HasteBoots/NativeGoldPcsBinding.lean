module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsWire
public import FormalProof4FHE.HasteBoots.NativeBrakedownContext

@[expose] public section

/-! Native bind checks precede context computation. Context hashing and both
binding messages use the same trusted parameter object and original raw query
and values; the digest is computed rather than supplied as a certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsBinding

open NativeBrakedownContext (RowDescription Parameters)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript utf8)
open OracleProgram (Program bind run)
open InputIndexedOracle (World)

def check {C : Type} (parameters : Parameters C) (query : Query) (values : Row) : Bool :=
  decide (query.val.length = parameters.numVariables.val) && decide (values.val.length = parameters.width.val) &&
    query.val.all (fun pair => NativeGoldMatrix.validate pair.1.model parameters.width.val && NativeGoldMatrix.validate pair.2.model parameters.width.val)

def appendBound (transcript : Transcript) (context root : Digest) (query : Query) (values : Row) : Transcript :=
  NativeTranscript.appendBytes
    (NativeTranscript.appendBytes transcript (utf8 "mw brakedown row-code v2") (List.ofFn context))
    (utf8 "mw commitment and query") (NativeGoldPcsWire.opening root query values)

def protocol {C : Type} (row : RowDescription C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) : Program (Option Transcript) :=
  if check parameters query values then
    bind (NativeBrakedownContext.context row parameters) (fun context => match context with
      | none => .pure none
      | some context => .pure (some (appendBound transcript context root query values)))
  else .pure none

theorem check_iff {C : Type} (parameters : Parameters C) (query : Query) (values : Row) : check parameters query values = true ↔
    query.val.length = parameters.numVariables.val ∧ values.val.length = parameters.width.val ∧
      ∀ pair ∈ query.val, NativeGoldMatrix.validate pair.1.model parameters.width.val = true ∧
        NativeGoldMatrix.validate pair.2.model parameters.width.val = true := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc]

/-- A packed coefficient query is checked against the actual raw matrices. -/
theorem coefficients_check {C : Type} (parameters : Parameters C) (point : List NativeFieldWire.GoldExtension)
    (query : Query) (values : Row) (shape : NativeGoldProjection.dimensions parameters.width.val = true)
    (count : query.val.length = parameters.numVariables.val)
    (model : query.models = (NativeGoldCoefficientsQuery.built parameters.width.val point).pairs)
    (size : values.val.length = parameters.width.val) : check parameters query values = true := by
  apply (check_iff parameters query values).mpr
  refine ⟨count,size,?_⟩
  intro pair member
  have represented : NativeGoldPcsWire.pairModel pair ∈ (NativeGoldCoefficientsQuery.built parameters.width.val point).pairs := by
    rw [← model]
    exact List.mem_map.mpr ⟨pair,member,rfl⟩
  obtain ⟨value,_,same⟩ := List.mem_map.mp represented
  change NativeGoldMatrix.validate (NativeGoldPcsWire.pairModel pair).zero parameters.width.val = true ∧
    NativeGoldMatrix.validate (NativeGoldPcsWire.pairModel pair).one parameters.width.val = true
  rw [← same]
  exact ⟨NativeGoldMultiplicationMatrix.matrix_valid _ _ shape,NativeGoldMultiplicationMatrix.matrix_valid _ _ shape⟩

theorem appendBound_input (transcript : Transcript) (context root : Digest) (query : Query) (values : Row) :
    (appendBound transcript context root query values).input = transcript.input ++ TranscriptFrame.encodeMany
      [⟨1,utf8 "mw brakedown row-code v2",List.ofFn context⟩,
       ⟨1,utf8 "mw commitment and query",NativeGoldPcsWire.opening root query values⟩] := by
  simp only [appendBound,NativeTranscript.appendBytes,NativeTranscript.absorb,TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]

theorem rejected {C : Type} (row : RowDescription C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (world : World) (invalid : check parameters query values ≠ true) :
    (run (protocol row parameters transcript root query values) world).run = (none,[]) := by
  simp only [protocol,ite_eq_right invalid,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem serialization_failure {C : Type} (row : RowDescription C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (world : World) (valid : check parameters query values = true)
    (invalid : NativeBrakedownContext.input row parameters = none) :
    (run (protocol row parameters transcript root query values) world).run = (none,[]) := by
  simp only [protocol,ite_eq_left valid,OracleProgram.run_bind,ObservationReplay.run_bind,
    NativeBrakedownContext.context_failure row parameters invalid world,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem accepted {C : Type} (row : RowDescription C) (parameters : Parameters C) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (world : World) (valid : check parameters query values = true)
    (bytes : InputIndexedOracle.Input) (serialized : NativeBrakedownContext.input row parameters = some bytes) :
    (run (protocol row parameters transcript root query values) world).run =
      (some (appendBound transcript (InputIndexedOracle.sha512 world bytes) root query values),
        [.hash bytes (List.ofFn (InputIndexedOracle.sha512 world bytes))]) := by
  simp only [protocol,ite_eq_left valid,OracleProgram.run_bind,ObservationReplay.run_bind,
    NativeBrakedownContext.context_success row parameters bytes serialized world,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

end FormalProof4FHE.HasteBoots.NativeGoldPcsBinding
