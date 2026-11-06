module

public import FormalProof4FHE.HasteBoots.NativeGoldQueryGroups
public import FormalProof4FHE.HasteBoots.NativeGoldPcsBinding
@[expose] public section

/-! The native bind_many prefix with checked nonempty point/value counts,
query/value/matrix dimensions and original raw batch serialization. The same
actual context hash and checked queries determine subsequent response groups.
This is the binding prefix, not batch response/column verification or security;
strict proof decoding, native code refinement and composition remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchBinding
open NativePrefixCodec (Vector)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeBrakedownContext (Parameters RowDescription)
open NativeTranscript (Transcript utf8)
open InputIndexedOracle (Input World)
open OracleProgram (Program bind run)

def check {C : Type} (parameters : Parameters C) (queries : Vector Query) (values : Vector Row) : Bool :=
  !queries.val.isEmpty && decide (queries.val.length = values.val.length) &&
    (queries.val.zip values.val).all (fun pair => NativeGoldPcsBinding.check parameters pair.1 pair.2)

def queriesCodec := NativePrefixCodec.vector NativeGoldPcsWire.queryCodec
def valuesCodec := NativePrefixCodec.vector NativeLookupRequestWire.rowCodec

def payload (context root : Digest) (queries : Vector Query) (values : Vector Row) : Input :=
  List.ofFn context ++ List.ofFn root ++ queriesCodec.encode queries ++ valuesCodec.encode values

def appendBound (parent : Transcript) (context root : Digest) (queries : Vector Query) (values : Vector Row) : Transcript :=
  NativeTranscript.appendBytes parent (utf8 "mw batched row-code v1") (payload context root queries values)

structure Bound where
  parent : Transcript
  queries : Vector Query
  values : Vector Row

/-- Original native bind_many, retaining the caller-derived queries used for response grouping. -/
def protocol {C : Type} (row : RowDescription C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) : Program (Option Bound) :=
  if check parameters queries values then
    bind (NativeBrakedownContext.context row parameters) (fun context => match context with
      | none => .pure none
      | some context => .pure (some ⟨appendBound parent context root queries values,queries,values⟩))
  else .pure none

theorem check_iff {C : Type} (parameters : Parameters C) (queries : Vector Query) (values : Vector Row) :
    check parameters queries values = true ↔ queries.val ≠ [] ∧ queries.val.length = values.val.length ∧
      List.Forall₂ (fun query value => NativeGoldPcsBinding.check parameters query value = true) queries.val values.val := by
  have nonempty_iff : (!queries.val.isEmpty) = true ↔ queries.val ≠ [] := by
    cases queries.val <;> simp
  simp only [check,Bool.and_eq_true,nonempty_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨nonempty,count⟩,valid⟩
    refine ⟨nonempty,count,List.forall₂_iff_zip.mpr ⟨count,?_⟩⟩
    intro query value member
    exact (List.all_eq_true.mp valid) (query,value) member
  · rintro ⟨nonempty,count,valid⟩
    refine ⟨⟨nonempty,count⟩,List.all_eq_true.mpr ?_⟩
    intro pair member
    exact List.forall₂_zip valid member

theorem rejected {C : Type} (row : RowDescription C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (world : World)
    (invalid : check parameters queries values ≠ true) :
    (run (protocol row parameters parent root queries values) world).run = (none,[]) := by
  simp only [protocol,ite_eq_right invalid,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem serialization_failure {C : Type} (row : RowDescription C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (world : World)
    (valid : check parameters queries values = true) (invalid : NativeBrakedownContext.input row parameters = none) :
    (run (protocol row parameters parent root queries values) world).run = (none,[]) := by
  simp only [protocol,ite_eq_left valid,OracleProgram.run_bind,ObservationReplay.run_bind,
    NativeBrakedownContext.context_failure row parameters invalid world,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem accepted {C : Type} (row : RowDescription C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (world : World)
    (valid : check parameters queries values = true) (bytes : Input) (serialized : NativeBrakedownContext.input row parameters = some bytes) :
    (run (protocol row parameters parent root queries values) world).run =
      (some ⟨appendBound parent (InputIndexedOracle.sha512 world bytes) root queries values,queries,values⟩,
        [.hash bytes (List.ofFn (InputIndexedOracle.sha512 world bytes))]) := by
  simp only [protocol,ite_eq_left valid,OracleProgram.run_bind,ObservationReplay.run_bind,
    NativeBrakedownContext.context_success row parameters bytes serialized world,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem appendBound_input (parent : Transcript) (context root : Digest) (queries : Vector Query) (values : Vector Row) :
    (appendBound parent context root queries values).input = parent.input ++
      TranscriptFrame.encode ⟨1,utf8 "mw batched row-code v1",payload context root queries values⟩ := rfl

theorem bound_origin {C : Type} (row : RowDescription C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (world : World) (bound : Bound)
    (executed : (run (protocol row parameters parent root queries values) world).run.1 = some bound) :
    check parameters queries values = true ∧ ∃ digest,
      (run (NativeBrakedownContext.context row parameters) world).run.1 = some digest ∧
      bound = ⟨appendBound parent digest root queries values,queries,values⟩ ∧
      (run (protocol row parameters parent root queries values) world).run.2 =
        (run (NativeBrakedownContext.context row parameters) world).run.2 := by
  unfold protocol at executed ⊢
  split at executed
  next valid =>
    simp only [ite_eq_left valid,OracleProgram.run_bind,ObservationReplay.run_bind] at executed ⊢
    cases computed : (run (NativeBrakedownContext.context row parameters) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some digest =>
      simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed ⊢
      exact ⟨valid,digest,rfl,(Option.some.inj executed).symm,by simp only [List.append_nil]⟩
  next invalid => contradiction

/-- Grouping consumes the same checked raw queries, with every original claim retained. -/
theorem bound_groups {C : Type} (row : RowDescription C) (parameters : Parameters C) (parent : Transcript)
    (root : Digest) (queries : Vector Query) (values : Vector Row) (world : World) (bound : Bound)
    (executed : (run (protocol row parameters parent root queries values) world).run.1 = some bound) :
    bound.queries = queries ∧ bound.values = values ∧
      ∀ first second : Fin bound.queries.val.length,
        NativeGoldQueryGroups.group parameters.leftVariables.val bound.queries first = NativeGoldQueryGroups.group parameters.leftVariables.val bound.queries second ↔
        List.Forall₂ NativeGoldQueryGroups.PairEqual ((bound.queries.val.get first).val.take parameters.leftVariables.val)
          ((bound.queries.val.get second).val.take parameters.leftVariables.val) := by
  obtain ⟨_,digest,_,same,_⟩ := bound_origin row parameters parent root queries values world bound executed
  subst bound
  exact ⟨rfl,rfl,NativeGoldQueryGroups.group_eq_iff parameters.leftVariables.val queries⟩
end FormalProof4FHE.HasteBoots.NativeGoldBatchBinding
