module
public import FormalProof4FHE.HasteBoots.NativeGoldEncodedParameters
@[expose] public section

/-! new_encoded consumes the actual completed code object. Pending constructor
states have no parameter result; this is a phase observation, not a new native
validation gate. Success derives code identity, message association, parameter
geometry and the backend root from execution receipts. Rust/source/heap and
physical refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldParameterInitialization
open NativeGoldBlockCodeProgram (Request Config Completed)
open NativeGoldEncodedParameters (Header Initialized)

def finish (header : Header) (config : Config) : Option (Except NativeGoldEncodedParameters.Error Initialized) :=
  match config.phase with
  | .done result => some (NativeGoldEncodedParameters.build header result.code)
  | _ => none

theorem finish_origin (header : Header) (config : Config) (initialized : Initialized)
    (executed : finish header config = some (.ok initialized)) :
    ∃ result : Completed, config.phase = .done result ∧
      NativeGoldEncodedParameters.build header result.code = .ok initialized := by
  unfold finish at executed
  split at executed
  · rename_i result finished
    exact ⟨result,finished,Option.some.inj executed⟩
  · cases executed

theorem code_origin (header : Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : Initialized)
    (executed : finish header config = some (.ok initialized)) :
    ∃ result : Completed, config.phase = .done result ∧ initialized.parameters.code = result.code ∧
      NativeGoldBlockCodeProgram.LayoutReady request result.layout ∧
      ConcreteNTTGoldTable.newTable (NativeGoldBlockCodeLayout.logSize result.layout) = .created result.loaded := by
  obtain ⟨result,finished,built⟩ := finish_origin header config initialized executed
  have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
  exact ⟨result,finished,NativeGoldEncodedParameters.retained_code header result.code initialized built,origin.2.1,origin.2.2.1⟩

theorem parameter_geometry (header : Header) (config : Config) (initialized : Initialized)
    (executed : finish header config = some (.ok initialized)) :
    NativeBrakedownParameters.build NativeGoldBlockCode.description initialized.parameters = some initialized.geometry := by
  obtain ⟨result,_,built⟩ := finish_origin header config initialized executed
  exact NativeGoldEncodedParameters.legacy_build header result.code initialized built

theorem message_association (header : Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : Initialized)
    (executed : finish header config = some (.ok initialized)) :
    request.message.val = 2^(initialized.parameters.numVariables.val-initialized.parameters.leftVariables.val) := by
  obtain ⟨result,finished,built⟩ := finish_origin header config initialized executed
  have codeSpec := NativeGoldBlockCode.build_spec _ request.message request.block request.blowup result.code
    (NativeGoldBlockCodeBackend.completed_build request config reachable result finished)
  have associated := NativeGoldEncodedParameters.message_matches header result.code initialized built
  rw [codeSpec.messageEq] at associated
  exact associated

theorem code_primitive (header : Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : Initialized)
    (executed : finish header config = some (.ok initialized)) :
    IsPrimitiveRoot (NativeFieldRepresentation.goldValue initialized.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize initialized.parameters.code+1)) := by
  obtain ⟨result,finished,built⟩ := finish_origin header config initialized executed
  rw [NativeGoldEncodedParameters.retained_code header result.code initialized built]
  exact NativeGoldBlockCodeBackend.completed_primitive request config reachable result finished

theorem encoding_available (header : Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : Initialized)
    (executed : finish header config = some (.ok initialized)) :
    ∃ root : NativeGoldSolinas.Word,
      (NativeGoldBlockCodeBackend.observations config.cache (NativeGoldBlockCodeProgram.reachable_good request config reachable).1).load
        (NativeGoldBlockCode.logSize initialized.parameters.code) = some root ∧
      NativeGoldRowEncoding.check (NativeGoldBlockCode.encoding initialized.parameters.code root) = true ∧
      root.val = initialized.parameters.code.domainRoot.val := by
  obtain ⟨result,finished,built⟩ := finish_origin header config initialized executed
  have retained := NativeGoldEncodedParameters.retained_code header result.code initialized built
  let root := NativeGoldBlockCodeBackend.planRoot request config reachable result finished
  refine ⟨root,?_,?_,?_⟩
  · rw [retained]
    exact NativeGoldBlockCodeBackend.completed_loaded request config reachable result finished
  · rw [retained]
    exact NativeGoldBlockCodeBackend.completed_encoding_check request config reachable result finished
  · rw [retained,NativeGoldBlockCodeBackend.planRoot_value]
    have origin := NativeGoldBlockCodeProgram.completed_origin request config reachable result finished
    rw [origin.2.2.2.2]
    rfl

end FormalProof4FHE.HasteBoots.NativeGoldParameterInitialization
