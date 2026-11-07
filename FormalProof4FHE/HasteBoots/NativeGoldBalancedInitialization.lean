module
public import FormalProof4FHE.HasteBoots.NativeGoldBalancedLayout
public import FormalProof4FHE.HasteBoots.NativeGoldParameterStore
@[expose] public section

/-! Source handoff from the selected balanced layout to the actual code request
and new_encoded header. Neither a code object nor a code-validity callback is
an input. Constructor scheduling and initialization still use their explicit
receipts; source/heap and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBalancedInitialization
open NativeGoldBalancedLayout (Request Candidate Error)

structure Prepared where
  selected : Candidate
  codeRequest : NativeGoldBlockCodeProgram.Request
  header : NativeGoldEncodedParameters.Header
  deriving DecidableEq

def launch (request : Request) (selected : Candidate) : Prepared :=
  ⟨selected,⟨Fin.ofNat (2^64) selected.columns,request.width,request.blowup⟩,
    ⟨request.numVariables,request.width,Fin.ofNat (2^64) selected.left,request.queries⟩⟩

def prepare (request : Request) : Except Error Prepared :=
  (NativeGoldBalancedLayout.select request).map (launch request)

theorem prepare_origin (request : Request) (prepared : Prepared)
    (executed : prepare request = .ok prepared) :
    NativeGoldBalancedLayout.select request = .ok prepared.selected ∧ prepared = launch request prepared.selected := by
  unfold prepare at executed
  cases selected : NativeGoldBalancedLayout.select request with
  | error error => simp only [selected] at executed; cases executed
  | ok chosen =>
    simp only [selected] at executed
    cases executed
    exact ⟨rfl,rfl⟩

theorem prepare_words (request : Request) (prepared : Prepared)
    (executed : prepare request = .ok prepared) :
    prepared.codeRequest.message.val = prepared.selected.columns ∧
    prepared.header.leftVariables.val = prepared.selected.left ∧
    prepared.codeRequest.block = request.width ∧ prepared.codeRequest.blowup = request.blowup ∧
    prepared.header.numVariables = request.numVariables ∧ prepared.header.width = request.width ∧
    prepared.header.queries = request.queries := by
  obtain ⟨selected,same⟩ := prepare_origin request prepared executed
  have shape := NativeGoldBalancedLayout.selected_shape request prepared.selected selected
  have dims := NativeGoldBalancedLayout.selected_dimensions request prepared.selected selected
  have leftSmall : prepared.selected.left < 2^64 := by omega
  have exponent : request.numVariables.val-prepared.selected.left < 64 := by omega
  have columnsSmall : prepared.selected.columns < 2^64 := by
    rw [shape.2.1]
    exact Nat.pow_lt_pow_right (by decide) exponent
  rw [same]
  simpa [launch] using And.intro columnsSmall leftSmall

theorem initialized_meaning (request : Request) (prepared : Prepared)
    (executed : prepare request = .ok prepared) (config : NativeGoldBlockCodeProgram.Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable prepared.codeRequest config)
    (initialized : NativeGoldEncodedParameters.Initialized)
    (finished : NativeGoldParameterInitialization.finish prepared.header config = some (.ok initialized)) :
    initialized.parameters.numVariables = request.numVariables ∧ initialized.parameters.width = request.width ∧
    initialized.parameters.leftVariables.val = prepared.selected.left ∧ initialized.parameters.queries = request.queries ∧
    initialized.parameters.code.messageLength.val = prepared.selected.columns ∧
    IsPrimitiveRoot (NativeFieldRepresentation.goldValue initialized.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize initialized.parameters.code+1)) ∧
    NativeBrakedownParameters.build NativeGoldBlockCode.description initialized.parameters = some initialized.geometry := by
  have words := prepare_words request prepared executed
  obtain ⟨result,phase,built⟩ := NativeGoldParameterInitialization.finish_origin prepared.header config initialized finished
  have fields := NativeGoldEncodedParameters.header_fields prepared.header result.code initialized built
  have retained := NativeGoldEncodedParameters.retained_code prepared.header result.code initialized built
  have codeSpec := NativeGoldBlockCode.build_spec _ prepared.codeRequest.message prepared.codeRequest.block prepared.codeRequest.blowup result.code
    (NativeGoldBlockCodeBackend.completed_build prepared.codeRequest config reachable result phase)
  refine ⟨fields.1.trans words.2.2.2.2.1,fields.2.1.trans words.2.2.2.2.2.1,?_,
    fields.2.2.2.trans words.2.2.2.2.2.2,?_,?_,?_⟩
  · rw [fields.2.2.1]; exact words.2.1
  · rw [retained,codeSpec.messageEq]; exact words.1
  · exact NativeGoldParameterInitialization.code_primitive prepared.header prepared.codeRequest config reachable initialized finished
  · exact NativeGoldParameterInitialization.parameter_geometry prepared.header config initialized finished

theorem initialized_code_shape (request : Request) (prepared : Prepared)
    (executed : prepare request = .ok prepared) (config : NativeGoldBlockCodeProgram.Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable prepared.codeRequest config)
    (initialized : NativeGoldEncodedParameters.Initialized)
    (finished : NativeGoldParameterInitialization.finish prepared.header config = some (.ok initialized)) :
    initialized.parameters.code.blockWidth = request.width ∧
    initialized.parameters.code.blocks.val = prepared.selected.blocks ∧
    initialized.parameters.code.messageBlocks.val =
      NativeGoldBlockCode.paddedBlocks prepared.selected.columns request.width.val ∧
    initialized.parameters.code.modulus = NativeBrakedownContext.modulus := by
  have words := prepare_words request prepared executed
  have selected := (prepare_origin request prepared executed).1
  have shape := NativeGoldBalancedLayout.selected_shape request prepared.selected selected
  obtain ⟨result,phase,built⟩ := NativeGoldParameterInitialization.finish_origin prepared.header config initialized finished
  have retained := NativeGoldEncodedParameters.retained_code prepared.header result.code initialized built
  have codeSpec := NativeGoldBlockCode.build_spec _ prepared.codeRequest.message prepared.codeRequest.block prepared.codeRequest.blowup result.code
    (NativeGoldBlockCodeBackend.completed_build prepared.codeRequest config reachable result phase)
  rw [retained]
  refine ⟨codeSpec.blockEq.trans words.2.2.1,?_,?_,codeSpec.modulus⟩
  · rw [codeSpec.count,words.1,words.2.2.1,words.2.2.2.1]
    exact shape.2.2.1.symm
  · rw [codeSpec.padded,words.1,words.2.2.1]

end FormalProof4FHE.HasteBoots.NativeGoldBalancedInitialization
