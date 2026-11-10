module
public import FormalProof4FHE.HasteBoots.LookupPCSCodeCapacity
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeBackend
public import FormalProof4FHE.HasteBoots.SymbolLift
@[expose] public section

/-! Cache-backed completed construction derives the actual RS domain, response
code membership and distance. Primitive roots and encoder certificates are not
caller premises. Whole native verifier/byte and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.LookupPCSBackendCode
open NativeGoldBlockCodeProgram (Request Config Completed)
open NativeGoldBlockCode (Stored description)
open NativeFields (Goldilocks)
open NativeUsizeMessage (Usize)
noncomputable section

/-- The actual original constructor's bit-reversed odd-root evaluation domain. -/
def domain (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    Fin (2 ^ NativeGoldBlockCode.logSize result.code) ↪ Goldilocks :=
  NTTButterfly.domain (NativeGoldBlockCode.logSize result.code) (NativeFieldRepresentation.goldValue result.code.domainRoot)
    (NativeGoldBlockCodeBackend.completed_primitive request config reachable result finished)

/-- Exact native domain cardinality, from completed code construction. -/
theorem domain_size (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    Fintype.card (Fin (2 ^ NativeGoldBlockCode.logSize result.code)) = result.code.blocks.val := by
  have built := NativeGoldBlockCodeBackend.completed_build request config reachable result finished
  simpa only [Fintype.card_fin] using (NativeGoldBlockCodeMeaning.constructor_log _ request.message request.block request.blowup result.code built).2.symm

/-- Original parameter capacity comes from that same completed cache-backed
constructor, with only the actual retained code identity and parameter result. -/
theorem parameter_spec (message blowup : Usize) (parameters : NativeBrakedownContext.Parameters Stored)
    (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable ⟨message,parameters.width,blowup⟩ config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = parameters.code)
    (geometry : NativeBrakedownParameters.Geometry)
    (built : NativeBrakedownParameters.build description parameters = some geometry) :
    LookupPCSCodeCapacity.Spec parameters geometry := by
  have code := NativeGoldBlockCodeBackend.completed_build ⟨message,parameters.width,blowup⟩ config reachable result finished
  rw [retained] at code
  exact LookupPCSCodeCapacity.code_spec _ message blowup parameters code geometry built

variable {L : Type} [Field L] [Algebra Goldilocks L]

/-- Each actual encoded response lane, assembled using its physical block
width, lies in exactly the scalar RS alphabet used by the PCS analysis. -/
theorem lifted_response (request : Request) (config : Config) (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result)
    (basis : Module.Basis (Fin result.code.blockWidth.val) Goldilocks L) (width : ℕ)
    (input output : List NativeFieldRepresentation.GoldWord)
    (encoded : NativeGoldRowEncoding.encodeResponses (NativeGoldBlockCode.encoding result.code
      (NativeGoldBlockCodeBackend.planRoot request config reachable result finished)) width input = some output) :
    ∀ lane < width,
      SymbolLift.packWord basis (NativeGoldResponseMeaning.laneWord (NativeGoldBlockCode.encoding result.code
        (NativeGoldBlockCodeBackend.planRoot request config reachable result finished)) output lane) ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain request config reachable result finished))
        result.code.messageBlocks.val := by
  intro lane bound
  have exactEncoding := (NativeGoldBlockCodeBackend.completed_response_lanes request config reachable result finished
    width input output encoded lane bound).1
  rw [exactEncoding]
  exact SymbolLift.encode_mem_scalarCode basis (domain request config reachable result finished) _

/-- The analysis-field minimum distance is derived from the original native
code's degree and domain. It is independent of the lookup extension degree. -/
theorem lifted_minDist [DecidableEq L] (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : Completed) (finished : config.phase = .done result) :
    Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain request config reachable result finished))
      result.code.messageBlocks.val : Set (Fin (2 ^ NativeGoldBlockCode.logSize result.code) → L)) =
      result.code.blocks.val - result.code.messageBlocks.val + 1 := by
  have built := NativeGoldBlockCodeBackend.completed_build request config reachable result finished
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions _ request.message request.block request.blowup result.code built
  let : NeZero result.code.messageBlocks.val := ⟨Nat.ne_of_gt dimensions.1⟩
  have enough : result.code.messageBlocks.val ≤ Fintype.card (Fin (2 ^ NativeGoldBlockCode.logSize result.code)) := by
    simpa only [Fintype.card_fin] using Nat.le_of_lt dimensions.2.1
  have distance := ReedSolomon.minDist_of_le
    (α := SymbolLift.liftedDomain (K := L) (domain request config reachable result finished)) enough
  simpa only [domain_size request config reachable result finished] using distance

/-- The distance needed by original-root PCS is expressed in the actual native
parameter constructor's tree height and its retained message-block degree. -/
theorem parameter_minDist [DecidableEq L] (message blowup : Usize)
    (parameters : NativeBrakedownContext.Parameters Stored) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable ⟨message,parameters.width,blowup⟩ config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = parameters.code)
    (geometry : NativeBrakedownParameters.Geometry)
    (built : NativeBrakedownParameters.build description parameters = some geometry) :
    Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L)
      (domain ⟨message,parameters.width,blowup⟩ config reachable result finished)) result.code.messageBlocks.val :
      Set (Fin (2 ^ NativeGoldBlockCode.logSize result.code) → L)) =
      2 ^ geometry.height - parameters.code.messageBlocks.val + 1 := by
  have spec := parameter_spec message blowup parameters config reachable result finished retained geometry built
  have blocks : result.code.blocks.val = 2 ^ geometry.height := by
    rw [spec.height,← retained]
    simpa only [Fintype.card_fin] using (domain_size ⟨message,parameters.width,blowup⟩ config reachable result finished).symm
  exact (lifted_minDist ⟨message,parameters.width,blowup⟩ config reachable result finished).trans
    (by rw [blocks,retained])

end
end FormalProof4FHE.HasteBoots.LookupPCSBackendCode
