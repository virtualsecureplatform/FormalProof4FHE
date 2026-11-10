module
public import FormalProof4FHE.HasteBoots.LookupPCSBackendCode
@[expose] public section

/-! The constructor-derived domain is indexed by the original parameter
object's actual tree height. Reindexing changes neither roots nor evaluation
points, and actual encoded responses retain their scalar RS membership. -/
namespace FormalProof4FHE.HasteBoots.LookupPCSParameterDomain
open NativeGoldBlockCodeProgram (Config Completed)
open NativeGoldBlockCode (Stored description)
open NativeFields (Goldilocks)
open NativeUsizeMessage (Usize)
noncomputable section
variable (message blowup : Usize) (parameters : NativeBrakedownContext.Parameters Stored) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable ⟨message,parameters.width,blowup⟩ config)
    (result : Completed) (finished : config.phase = .done result) (retained : result.code = parameters.code)
    (geometry : NativeBrakedownParameters.Geometry)
    (built : NativeBrakedownParameters.build description parameters = some geometry)

def positions : Fin (2 ^ geometry.height) ≃ Fin (2 ^ NativeGoldBlockCode.logSize result.code) :=
  finCongr (congrArg (fun n : ℕ => 2 ^ n)
    ((LookupPCSBackendCode.parameter_spec message blowup parameters config reachable result finished retained geometry built).height.trans
      (congrArg NativeGoldBlockCode.logSize retained.symm)))

def domain : Fin (2 ^ geometry.height) ↪ Goldilocks :=
  ⟨fun position => LookupPCSBackendCode.domain ⟨message,parameters.width,blowup⟩ config reachable result finished
    (positions (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built) position),
    (LookupPCSBackendCode.domain ⟨message,parameters.width,blowup⟩ config reachable result finished).injective.comp
      (positions (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built)).injective⟩

variable {L : Type} [Field L] [Algebra Goldilocks L]

/-- Original-height indexing gives the exact scalar-code distance needed by
PCS, without an independent domain or primitive-root premise. -/
theorem minDist [DecidableEq L] :
    Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L)
      (domain (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built))) parameters.code.messageBlocks.val :
      Set (Fin (2 ^ geometry.height) → L)) = 2 ^ geometry.height - parameters.code.messageBlocks.val + 1 := by
  have spec := LookupPCSBackendCode.parameter_spec message blowup parameters config reachable result finished retained geometry built
  let : NeZero parameters.code.messageBlocks.val := ⟨Nat.ne_of_gt spec.degreePositive⟩
  have enough : parameters.code.messageBlocks.val ≤ Fintype.card (Fin (2 ^ geometry.height)) := by
    simpa only [Fintype.card_fin] using spec.degreeLeaves
  simpa only [Fintype.card_fin] using ReedSolomon.minDist_of_le
    (α := SymbolLift.liftedDomain (K := L) (domain (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built))) enough

/-- Actual native response symbols keep the same code membership after the
unique index transport to the original parameter tree height. -/
theorem lifted_response (basis : Module.Basis (Fin result.code.blockWidth.val) Goldilocks L) (width : ℕ)
    (input output : List NativeFieldRepresentation.GoldWord)
    (encoded : NativeGoldRowEncoding.encodeResponses (NativeGoldBlockCode.encoding result.code
      (NativeGoldBlockCodeBackend.planRoot ⟨message,parameters.width,blowup⟩ config reachable result finished)) width input = some output) :
    ∀ lane < width,
      (fun position => SymbolLift.packWord basis (NativeGoldResponseMeaning.laneWord (NativeGoldBlockCode.encoding result.code
        (NativeGoldBlockCodeBackend.planRoot ⟨message,parameters.width,blowup⟩ config reachable result finished)) output lane)
          (positions (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built) position)) ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := L)
        (domain (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built))) result.code.messageBlocks.val := by
  intro lane bound
  have exactEncoding := (NativeGoldBlockCodeBackend.completed_response_lanes ⟨message,parameters.width,blowup⟩ config reachable result finished
    width input output encoded lane bound).1
  rw [exactEncoding]
  exact SymbolLift.encode_mem_scalarCode basis (domain (message := message) (blowup := blowup) (parameters := parameters) (config := config) (reachable := reachable) (result := result) (finished := finished) (retained := retained) (geometry := geometry) (built := built)) _

end
end FormalProof4FHE.HasteBoots.LookupPCSParameterDomain
