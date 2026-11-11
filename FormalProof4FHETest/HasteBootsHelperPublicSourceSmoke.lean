module
import all FormalProof4FHE.HasteBoots.AllocatedHelperContext
import all FormalProof4FHE.HasteBoots.HelperPublicOwnership
import all FormalProof4FHE.HasteBoots.HelperPublicSourceObligation
import all FormalProof4FHETest.HasteBootsConstructedTargetsSmoke
import all FormalProof4FHETest.HasteBootsCallerAvailabilitySmoke
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke

namespace FormalProof4FHE.HasteBoots.HelperPublicSourceSmoke
open HasteBootsBatchMeaningSmoke (usize root)
open NativeGoldParameterStore (Entry)
noncomputable section

def request (blowup : ℕ) : NativeGoldBlockCodeProgram.Request := ⟨usize 4,usize 3,usize blowup⟩
def header (queries : ℕ) : NativeGoldEncodedParameters.Header := ⟨usize 3,usize 4,usize 1,usize queries⟩
def allocate? (entries : List Entry) (blowup queries : ℕ) : Option (List Entry) :=
  match NativeGoldParameterStore.allocate entries (request blowup) (header queries)
      (HasteBootsConstructedTargetsSmoke.advance (request blowup) 6 {}) with
  | some (.ok result) => some result.entries
  | _ => none

def entries : Option (List Entry) := (allocate? [] 2 544).bind (fun first => allocate? first 4 600)

def executableTemplate (entry : Entry) : NativeGoldHelperVerification.Context Unit :=
  ⟨⟨fun _ => false,fun _ => false,fun _ => none⟩,⟨[],by decide⟩,entry.initialized.parameters,
    NativeTranscript.new [] (fun _ => 0),⟨[],by decide⟩,
    ⟨⟨⟨[],by decide⟩,by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,(),⟨[],by decide⟩⟩,
    18,18,18,18,6⟩

/-- info: true -/
#guard_msgs in
#eval match entries with
  | some [first,last] => decide (first.initialized.parameters.code = last.initialized.parameters.code) &&
      first.request.blowup.val == 2 && last.request.blowup.val == 4 &&
      first.initialized.parameters.width.val == 4 && first.initialized.parameters.code.blockWidth.val == 3
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match entries with
  | some (first::rest) =>
    match AllocatedHelperContext.borrow (first::rest) 0 (executableTemplate first),
        AllocatedHelperContext.borrow (first::rest) 1 (executableTemplate first) with
    | some first,some last => first.helper.queries.val == 544 && last.helper.queries.val == 600 &&
        first.fieldFuel == 18 && last.workerFuel == 6
    | _,_ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match entries with
  | some (first::rest) => (AllocatedHelperContext.borrow (first::rest) 2 (executableTemplate first)).isNone &&
      (NativeGoldParameterStore.allocate [] (request 2) (header 544) {}).isNone
  | _ => false

/-- Borrowing reads only the selected helper object; the original template's
registry, requests, parent, proof and verifier fuel remain original data. -/
example (entry : Entry) : (AllocatedHelperContext.borrow [entry] 0 HasteBootsCallerAvailabilitySmoke.ctx).map
      (fun ctx => (ctx.registry,ctx.requests,ctx.parent,ctx.proof,ctx.fieldFuel)) =
    some (HasteBootsCallerAvailabilitySmoke.ctx.registry,HasteBootsCallerAvailabilitySmoke.ctx.requests,
      HasteBootsCallerAvailabilitySmoke.ctx.parent,HasteBootsCallerAvailabilitySmoke.ctx.proof,HasteBootsCallerAvailabilitySmoke.ctx.fieldFuel) := rfl

section Native
open SingleSelectedSmoke (ctx world work prepared)

def reference : NativeGoldBatchPcsProgram.Context :=
  {HasteBootsBatchMeaningSmoke.ctx with parameters := ctx.parameters,root := ctx.root,queries := ⟨[],by decide⟩,values := ⟨[],by decide⟩}

/-- The actual single helper query is decoded on the original public
reference dimensions, without a supplied query-interpretation certificate. -/
example : NativeGoldCoefficientsQuery.interpret reference.parameters.width.val reference.parameters.numVariables.val ⟨ctx.query.models,none⟩ =
    some (RegistryPublicSourceObligation.query (show ctx.parameters = reference.parameters from rfl)
      (SingleOpeningNativeObligation.query ctx world work prepared)) :=
  HelperPublicSourceObligation.query_read ctx reference rfl world work prepared ctx.query rfl

/-- The single-opening fixture also retains independent packing/code widths. -/
example : reference.parameters.width.val = 3 ∧ reference.parameters.code.blockWidth.val = 4 ∧
    GoldHistorySourceTable.Geometry reference.parameters :=
  ⟨rfl,rfl,HelperPublicSource.geometry ctx reference rfl world work prepared⟩

example (candidateOrigin : CacheBackedSingleOpening.Origin ctx) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (history : List NativeTranscript.Observation) :
    HelperPublicSource.Compatible ctx reference candidateOrigin referenceOrigin world work prepared root history
      (HelperPublicSource.geometry ctx reference rfl world work prepared) :=
  HelperPublicSource.compatible ctx reference candidateOrigin referenceOrigin rfl rfl world work prepared root history

/-- The checked sum's coefficient vector transports with full parameter
identity, retaining the original helper packing width. -/
example (value : NativeFieldWire.GoldExtension) :
    HEq (HelperPublicSourceObligation.coefficients ctx.parameters value)
      (HelperPublicSourceObligation.coefficients reference.parameters value) :=
  HelperPublicSourceObligation.coefficients_heq rfl value

end Native
end
end FormalProof4FHE.HasteBoots.HelperPublicSourceSmoke
