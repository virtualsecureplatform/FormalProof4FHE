module
import all FormalProof4FHE.HasteBoots.LookupSourcePublicOwnership
import all FormalProof4FHE.HasteBoots.RegistryPublicSourceObligation
import all FormalProof4FHETest.HasteBootsCallerAvailabilitySmoke
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke

namespace FormalProof4FHE.HasteBoots.RegistryPublicSourceSmoke
open HasteBootsBatchMeaningSmoke (ctx world work prepared root usize)
open NativeFields (Goldilocks)
noncomputable section

def helper : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening) :=
  {HasteBootsCallerAvailabilitySmoke.ctx with registry :=
    ⟨[⟨ctx.parameters,ctx.root⟩,⟨{ctx.parameters with queries := usize 99},ctx.root⟩],by decide⟩}
def original := RegistryPublicSource.context helper ⟨0,by decide⟩
def later := RegistryPublicSource.context helper ⟨1,by decide⟩

/-- Each reference retains its original registry record, root and quota. -/
example : original.parameters = ctx.parameters ∧ original.root = ctx.root ∧ later.parameters.queries.val = 99 := ⟨rfl,rfl,rfl⟩

/-- Equal raw code and root do not identify full parameters of later aliases. -/
example : original.parameters.code = later.parameters.code ∧ original.root = later.root ∧ original.parameters ≠ later.parameters := by
  refine ⟨rfl,rfl,?_⟩
  intro same
  have quota := congrArg (fun p : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored => p.queries.val) same
  change 1 = 99 at quota
  contradiction

/-- A reference extraction context has no call-dependent query/value payload. -/
example : original.queries.val = [] ∧ original.values.val = [] ∧ original.opening.columns.val = [] := ⟨rfl,rfl,rfl⟩

/-- Geometry is supplied by the actual original batch preparation. -/
example : GoldHistorySourceTable.Geometry original.parameters :=
  RegistryPublicSource.geometry ctx original rfl world work prepared

/-- The second original right query survives shared left-response grouping
and is interpreted as the original raw query on the reference dimensions. -/
example : NativeGoldCoefficientsQuery.interpret original.parameters.width.val original.parameters.numVariables.val
      ⟨HasteBootsBatchMeaningSmoke.secondQuery.models,none⟩ =
    some (RegistryPublicSourceObligation.query (show ctx.parameters = original.parameters from rfl)
      (BatchOpeningNativeObligation.query ctx world work prepared ⟨1,by decide +kernel⟩)) :=
  RegistryPublicSourceObligation.query_read ctx original rfl world work prepared ⟨1,by decide +kernel⟩ _ (by decide +kernel)

example : NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨0,by decide +kernel⟩ =
    NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨1,by decide +kernel⟩ ∧
    work.binding.queries.val[0]? ≠ work.binding.queries.val[1]? := by decide +kernel

def row : NativeLookupRequestWire.Row := ⟨[1,0,0],by decide⟩
def aliasRow : NativeLookupRequestWire.Row := ⟨[usize (NativeFields.goldilocksModulus+1),0,0],by decide⟩

/-- Wrong-row obligations compare native field coordinates; noncanonical raw
words remain distinct original data. -/
example : row ≠ aliasRow ∧ RegistryPublicSourceObligation.rowValue original.parameters row =
    RegistryPublicSourceObligation.rowValue original.parameters aliasRow := by
  constructor
  · decide +kernel
  · funext lane
    fin_cases lane <;> decide +kernel

/-- The actual first original batch getter also matches a noncanonical
received zero row; the falsity reduction derives its width and encoding. -/
def zeroAlias : NativeLookupRequestWire.Row := ⟨[usize NativeFields.goldilocksModulus,0,0],by decide⟩
example : work.binding.values.val[0]? = some (HasteBootsBatchMeaningSmoke.zeros 3 (by decide)) ∧
    NativeGoldPcsClaim.equal (HasteBootsBatchMeaningSmoke.zeros 3 (by decide)).val zeroAlias.val = true := by decide +kernel

/-- The original allocated cube agrees with the call's cube while retaining
independent constructor provenance records and empty reference call data. -/
example (candidateOrigin : CacheBackedCodeOrigin.Origin ctx) (referenceOrigin : CacheBackedCodeOrigin.Origin original)
    (history : List NativeTranscript.Observation) :
    RegistryPublicSource.Compatible ctx original candidateOrigin referenceOrigin world work prepared root history
      (RegistryPublicSource.geometry ctx original rfl world work prepared) :=
  RegistryPublicSource.compatible ctx original candidateOrigin referenceOrigin rfl rfl world work prepared root history

end
end FormalProof4FHE.HasteBoots.RegistryPublicSourceSmoke
