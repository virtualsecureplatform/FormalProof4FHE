module
import all FormalProof4FHE.HasteBoots.SingleOpeningProfileColumnNative
import all FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnChecks
import all FormalProof4FHETest.HasteBootsSingleCompositionSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleFamilySmoke
open InputIndexedOracle (Input)
open SingleLinkSmoke (field opening quote nonce)

/-- Structural selector fixture, not a claimed successfully constructed code. -/
def ctx : NativeGoldPcsExecution.Context :=
  ⟨⟨fun _ => true,fun _ => true,fun _ => some 0⟩,
    ⟨⟨0,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩,
      ⟨⟨1,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩,⟨8,by decide⟩,NativeBrakedownContext.modulus,⟨1,by decide⟩⟩⟩,
    ⟨[],fun _ => 0⟩,field.data.root,field.data.query,field.data.claimed,opening,1⟩

def step (input : Input) (_ : Unit) : OracleMachine.Command Unit Unit := .read input 93 1 (fun _ => ())

example : (SingleOpeningProfileColumnExposure.select ctx (step (nonce quote)) (.inl (),[])).map
    (fun decoded => (decoded.column.index.count.val,decoded.field.count.val)) = some (2,1) := by decide +kernel

/-- A structurally valid nonce with a smaller ordered quota is ineligible. -/
def foreignQuota := SingleOpeningPreparedChallenge.input field (fun _ => 0) opening NativeGoldPcsColumns.label
  ⟨8,by decide⟩ ⟨1,by decide⟩ quote

example : (SingleOpeningChallengeLink.parse foreignQuota).isSome = true := by decide +kernel
example : (SingleOpeningProfileColumnExposure.select ctx (step foreignQuota) (.inl (),[])).isNone = true := by decide +kernel

/-- A foreign field count cannot replace the original full matrix count. -/
def foreignField := SingleOpeningPreparedChallenge.input {field with count := ⟨2,by decide⟩} (fun _ => 0) opening
  NativeGoldPcsColumns.label ⟨8,by decide⟩ ⟨2,by decide⟩ quote

example : (SingleOpeningChallengeLink.parse foreignField).isSome = true := by decide +kernel
example : (SingleOpeningProfileColumnExposure.select ctx (step foreignField) (.inl (),[])).isNone = true := by decide +kernel

/-- Earlier positive exposure anywhere on this stream prevents a new charge. -/
example : (SingleOpeningProfileColumnExposure.select ctx (step (nonce quote))
    (.inl (),[.output (nonce quote) 700 [9]])).isNone = true := by decide +kernel

/-- Starts and empty reads preserve first-positive-read eligibility. -/
example : (SingleOpeningProfileColumnExposure.select ctx (step (nonce quote))
    (.inl (),[.start (nonce quote),.output (nonce quote) 700 []])).isSome = true := by decide +kernel

/-- Single-opening tests are exactly the random and structured lane families. -/
example : Fintype.card (SingleOpeningConcreteColumnFamily.Test ctx) = 2 := by decide +kernel

/-- Packing width three and code-symbol width four remain independent. -/
def mixedCtx : NativeGoldPcsExecution.Context := {ctx with parameters := {ctx.parameters with
  width := ⟨3,by decide⟩,leftVariables := ⟨1,by decide⟩,
  code := {ctx.parameters.code with messageLength := ⟨2,by decide⟩,blockWidth := ⟨4,by decide⟩}}}

def matrixState : NativeFieldVector.State :=
  {NativeFieldVector.initial (field.phase (fun _ => 0)) 18 with remaining := 0,values := List.range 18}

example : SingleOpeningRecoveredMatrix.random mixedCtx matrixState ⟨2,by decide⟩ (⟨1,by decide⟩,⟨2,by decide⟩) = 17 := by decide +kernel

example : Fintype.card (SingleOpeningConcreteColumnFamily.Test mixedCtx) = 6 ∧
    Fintype.card (Fin mixedCtx.parameters.code.blockWidth.val) = 4 := by decide +kernel

def responses : NativeGoldPcsOpening.Opening :=
  ⟨⟨List.replicate 6 7,by decide⟩,
    ⟨List.ofFn (fun index : Fin 6 => (⟨index.val,by have h := index.isLt; omega⟩ : NativeFieldRepresentation.GoldWord)),by decide⟩,
    ⟨[],by decide⟩⟩

example : SingleOpeningFixedResponseData.messages mixedCtx responses ⟨2,by decide⟩ ⟨1,by decide⟩ = 5 := by decide +kernel
example : SingleOpeningFixedResponseData.testMessages mixedCtx responses ⟨2,by decide⟩ ⟨1,by decide⟩ = 7 := by decide +kernel

end FormalProof4FHE.HasteBoots.SingleFamilySmoke
