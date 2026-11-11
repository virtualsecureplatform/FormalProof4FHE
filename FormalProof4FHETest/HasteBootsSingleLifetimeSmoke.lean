module
import all FormalProof4FHE.HasteBoots.SingleOpeningLifetimeMeasurable
import all FormalProof4FHETest.HasteBootsSingleEarlyReceiptSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleLifetimeSmoke
noncomputable section
open InputIndexedOracle (World)
open OracleProgram (Program run)
open SingleEarlyReceiptSmoke (field root zeros)

def fieldKey := TranscriptFrame.encodeMany field.frames
def columnKey := SingleEarlyReceiptSmoke.nonce

def step : ℕ → OracleMachine.Command ℕ Unit
  | 0 => .start fieldKey 1
  | 1 => .read fieldKey 700 0 (fun _ => 2)
  | 2 => .hash [77] (fun _ => 3)
  | 3 => .read fieldKey 999 1 (fun _ => 4)
  | 4 => .read columnKey 501 1 (fun _ => 5)
  | _ => .done ()

def trace (fuel : ℕ) := CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean 0) id step fuel zeros

/-- Starts and empty reads do not create a first-field boundary. -/
example : CausalStreamExposure.seen (trace 3).run.2 fieldKey = false ∧
    CausalStreamExposure.firstRead step (trace 3).run = some fieldKey := by decide +kernel
example : CausalStreamExposure.firstRead step (trace 4).run = some columnKey := by decide +kernel

/-- The later full history recovers the actual earlier machine packet. -/
example : CausalFirstStreamPrefix.recover fieldKey (trace 5).run.2 = some (trace 3).run.2 := by decide +kernel
example : (SingleOpeningFirstFieldSource.recover root (trace 5).run.2 field).map List.length = some 1 := by
  have found : CausalFirstStreamPrefix.recover (SingleOpeningFirstFieldSource.input field) (trace 5).run.2 = some (trace 3).run.2 := by decide +kernel
  have packet : (trace 3).run.2 = [.start fieldKey,.output fieldKey 700 [],.hash [77] (List.replicate 64 0)] := by decide +kernel
  unfold SingleOpeningFirstFieldSource.recover
  rw [found,Option.map_some,Option.map_some]
  apply congrArg some
  unfold SingleOpeningFirstFieldSource.selectedLog
  have fresh : (field.data.context,field.data.root) ∉
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root (trace 3).run.2).1.1.frozen := by
    rw [packet]
    simp only [NativeRootFamilyHistory.reconstruct,List.foldl_cons,List.foldl_nil,
      NativeRootFamilyState.record,NativeParentHistory.record,NativeParentLedger.discover_frozen,
      NativeRootFamilyHistory.initial,NativeParentLedger.empty,ite_true,Finset.notMem_empty]
    exact id
  rw [NativeRootFamilySourceSelection.select_new _ _ fresh]
  have hashes : (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root (trace 3).run.2).2.hash =
      JointHashCache.project (trace 3).run.2 := NativeGoldBatchFamilyAvailability.reconstructed_hash root (trace 3).run.2
  rw [hashes,packet]
  decide +kernel

/-- The prelude contains a far-offset partial field read before its hash. -/
def before : Program ℕ := .read fieldKey 63 1 (fun _ => .hash [88] (fun _ => .pure 0))
def oldTrace (fuel : ℕ) := CausalExposureLifetime.history (run before) id step fuel zeros

example : CausalStreamExposure.seen (run before zeros).run.2 fieldKey = true ∧
    CausalStreamExposure.firstRead step (oldTrace 3).run = none := by decide +kernel

/-- Later hashes cannot replace the inherited field's earlier empty source. -/
example : (SingleOpeningFirstFieldSource.recover root (oldTrace 5).run.2 field).map List.length = some 0 := by decide +kernel

def machine := OracleMachinePrelude.prepend step
def rebased (fuel : ℕ) := CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean before) id machine fuel zeros

/-- Rebasing charges the prelude read itself and retains the later exposure. -/
example : CausalStreamExposure.firstRead machine (rebased 0).run = some fieldKey := by decide +kernel
example : (rebased 7).run.2 = (oldTrace 5).run.2 := by decide +kernel
example : CausalStreamExposure.firstRead machine (rebased 5).run = none := by decide +kernel


def stopped (_ : Unit) : OracleMachine.Command Unit Unit := .done ()

/-- A stopped machine has no oracle trace containing an accepted native call. -/
example (Memory : Type) (ctx : NativeGoldPcsExecution.Context) (radius : ℕ) (world : World) :
    ¬SingleOpeningLifetimeSoundness.Failure Memory root ctx radius
      (SingleOpeningLifetimeSoundness.clean ()) id stopped world := by
  rintro ⟨fuel,⟨witness⟩⟩
  have touched := (SingleOpeningChallengeHistory.accepted_exposures witness.receipt _ witness.choose witness.verifierFuel witness.memory witness.accepted).1
  have empty : (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean ()) id stopped fuel world).run.2 = [] := by
    cases fuel <;> rfl
  have never (input : InputIndexedOracle.Input) : CausalStreamExposure.seen
      (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean ()) id stopped fuel world).run.2 input = false := by
    rw [empty]
    rfl
  have impossible := (never (SingleOpeningColumnLaw.input witness.receipt world)).symm.trans touched
  cases impossible

namespace Context
open SingleSelectedSmoke (ctx)

def other : NativeGoldPcsExecution.Context := {ctx with
  root := fun _ => 9,transcript := ⟨[99],fun _ => 1⟩,
  query := ⟨[],by decide⟩,claimed := ⟨[1],by decide⟩,
  opening := {ctx.opening with columns := ⟨[],by decide⟩},fieldFuel := 0,
  tables := ⟨fun _ => false,fun _ => false,fun _ => none⟩}

theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
    (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) := HasteBootsBatchMeaningSmoke.primitive

/-- Event charges use fixed parameters and selected nonce/history data. -/
example {S A : Type} (advance : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) (world : World) :
    SingleOpeningFieldProximity.event root other primitive 0 root advance packet world ↔
      SingleOpeningFieldProximity.event root ctx primitive 0 root advance packet world :=
  SingleOpeningEventContext.field_event root other ctx rfl primitive primitive 0 root advance packet world

example {S A : Type} (advance : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) (world : World) :
    SingleOpeningProfileColumnExposure.event root other primitive root advance packet 0 world ↔
      SingleOpeningProfileColumnExposure.event root ctx primitive root advance packet 0 world :=
  SingleOpeningEventContext.profile_column_event root other ctx rfl primitive primitive 0 root advance packet world
end Context

end
end FormalProof4FHE.HasteBoots.SingleLifetimeSmoke
