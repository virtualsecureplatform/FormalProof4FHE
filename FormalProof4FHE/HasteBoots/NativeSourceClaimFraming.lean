module

public import FormalProof4FHE.HasteBoots.NativeDeferredBatchFraming
public import FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
import all Init.Data.String.Defs
@[expose] public section

/-! Actual source-claim insertion and alias/rejection control preserve append-only framing under original encoded query/value bounds. Only used slots with an available row require a size bound; no future context answer selects a framing certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeSourceClaimFraming
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row Request)
open NativeSharedSourceClaims (Progress Result)
open NativeTranscriptExtension (Extends)
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def Fits (query : Query) (values : Row) : Prop :=
  18 + (NativeGoldPcsWire.queryCodec.encode query).length + (NativeLookupRequestWire.rowCodec.encode values).length < TranscriptFrame.lengthLimit

def Domain {C : Type} (registry : Vector (Oracle C)) (requests : Vector Request) (query : Query) (values : Vector Row) : Prop :=
  ∀ slot : Fin registry.val.length, NativeSharedSourceClaims.used requests slot = true → ∀ value,
    values.val[slot.val]? = some value → Fits query value

theorem push_extension {C : Type} (registry : Vector (Oracle C)) (state : NativeDeferredOpeningBatch.State)
    (slot : NativeUsizeMessage.Usize) (query : Query) (values : Row) (fits : Fits query values) :
    Extends state.parent (NativeDeferredOpeningBatch.push registry state slot query values).1.parent := by
  unfold NativeDeferredOpeningBatch.push
  split
  · exact NativeTranscriptExtension.Extends.refl state.parent
  · split
    · split
      · split
        · apply NativeTranscriptExtension.absorb state.parent 1 NativeDeferredOpeningBatch.claimLabel _
          constructor
          · change (NativeTranscript.utf8 "packed deferred opening claim v1").length < TranscriptFrame.lengthLimit
            decide +kernel
          · have count := NativeUsizeMessage.encode_length ⟨state.claims.val.length,state.claims.property⟩
            have index := NativeUsizeMessage.encode_length slot
            apply lt_of_le_of_lt (show _ ≤ 18 + (NativeGoldPcsWire.queryCodec.encode query).length +
              (NativeLookupRequestWire.rowCodec.encode values).length from ?_) fits
            simp only [NativeDeferredOpeningBatch.claimPayload,List.length_append]
            omega
        · exact NativeTranscriptExtension.Extends.refl state.parent
      · exact NativeTranscriptExtension.Extends.refl state.parent
    · exact NativeTranscriptExtension.Extends.refl state.parent

theorem after_context {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest)
    (fits : ∀ value, values.val[slot.val]? = some value → Fits query value) :
    Extends before.state.parent (NativeSharedSourceClaims.afterContext registry query values slot before context).progress.state.parent := by
  cases context with
  | none => exact NativeTranscriptExtension.Extends.refl before.state.parent
  | some digest =>
    simp only [NativeSharedSourceClaims.afterContext]
    split
    · exact NativeTranscriptExtension.Extends.refl before.state.parent
    next value found =>
      split
      · split <;> exact NativeTranscriptExtension.Extends.refl before.state.parent
      · have preserved := push_extension registry before.state ⟨slot.val,lt_of_lt_of_le slot.isLt registry.property.le⟩ query value (fits value found)
        split <;> exact preserved

theorem step_extension {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World)
    (domain : Domain registry requests query values) :
    Extends before.state.parent (run (NativeSharedSourceClaims.step row registry requests query values slot before) world).run.1.progress.state.parent := by
  unfold NativeSharedSourceClaims.step
  split
  next used =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact after_context registry query values slot before _ (domain slot used)
  next unused => exact NativeTranscriptExtension.Extends.refl before.state.parent

theorem loop_extension {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before : Progress) (world : World)
    (domain : Domain registry requests query values) :
    Extends before.state.parent (run (NativeSharedSourceClaims.loop row registry requests query values slots before) world).run.1.progress.state.parent := by
  induction slots generalizing before with
  | nil => exact NativeTranscriptExtension.Extends.refl before.state.parent
  | cons slot rest ih =>
    simp only [NativeSharedSourceClaims.loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    have first := step_extension row registry requests query values slot before world domain
    cases selected : (run (NativeSharedSourceClaims.step row registry requests query values slot before) world).run.1 with
    | stopped after reason =>
      simpa only [selected,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using first
    | done after =>
      simp only [selected] at first ⊢
      exact first.trans (ih after)

theorem program_framed {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World)
    (framed : Framed state.parent) (domain : Domain registry requests query values) :
    Framed (run (NativeSharedSourceClaims.program row registry requests query values state) world).run.1.progress.state.parent :=
  NativeTranscriptFraming.of_extension framed (loop_extension row registry requests query values _ _ world domain)
end
end FormalProof4FHE.HasteBoots.NativeSourceClaimFraming
