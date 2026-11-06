module

public import FormalProof4FHE.HasteBoots.NativeChildParentFraming
public import FormalProof4FHE.HasteBoots.NativeLookupParentFraming
public import FormalProof4FHE.HasteBoots.NativeGoldHelperFraming
@[expose] public section

/-! End-to-end parent framing through original preflight, registry, retained
child initialization and successful body finish. Static native message-size
domains remain explicit; no future intermediate transcript framing is assumed. -/
namespace FormalProof4FHE.HasteBoots.NativeLookupBodyFraming
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends)
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def Domain {C S B : Type} (registry : Vector (Oracle C)) (requests : Vector Request)
    (proof : NativeSharedLookupProofData.Proof S B) : Prop :=
  NativeLookupParentFraming.Domain registry.val requests ∧
  9 + 128 * registry.val.length < TranscriptFrame.lengthLimit ∧
  NativeChildParentFraming.PacketDomain proof.multiplicities

theorem protocol_parent {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (executed : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    (domain : Domain registry requests proof) : Extends parent result.parent := by
  obtain ⟨geometry,launched,_,_,launch,body⟩ := NativeSharedLookupExecution.bound_origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result executed
  have earlier := NativeLookupParentFraming.prepared row registry helper parent requests world domain.1 domain.2.1
  exact earlier.trans (NativeChildParentFraming.launched_body requests.property.le (NativeSharedLookupParent.models requests) .retain
    (registry.val.map Oracle.geometry) geometry proof lookupFuel equalityFuel scalarFuel _ world launched.1 launched.2 result launch body domain.2.2)

theorem protocol_framed {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (executed : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    (framed : Framed parent) (domain : Domain registry requests proof) : Framed result.parent :=
  NativeTranscriptFraming.of_extension framed (protocol_parent row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result executed domain)

theorem prepared_body {Memory : Type}
    (ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory)
    (executed : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared)
    (framed : Framed ctx.parent) (domain : Domain ctx.registry ctx.requests ctx.proof) : Framed prepared.body.parent := by
  have same := (NativeGoldLookupVerification.prepare_spec _ prepared executed).1
  have erased := congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx choose memory world)
  have native : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 =
      .helpers prepared.body prepared.plan (.done prepared.helpers) := by rw [← erased,same]
  have origin := NativeGoldHelperVerification.helpers_origin ctx choose memory world prepared.body prepared.plan (.done prepared.helpers) native
  have body := congrArg Prod.fst origin.native
  change (run (NativeSharedLookupHelpers.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1.1 = some (.bound prepared.body) at body
  rw [NativeSharedLookupHelpers.run_protocol] at body
  exact protocol_framed NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world prepared.body body framed domain
end
end FormalProof4FHE.HasteBoots.NativeLookupBodyFraming
