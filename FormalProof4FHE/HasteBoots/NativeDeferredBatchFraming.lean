module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchTranscriptExtension
public import FormalProof4FHE.HasteBoots.NativeDeferredBatchAvailability
import all Init.Data.String.Defs
@[expose] public section

/-! Deferred sealing and actual accepted batch transitions derive receipt framing from an initially framed parent and static serialized-message bounds. Domains mention only ordered original group/packet pairs, never future oracle answers; later stopped results retain earlier receipt invariants. -/
namespace FormalProof4FHE.HasteBoots.NativeDeferredBatchFraming
open NativeDeferredBatchVerification (Context Call Progress Result Trace Receipt)
open NativeGoldBatchPcsProgram (Scheduler)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeGoldBlockCode (Stored Tables)
open NativeTranscriptExtension (Extends)
open NativeTranscriptFraming (Framed)
open NativeTranscript (Transcript utf8)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def CallFits (planned : Call) : Prop :=
  128 + (NativeGoldBatchBinding.queriesCodec.encode planned.queries).length +
    (NativeGoldBatchBinding.valuesCodec.encode planned.values).length < TranscriptFrame.lengthLimit ∧
  (NativeLookupRequestWire.rowCodec.encode planned.opening.test ++
    (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec).encode planned.opening.evaluations).length < TranscriptFrame.lengthLimit

/-- Only the actual ordered group/packet pairs are bounded, not unused groups
or fictitious cross-pairings. No condition depends on a future oracle answer. -/
def PacketDomain (registry : Vector (Oracle Stored)) (state : NativeDeferredOpeningBatch.State)
    (groups : List (Fin (NativeSourceRegistry.groupCount state.sources))) (openings : List NativeGoldBatchOpening.Opening) : Prop :=
  ∀ group opening, (group,opening) ∈ groups.zip openings → ∀ planned,
    NativeDeferredBatchVerification.call registry state group opening = some planned → CallFits planned

def Domain (ctx : Context) : Prop :=
  (NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).2 = .ok () →
    PacketDomain ctx.registry ctx.state (NativeDeferredOpeningBatch.usedGroups ctx.state) ctx.proof.val

def ValidProgress (tables : Tables) (fieldFuel : ℕ) {Memory : Type} (progress : Progress Memory) : Prop :=
  Framed progress.parent ∧ ∀ receipt ∈ progress.receipts,
    NativeGoldBatchSourceRisk.Framed (receipt.call.context tables fieldFuel receipt.before)

theorem call_framed (tables : Tables) (fieldFuel : ℕ) (parent : Transcript) (planned : Call)
    (framed : Framed parent) (fits : CallFits planned) :
    NativeGoldBatchSourceRisk.Framed (planned.context tables fieldFuel parent) := by
  obtain ⟨frames,bytes,valid⟩ := framed
  exact ⟨frames,bytes,valid,fits.1⟩

theorem seal_extension (state : NativeDeferredOpeningBatch.State) (packets : ℕ) :
    Extends state.parent (NativeDeferredOpeningBatch.sealBatch state packets).1.parent := by
  unfold NativeDeferredOpeningBatch.sealBatch
  split
  · split
    · exact NativeTranscriptExtension.Extends.refl state.parent
    · apply NativeTranscriptExtension.absorb state.parent 1 NativeDeferredOpeningBatch.sealLabel _
      constructor
      · change (utf8 "packed deferred opening seal v1").length < TranscriptFrame.lengthLimit
        decide +kernel
      · have first := NativeUsizeMessage.encode_length ⟨state.claims.val.length,state.claims.property⟩
        have second := NativeUsizeMessage.encode_length ⟨(NativeDeferredOpeningBatch.usedGroups state).length,NativeDeferredOpeningBatch.usedGroups_fits state⟩
        apply lt_of_le_of_lt (show _ ≤ 18 from ?_) (by decide +kernel : 18 < TranscriptFrame.lengthLimit)
        simpa only [List.length_append] using Nat.add_le_add first second
  · exact NativeTranscriptExtension.Extends.refl state.parent

theorem trace_framed {Memory : Type} {tables : Tables} {registry : Vector (Oracle Stored)}
    {state : NativeDeferredOpeningBatch.State} {fieldFuel : ℕ} {choose : Scheduler Memory} {workerFuel : ℕ} {world : World}
    {groups : List (Fin (NativeSourceRegistry.groupCount state.sources))} {openings : List NativeGoldBatchOpening.Opening}
    {before : Progress Memory} {result : Result Memory} {log : List NativeTranscript.Observation}
    (trace : Trace tables registry state fieldFuel choose workerFuel world groups openings before result log)
    (domain : PacketDomain registry state groups openings) (valid : ValidProgress tables fieldFuel before) :
    ValidProgress tables fieldFuel result.progress := by
  revert domain valid
  induction trace with
  | done before => intro _ valid; exact valid
  | packets groups openings before mismatch => intro _ valid; exact valid
  | index group rest opening openings before missing => intro _ valid; exact valid
  | stopped group rest opening openings before planned outcome log computed executed failed => intro _ valid; exact valid
  | passed group rest opening openings before after planned outcome log result later computed executed advanced tail ih =>
    intro domain valid
    have fits := domain group opening (by simp) planned computed
    obtain ⟨work,completion,next,sameOutcome,accepted,sameAfter⟩ := NativeDeferredBatchVerification.advance_spec before planned outcome after advanced
    have passed : (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run.1 = .completed work completion :=
      (congrArg Prod.fst executed).trans sameOutcome
    have extension := NativeGoldBatchTranscriptExtension.accepted (planned.context tables fieldFuel before.parent) choose workerFuel before.memory world
      work completion passed next accepted fits
    have afterValid : ValidProgress tables fieldFuel after := by
      rw [sameAfter]
      constructor
      · exact NativeTranscriptFraming.of_extension valid.1 extension
      · intro receipt member
        rcases List.mem_append.mp member with old | added
        · exact valid.2 receipt old
        · obtain rfl := List.mem_singleton.mp added
          exact call_framed tables fieldFuel before.parent planned valid.1 fits
    apply ih ?_ afterValid
    intro selected packet member call computed
    exact domain selected packet (by simp only [List.zip_cons_cons,List.mem_cons]; exact Or.inr member) call computed

theorem program_framed {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification result)
    (framed : Framed ctx.state.parent) (domain : Domain ctx) : ValidProgress ctx.tables ctx.fieldFuel result.progress := by
  have trace := NativeDeferredBatchVerification.program_trace ctx choose memory world result executed
  apply trace_framed trace.2 (domain trace.1)
  exact ⟨NativeTranscriptFraming.of_extension framed (seal_extension ctx.state ctx.proof.val.length),by simp⟩

theorem receipt_framed {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification result)
    (framed : Framed ctx.state.parent) (domain : Domain ctx) (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts) :
    NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) :=
  (program_framed ctx choose memory world result executed framed domain).2 receipt member
end
end FormalProof4FHE.HasteBoots.NativeDeferredBatchFraming
