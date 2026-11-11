module
import all FormalProof4FHE.HasteBoots.SingleOpeningFirstColumnCoverage
import all FormalProof4FHETest.HasteBootsSingleCompositionSmoke
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke
import all FormalProof4FHE.HasteBoots.NativeGoldBatchColumns
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleEarlyReceiptSmoke
noncomputable section
open InputIndexedOracle (Input World)
open SingleLinkSmoke (opening)

def root : NativeRootMessage.Digest := fun _ => 0
def zeros : World := fun _ => 0
def field := {SingleLinkSmoke.field with count := ⟨9,by decide⟩}
def quote : Input := TranscriptFrame.littleEndian 16 72 ++ List.replicate 64 0
def nonce := SingleOpeningPreparedChallenge.input field root opening NativeGoldPcsColumns.label ⟨8,by decide⟩ ⟨2,by decide⟩ quote

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read nonce 999 1 (fun _ => ())
def clean : NativeIndexExposureRisk.Packet Unit Unit := (.inl (),[])

def selectedOption := SingleOpeningEarlyReceiptPrefixRisk.select step clean
theorem present : selectedOption.isSome = true := by decide +kernel
def view := selectedOption.get present
theorem selected : SingleOpeningEarlyReceiptPrefixRisk.select step clean = some view := (Option.some_get present).symm

example : view.field.count.val = 9 ∧ view.receipt.length = 80 := by decide +kernel

/-- Receipt keys cannot alias the encoded original field stream. -/
example (consumed : Input) : SingleOpeningEarlyReceiptPrefixRisk.fieldInput view ≠ NativeReceiptPrefixView.key consumed :=
  SingleOpeningEarlyReceiptPrefixRisk.selected_not_receipt step clean view selected consumed

/-- The actual collector matches this quote at nine coefficients, retaining suspension at eight. -/
example : SingleOpeningEarlyReceiptBound.finiteEvent root 9 step clean zeros := by
  unfold SingleOpeningEarlyReceiptBound.finiteEvent
  rw [SingleOpeningFreshReceiptDigest.run_some root 9 step clean zeros view selected]
  unfold SingleOpeningEarlyReceiptBound.matching
  decide +kernel
example : ¬ SingleOpeningEarlyReceiptBound.finiteEvent root 8 step clean zeros := by
  unfold SingleOpeningEarlyReceiptBound.finiteEvent
  rw [SingleOpeningFreshReceiptDigest.run_some root 8 step clean zeros view selected]
  unfold SingleOpeningEarlyReceiptBound.matching
  decide +kernel

def key := NativeReceiptPrefixView.key (List.replicate 72 0)
def priorReceipt : NativeIndexExposureRisk.Packet Unit Unit := (.inl (),[.output key 63 [0]])
def priorOption := SingleOpeningEarlyReceiptPrefixRisk.select step priorReceipt
theorem priorPresent : priorOption.isSome = true := by decide +kernel
def priorView := priorOption.get priorPresent
theorem priorSelected : SingleOpeningEarlyReceiptPrefixRisk.select step priorReceipt = some priorView := (Option.some_get priorPresent).symm

example : (SingleOpeningEarlyReceiptPrefixRisk.select step priorReceipt).isSome = true := by decide +kernel
example : (NativeReceiptPrefixView.guesses 72 priorReceipt.2).card = 1 := by decide +kernel
example : SingleOpeningEarlyReceiptBound.finiteEvent root 9 step priorReceipt zeros := by
  unfold SingleOpeningEarlyReceiptBound.finiteEvent
  rw [SingleOpeningFreshReceiptDigest.run_some root 9 step priorReceipt zeros priorView priorSelected]
  unfold SingleOpeningEarlyReceiptBound.matching
  decide +kernel

/-- One earlier receipt coordinate excludes the fresh-digest branch. -/
example : ¬SingleOpeningFreshReceiptDigest.event root 9 step priorReceipt zeros := by
  unfold SingleOpeningFreshReceiptDigest.event
  rw [SingleOpeningFreshReceiptDigest.run_some root 9 step priorReceipt zeros priorView priorSelected]
  unfold SingleOpeningFreshReceiptDigest.after
  decide +kernel

example : SingleOpeningEarlyReceiptBound.risk step priorReceipt =
    1/(2 : ENNReal)^576 + 1/(2 : ENNReal)^512 := by
  rw [SingleOpeningEarlyReceiptBound.risk_selected step priorReceipt priorView priorSelected]
  rw [show (NativeReceiptPrefixView.guesses 72 priorReceipt.2).card = 1 by decide +kernel]
  simp only [Nat.cast_one]

/-- Starts and empty reads name no receipt-prefix target. -/
example : (NativeReceiptPrefixView.guesses 72 [.start key,.output key 63 []]).card = 0 := by decide +kernel

example : (SingleOpeningEarlyReceiptPrefixRisk.select step (.inl (),
    [.output (TranscriptFrame.encodeMany field.frames) 700 [0]])).isNone = true := by decide +kernel
example : (SingleOpeningEarlyReceiptPrefixRisk.select step (.inl (),[.output nonce 700 [0]])).isNone = true := by decide +kernel
example : (SingleOpeningEarlyReceiptPrefixRisk.select step (.inl (),
    [.start nonce,.output nonce 700 [],.output (TranscriptFrame.encodeMany field.frames) 700 []])).isSome = true := by decide +kernel

/-- The atomic column label is shared; field/response framing identifies the protocol. -/
example : NativeGoldBatchColumns.label = NativeGoldPcsColumns.label := by decide +kernel

/-- An unrelated column label is ineligible. -/
example : (SingleOpeningEarlyReceiptPrefixRisk.select
    (fun _ : Unit => (.read (SingleOpeningPreparedChallenge.input field root opening [42]
      ⟨8,by decide⟩ ⟨2,by decide⟩ quote) 999 1 (fun _ => ()) : OracleMachine.Command Unit Unit)) clean).isNone = true := by decide +kernel

namespace Native
open SingleSelectedSmoke (ctx world work prepared)

/-- Actual native preparation supplies its true receipt at an early column query. -/
example : ∃ sample, ∃ receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample,
    SingleOpeningEarlyReceiptBound.event ctx.transcript.profile
      (fun _ : Unit => (.read (SingleOpeningColumnLaw.input receipt world) 999 1 (fun _ => ()) : OracleMachine.Command Unit Unit))
      (.inl (),[]) world := by
  obtain ⟨sample,⟨receipt⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation ctx world work prepared
  let nativeStep (_ : Unit) : OracleMachine.Command Unit Unit := .read (SingleOpeningColumnLaw.input receipt world) 999 1 (fun _ => ())
  have first : CausalStreamExposure.firstRead nativeStep (.inl (),[]) = some (SingleOpeningColumnLaw.input receipt world) := by
    simp [CausalStreamExposure.firstRead,CausalSeedExposure.request,nativeStep,CausalStreamExposure.seen]
  rcases SingleOpeningEarlyReceiptNative.first_column_cases receipt prepared [] rfl (by simp) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) nativeStep (.inl (),[]) first with seen | early
  · simp [CausalStreamExposure.seen] at seen
  · exact ⟨sample,receipt,early⟩
end Native

end
end FormalProof4FHE.HasteBoots.SingleEarlyReceiptSmoke
