module
public import FormalProof4FHE.HasteBoots.ReceiptPayloadView
public import FormalProof4FHE.HasteBoots.FieldConsumedReplay
@[expose] public section

/-! Finite coefficient candidates determined entirely by earlier receipt keys.
Rejected candidates are decoded too; neither receipt digests nor their encoded
lengths are used. Nonpositive widths have no recovery guarantee. -/
namespace FormalProof4FHE.HasteBoots.ReceiptCoefficientCandidates
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open scoped Classical
noncomputable section

def chunks (width : ℕ) : ℕ → Input → List Input
  | 0, _ => []
  | fuel+1, raw => if raw = [] then [] else raw.take width :: chunks width fuel (raw.drop width)

theorem recover_chunks (width : ℕ) (positive : 0 < width) (original : List Input)
    (uniform : ∀ raw ∈ original, raw.length = width) (fuel : ℕ) (enough : original.length ≤ fuel) :
    chunks width fuel original.flatten = original := by
  induction original generalizing fuel with
  | nil => cases fuel <;> simp [chunks]
  | cons raw rest ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have length := uniform raw List.mem_cons_self
      have nonempty : raw ++ rest.flatten ≠ [] := by
        intro empty
        have := (List.append_eq_nil_iff.mp empty).1
        rw [this,List.length_nil] at length
        omega
      simp only [List.flatten_cons,chunks,nonempty,ite_false]
      have take : (raw ++ rest.flatten).take width = raw := by rw [← length,List.take_left]
      have drop : (raw ++ rest.flatten).drop width = rest.flatten := by rw [← length,List.drop_left]
      rw [take,drop]
      rw [ih (fun raw member => uniform raw (List.mem_cons_of_mem _ member)) fuel (by simpa using enough)]

theorem enough_chunks (width : ℕ) (positive : 0 < width) (original : List Input)
    (uniform : ∀ raw ∈ original, raw.length = width) : original.length ≤ original.flatten.length := by
  induction original with
  | nil => simp
  | cons raw rest ih =>
    have length := uniform raw List.mem_cons_self
    have tail := ih (fun raw member => uniform raw (List.mem_cons_of_mem _ member))
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

def decode (p : ℕ) (raw : Input) : List ℕ :=
  FieldConsumedReplay.values p (chunks (CanonicalByteSampler.byteCount p) raw.length raw)

theorem decode_traced (p : ℕ) (positive : 0 < CanonicalByteSampler.byteCount p)
    (state : NativeFieldVector.State) (trace : FieldConsumedReplay.Traced p state) :
    decode p state.phase.consumed = state.values := by
  rw [decode,trace.consumed,recover_chunks _ positive state.chunks trace.widths _
    (enough_chunks _ positive state.chunks trace.widths),trace.accepted]

def candidates (p : ℕ) (history : List Observation) : Finset (List ℕ) :=
  (ReceiptPayloadView.payloads history).image (decode p)

theorem covered (p : ℕ) (positive : 0 < CanonicalByteSampler.byteCount p)
    (state : NativeFieldVector.State) (trace : FieldConsumedReplay.Traced p state)
    (history : List Observation) (exposed : CausalStreamExposure.seen history (NativeFieldReceipt.input state.phase) = true) :
    state.values ∈ candidates p history := by
  apply Finset.mem_image.mpr
  exact ⟨state.phase.consumed,ReceiptPayloadView.seen _ history exposed,decode_traced p positive state trace⟩

theorem card (p : ℕ) (history : List Observation) : (candidates p history).card ≤ history.length :=
  (Finset.card_image_le).trans (ReceiptPayloadView.card history)

theorem on_fiber {P : Type} (past : InputIndexedOracle.World → NativeTranscript.Execution P)
    (world other : InputIndexedOracle.World) (p : ℕ) (same : (past other).run = (past world).run) :
    candidates p (past other).run.2 = candidates p (past world).run.2 := by rw [same]

end
end FormalProof4FHE.HasteBoots.ReceiptCoefficientCandidates
