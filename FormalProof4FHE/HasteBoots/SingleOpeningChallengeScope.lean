module
public import FormalProof4FHE.HasteBoots.SingleOpeningChallengeLink
public import FormalProof4FHE.HasteBoots.NativeFieldObservationScope
@[expose] public section

/-! A parsed column nonce strictly extends its recovered field input.
Actual native field collection therefore cannot expose any byte of that
column stream, including when collecting rejects or suspended prefixes. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningChallengeScope
open InputIndexedOracle (Input World)
open SingleOpeningChallengeLink (View)
open NativeRootMessage (Digest)
open TranscriptFrame (Frame encodeMany)

private theorem encodeMany_append (first later : List Frame) :
    encodeMany (first++later) = encodeMany first ++ encodeMany later := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,encodeMany,ih,List.append_assoc]

/-- Separation follows from complete encoded input lengths, not a hash
collision assumption or correctness of the quoted receipt. -/
theorem field_shorter (input : Input) (view : View)
    (parsed : SingleOpeningChallengeLink.parse input = some view) (profile : Digest) :
    (view.field.phase profile).pending.input.length < input.length := by
  have linked := SingleOpeningChallengeLink.parse_sound input view parsed profile
  have column := SingleOpeningColumnInputView.parse_sound input view.column linked.1 profile
  rw [linked.2.2.1,← column.1]
  simp only [NativePrequeryIndexLaw.requestInput,NativeIndexInputView.View.request,
    NativeIndexRequest.prepare,NativeTranscript.appendBytes,NativeTranscript.absorb,
    linked.2.2.2.1,encodeMany_append,encodeMany,List.length_append,List.length_nil,
    TranscriptFrame.encode_length]
  omega

theorem field_ne_column (input : Input) (view : View)
    (parsed : SingleOpeningChallengeLink.parse input = some view) (profile : Digest) :
    (view.field.phase profile).pending.input ≠ input := by
  intro equal
  have strict := field_shorter input view parsed profile
  rw [equal] at strict
  exact (Nat.lt_irrefl _) strict

/-- The old log can contain arbitrary hashes and partial queries under
other inputs. Only the recovered field stream is added by collection. -/
theorem unseen_after_collect (input : Input) (view : View)
    (parsed : SingleOpeningChallengeLink.parse input = some view) (profile : Digest)
    (fuel : ℕ) (world : World) (before : List NativeTranscript.Observation)
    (unseen : CausalStreamExposure.seen before input = false) :
    CausalStreamExposure.seen (before ++ (NativeFieldVector.execute NativeFields.goldilocksModulus fuel
      (NativeFieldVector.initial (view.field.phase profile) view.field.count.val) world).2) input = false :=
  NativeFieldObservationScope.unseen_after_collect _ _ _ _ _ _ unseen (field_ne_column input view parsed profile)
end FormalProof4FHE.HasteBoots.SingleOpeningChallengeScope
