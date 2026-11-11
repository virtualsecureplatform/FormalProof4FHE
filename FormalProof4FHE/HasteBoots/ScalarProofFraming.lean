module

public import FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension
public import FormalProof4FHE.HasteBoots.NativeExactCodec

@[expose] public section

namespace FormalProof4FHE.HasteBoots.ScalarProofFraming

open NativeScalarBatchWire NativeScalarBatchPreflight NativePrefixCodec
open NativeUsizeMessage (Usize)

/-- Canonical analysis encoding; correspondence with Rust deserialization remains separate. -/
def instanceCodec : Codec Instance := vector messageCodec

def proofCodec : Codec Proof := vector instanceCodec

theorem usize_length_mono (left right : Usize) (ordered : left.val ≤ right.val) :
    (NativeUsizeMessage.encode left).length ≤ (NativeUsizeMessage.encode right).length := by
  unfold NativeUsizeMessage.encode
  split_ifs <;>
    simp only [List.length_cons, List.length_nil, TranscriptFrame.littleEndian_length] <;> omega

theorem message_length_le (certificate : Instance) (message : Message)
    (member : message ∈ certificate.val) :
    (messageCodec.encode message).length ≤
      (certificate.val.flatMap messageCodec.encode).length := by
  obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
  rw [same]
  simp only [List.flatMap_append, List.flatMap_cons, List.length_append]
  omega

/-- Collection keeps one message per certificate and cannot enlarge their combined payload. -/
theorem collect_bound (round : ℕ) (instances : List Instance) (messages : List Message)
    (found : NativeScalarBatchRoundPacket.collect round instances = some messages) :
    messages.length = instances.length ∧
    (messages.flatMap messageCodec.encode).length ≤
      (instances.flatMap instanceCodec.encode).length := by
  induction instances generalizing messages with
  | nil =>
    simp only [NativeScalarBatchRoundPacket.collect] at found
    cases found
    exact ⟨rfl, Nat.le_refl _⟩
  | cons certificate tail ih =>
    simp only [NativeScalarBatchRoundPacket.collect] at found
    cases access : certificate.val[round]? with
    | none => simp [access] at found
    | some message =>
      cases rest : NativeScalarBatchRoundPacket.collect round tail with
      | none => simp [access, rest] at found
      | some remaining =>
        simp only [access, Option.bind_some, rest, Option.map_some, Option.some.injEq] at found
        subst messages
        obtain ⟨count, bound⟩ := ih remaining rest
        have selected := message_length_le certificate message (List.mem_of_getElem? access)
        constructor
        · simp only [List.length_cons, count]
        · simp only [List.flatMap_cons, List.length_append]
          change (messageCodec.encode message).length + _ ≤
            (NativeUsizeMessage.encode ⟨certificate.val.length, certificate.property⟩ ++
              certificate.val.flatMap messageCodec.encode).length + _
          simp only [List.length_append]
          omega

/-- A nonempty proof also pays for the round index using its first certificate header. -/
theorem collect_round_bound (round : Usize) (instances : List Instance)
    (nonempty : instances ≠ []) (messages : List Message)
    (found : NativeScalarBatchRoundPacket.collect round.val instances = some messages) :
    (NativeUsizeMessage.encode round).length +
      (messages.flatMap messageCodec.encode).length ≤
      (instances.flatMap instanceCodec.encode).length := by
  cases instances with
  | nil => exact False.elim (nonempty rfl)
  | cons certificate tail =>
    simp only [NativeScalarBatchRoundPacket.collect] at found
    cases access : certificate.val[round.val]? with
    | none => simp [access] at found
    | some message =>
      cases rest : NativeScalarBatchRoundPacket.collect round.val tail with
      | none => simp [access, rest] at found
      | some remaining =>
        simp only [access, Option.bind_some, rest, Option.map_some, Option.some.injEq] at found
        subst messages
        have bound := (collect_bound round.val tail remaining rest).2
        have selected := message_length_le certificate message (List.mem_of_getElem? access)
        have inside : round.val < certificate.val.length := List.getElem?_eq_some_iff.mp access |>.1
        have header := usize_length_mono round
          ⟨certificate.val.length, certificate.property⟩ (Nat.le_of_lt inside)
        simp only [List.flatMap_cons, List.length_append]
        change _ ≤ (NativeUsizeMessage.encode ⟨certificate.val.length, certificate.property⟩ ++
          certificate.val.flatMap messageCodec.encode).length + _
        simp only [List.length_append]
        omega

theorem packet_length_le (round : Usize) (proof : Proof) (nonempty : proof.val ≠ [])
    (packet : RoundPacket) (found : NativeScalarBatchRoundPacket.packet round proof = some packet) :
    (roundCodec.encode packet).length ≤ (proofCodec.encode proof).length := by
  unfold NativeScalarBatchRoundPacket.packet at found
  cases collected : NativeScalarBatchRoundPacket.collect round.val proof.val with
  | none => simp [collected] at found
  | some messages =>
    simp only [collected, Option.bind_some] at found
    split at found
    next fits =>
      cases found
      have count := (collect_bound round.val proof.val messages collected).1
      have bound := collect_round_bound round proof.val nonempty messages collected
      have same : (⟨messages.length, fits⟩ : Usize) =
          ⟨proof.val.length, proof.property⟩ := Fin.ext count
      rw [round_encode]
      change (_ ++ (NativeUsizeMessage.encode ⟨messages.length, fits⟩ ++ _)).length ≤
        (NativeUsizeMessage.encode ⟨proof.val.length, proof.property⟩ ++ _).length
      rw [same]
      simp only [List.length_append]
      omega
    next => contradiction

/-- A bounded canonical byte source supplies every scalar round framing bound.
This does not assert that the analysis reader implements the Rust decoder. -/
theorem roundDomain_of_bytes (proof : Proof) (nonempty : proof.val ≠ [])
    (source : Vector InputIndexedOracle.Byte)
    (parsed : NativeExactCodec.read proofCodec source.val = some proof) :
    NativeScalarTranscriptExtension.RoundDomain proof := by
  intro round packet found
  have bound := packet_length_le round proof nonempty packet found
  rw [NativeExactCodec.read_sound proofCodec source.val proof parsed] at bound
  exact lt_of_le_of_lt bound source.property

/-- The byte witness is precisely a canonical serialization-size obligation;
it contributes no unproved native deserializer claim. -/
theorem bounded_source_iff (proof : Proof) :
    (∃ source : Vector InputIndexedOracle.Byte,
      NativeExactCodec.read proofCodec source.val = some proof) ↔
      (proofCodec.encode proof).length < 2^64 := by
  constructor
  · rintro ⟨source, parsed⟩
    rw [NativeExactCodec.read_sound proofCodec source.val proof parsed]
    exact source.property
  · intro fits
    exact ⟨⟨proofCodec.encode proof, fits⟩, NativeExactCodec.read_encode proofCodec proof⟩

/-- A completed native scalar verifier necessarily checked a nonempty batch. -/
theorem nonempty_of_finished (transcript : NativeTranscript.Transcript) (statement : Statement)
    (proof : Proof) (fuel : ℕ) (world : InputIndexedOracle.World)
    (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims) :
    proof.val ≠ [] := by
  cases checked : beginVerify transcript statement proof with
  | error error =>
    have terminal := NativeScalarBatchVerifier.execute_terminal statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world
      (Or.inr ⟨.reject error, by rw [NativeScalarBatchVerifier.initial_failure _ _ _ _ checked]⟩)
    rw [terminal, NativeScalarBatchVerifier.initial_failure _ _ _ _ checked] at finished
    contradiction
  | ok result =>
    have accepted := (beginVerify_ok_iff transcript result statement proof).mp checked
    obtain ⟨first, head, _, _, _⟩ := dimensions_success statement accepted.2.1
    have count := (proofShape_iff statement proof |>.mp accepted.1).length_eq
    intro empty
    rw [empty, List.length_nil] at count
    have nil := List.length_eq_zero_iff.mp count
    simp [nil] at head

end FormalProof4FHE.HasteBoots.ScalarProofFraming
