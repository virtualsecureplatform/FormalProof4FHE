module

public import FormalProof4FHE.HasteBoots.TranscriptFrame
public import ToMathlib.Control.WriterT
import all Init.Data.String.Defs

@[expose] public section

/-!
# Native framed transcript transitions in the joint ideal world

This specifies `classical_transcript.rs` kinds 0–8, including reader starts,
empty reads, field receipts, checkpoints, and linked-child fingerprints.
Every query uses the same `InputIndexedOracle.World`. The log retains the
actual order of starts and output chunks, including receipt queries.

Field sampling calls `drawField` for every candidate, including rejections;
this module does not replace the rejection algorithm with accepted values.
Typed field/basis descriptors, parent-binding wrapper checks, adaptive
revelation, work accounting, and checked Rust correspondence remain separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeTranscript

open InputIndexedOracle (Byte Input World bytes)
open TranscriptFrame (Frame encode littleEndian)

def utf8 (text : String) : Input :=
  text.toUTF8.data.toList.map (fun byte => ⟨byte.toNat % 256, Nat.mod_lt _ (by decide)⟩)

structure Transcript where
  input : Input
  profile : Fin 64 → Byte

/-- These are observations, not distinct random-oracle keys or a work metric. -/
inductive Observation where
  | start (input : Input)
  | output (input : Input) (offset : ℕ) (bytes : Input)
  deriving DecidableEq

abbrev Execution := Writer (List Observation)

def absorb (state : Transcript) (kind : Fin 9) (label message : Input) : Transcript :=
  { state with input := state.input ++ encode ⟨kind, label, message⟩ }

def appendBytes (state : Transcript) (label message : Input) : Transcript :=
  absorb state 1 label message

def new (protocol : Input) (profile : Fin 64 → Byte) : Transcript :=
  let initial : Transcript := ⟨[], profile⟩
  let initial := absorb initial 0 (utf8 "protocol") (utf8 "HasteBoots framed SHAKE256 v1")
  let initial := absorb initial 0 (utf8 "application") protocol
  absorb initial 0 (utf8 "trusted profile") (List.ofFn profile)

/-- One finalization and one read, including when the requested count is zero. -/
def query (world : World) (input : Input) (count : ℕ) : Execution Input :=
  let output := bytes world input 0 count
  WriterT.mk (output, [.start input, .output input 0 output])

def requestInput (state : Transcript) (label : Input) (count : ℕ) : Input :=
  (absorb state 2 label (littleEndian 8 count)).input

def challengeBytes (world : World) (state : Transcript) (label : Input) (count : ℕ) :
    Execution (Input × Transcript) := do
  let requested := absorb state 2 label (littleEndian 8 count)
  let output ← query world requested.input count
  pure (output, absorb requested 3 label output)

/-- A checkpoint finalizes a framed clone and leaves the parent state alone. -/
def checkpoint (world : World) (state : Transcript) : Execution Input :=
  query world (absorb state 8 (utf8 "parent checkpoint") []).input 64

structure FieldPhase where
  pending : Transcript
  label : Input
  consumed : Input

/-- Finalization occurs even for an empty field-vector request. -/
def beginField (state : Transcript) (label : Input) (modulus count : ℕ) : Execution FieldPhase :=
  let pending := absorb state 4 label (littleEndian 16 modulus ++ littleEndian 8 count)
  WriterT.mk (⟨pending, label, []⟩, [.start pending.input])

/-- Each call corresponds to an actual reader read, not an accepted sample. -/
def drawField (world : World) (phase : FieldPhase) (count : ℕ) : Execution (Input × FieldPhase) :=
  let output := bytes world phase.pending.input phase.consumed.length count
  WriterT.mk ((output, { phase with consumed := phase.consumed ++ output }),
    [.output phase.pending.input phase.consumed.length output])

def receipt (world : World) (consumed : Input) : Execution Input := do
  let digest ← query world (utf8 "HasteBoots consumed field bytes v1" ++ consumed) 64
  pure (littleEndian 16 consumed.length ++ digest)

def finishField (world : World) (phase : FieldPhase) : Execution Transcript := do
  let output ← receipt world phase.consumed
  pure (absorb phase.pending 5 phase.label output)

/-- The label and context precede the seed query. The child inherits the
trusted profile and explicitly absorbs its label, context, and parent seed. -/
def forkChild (world : World) (parent : Transcript) (label context : Input) :
    Execution (Transcript × Transcript) := do
  let (seed, parent) ← challengeBytes world (absorb parent 6 label context)
    (utf8 "classical child seed") 64
  let child := new (utf8 "HasteBoots framed SHAKE256 child v1") parent.profile
  let child := appendBytes child (utf8 "child label") label
  let child := appendBytes child (utf8 "child context") context
  let child := appendBytes child (utf8 "parent seed") seed
  pure (parent, child)

/-- The owned-child primitive updates both states. Detached wrapper lineage
and one-shot binding checks must be established before invoking it. -/
def finishLinkedChild (world : World) (parent child : Transcript) (label : Input) :
    Execution (Transcript × Transcript) := do
  let (fingerprint, child) ← challengeBytes world child (utf8 "classical child finish") 64
  pure (absorb parent 7 label fingerprint, child)

theorem challenge_length (world : World) (state : Transcript) (label : Input) (count : ℕ) :
    (challengeBytes world state label count).run.1.1.length = count := by
  change (bytes world (requestInput state label count) 0 count).length = count
  exact InputIndexedOracle.bytes_length _ _ _ _

theorem challenge_profile (world : World) (state : Transcript) (label : Input) (count : ℕ) :
    (challengeBytes world state label count).run.1.2.profile = state.profile := rfl

/-- The returned output and its receipt refer to the very same request. -/
theorem challenge_state (world : World) (state : Transcript) (label : Input) (count : ℕ) :
    (challengeBytes world state label count).run.1.2.input =
      requestInput state label count ++
        encode ⟨3, label, bytes world (requestInput state label count) 0 count⟩ := rfl

theorem challenge_observations (world : World) (state : Transcript) (label : Input) (count : ℕ) :
    (challengeBytes world state label count).run.2 =
      [.start (requestInput state label count),
       .output (requestInput state label count) 0
         (bytes world (requestInput state label count) 0 count)] := rfl

/-- Framing preserves label identity. This gives distinct inputs for distinct
labels, not fresh randomness relative to an adversary's existing queries. -/
theorem request_label_injective (state : Transcript) (left right : Input) (count : ℕ)
    (leftFits : left.length < TranscriptFrame.lengthLimit)
    (rightFits : right.length < TranscriptFrame.lengthLimit)
    (same : requestInput state left count = requestInput state right count) : left = right := by
  change state.input ++ encode ⟨2, left, littleEndian 8 count⟩ =
    state.input ++ encode ⟨2, right, littleEndian 8 count⟩ at same
  have short : (littleEndian 8 count).length < TranscriptFrame.lengthLimit := by
    rw [TranscriptFrame.littleEndian_length]
    decide
  have frames := TranscriptFrame.encode_injective _ _ ⟨leftFits, short⟩ ⟨rightFits, short⟩
    (List.append_cancel_left same)
  exact congrArg Frame.label frames

def Coherent (world : World) (phase : FieldPhase) : Prop :=
  phase.consumed = bytes world phase.pending.input 0 phase.consumed.length

theorem begin_coherent (world : World) (state : Transcript) (label : Input) (modulus count : ℕ) :
    Coherent world (beginField state label modulus count).run.1 := by
  simp [Coherent, beginField, WriterT.run, WriterT.mk, bytes]

/-- Every rejected candidate stays in the consumed prefix. No virtual bytes
or accepted-value substitution is used to produce the receipt. -/
theorem draw_coherent (world : World) (phase : FieldPhase) (coherent : Coherent world phase)
    (count : ℕ) : Coherent world (drawField world phase count).run.1.2 := by
  change phase.consumed ++ bytes world phase.pending.input phase.consumed.length count =
    bytes world phase.pending.input 0
      (phase.consumed ++ bytes world phase.pending.input phase.consumed.length count).length
  rw [List.length_append, InputIndexedOracle.bytes_length]
  have split := InputIndexedOracle.bytes_append world phase.pending.input 0 phase.consumed.length count
  simp only [Nat.zero_add] at split
  rw [split]
  exact congrArg (fun initial => initial ++ bytes world phase.pending.input phase.consumed.length count) coherent

/-- Split reads have different observation logs but preserve both the total
raw output and final field phase, hence also the later receipt input. -/
theorem draw_split (world : World) (phase : FieldPhase) (first second : ℕ) :
    (drawField world phase (first + second)).run.1 =
      ((drawField world phase first).run.1.1 ++
        (drawField world (drawField world phase first).run.1.2 second).run.1.1,
       (drawField world (drawField world phase first).run.1.2 second).run.1.2) := by
  simp [drawField, WriterT.run_mk, InputIndexedOracle.bytes_append,
    InputIndexedOracle.bytes_length, List.append_assoc]

theorem receipt_length (world : World) (consumed : Input) :
    (receipt world consumed).run.1.length = 80 := by
  change (littleEndian 16 consumed.length ++
    bytes world (utf8 "HasteBoots consumed field bytes v1" ++ consumed) 0 64).length = 80
  simp [TranscriptFrame.littleEndian_length, InputIndexedOracle.bytes_length]

/-- The receipt query retains the entire consumed raw prefix in its key. -/
theorem receipt_observations (world : World) (consumed : Input) :
    (receipt world consumed).run.2 =
      [.start (utf8 "HasteBoots consumed field bytes v1" ++ consumed),
       .output (utf8 "HasteBoots consumed field bytes v1" ++ consumed) 0
         (bytes world (utf8 "HasteBoots consumed field bytes v1" ++ consumed) 0 64)] := rfl

theorem fork_profiles (world : World) (parent : Transcript) (label context : Input) :
    (forkChild world parent label context).run.1.1.profile = parent.profile ∧
      (forkChild world parent label context).run.1.2.profile = parent.profile := by
  exact ⟨rfl, rfl⟩

/-- The receipt domain starts with ASCII 'H' (72), outside the frame-kind
range. No receipt query can equal a nonempty encoded frame stream. This is
byte-level domain separation, not freshness against adversarial prequeries. -/
theorem receipt_domain_separated (consumed suffix : Input) (frame : Frame) :
    utf8 "HasteBoots consumed field bytes v1" ++ consumed ≠ encode frame ++ suffix := by
  intro same
  have domain : (utf8 "HasteBoots consumed field bytes v1").head? = some 72 := by
    unfold utf8
    decide
  have first := congrArg List.head? same
  rw [List.head?_append, domain] at first
  change some (72 : Byte) = some (⟨frame.kind.val, by omega⟩ : Byte) at first
  have value := congrArg Fin.val (Option.some.inj first)
  have bound := frame.kind.isLt
  change 72 = frame.kind.val at value
  omega

end FormalProof4FHE.HasteBoots.NativeTranscript
