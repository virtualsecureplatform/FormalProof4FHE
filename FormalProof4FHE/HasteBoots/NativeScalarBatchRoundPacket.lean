module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchPreflight

@[expose] public section

/-!
# Ordered scalar round extraction from the checked native proof

Each certificate contributes exactly its round-th message. Invalid accesses
are explicit failures, never default messages. Accepted native preflight
proves every access and the packet's 64-bit count bound. The scalar batch
still requires its challenge/interpolation/terminal execution and soundness.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchRoundPacket

open NativeScalarBatchWire NativeScalarBatchPreflight
open NativeUsizeMessage (Usize)

def collect (round : ℕ) : List Instance → Option (List Message)
  | [] => some []
  | certificate :: tail => (certificate.val[round]?).bind (fun message =>
      (collect round tail).map (fun rest => message :: rest))

def packet (round : Usize) (proof : Proof) : Option RoundPacket :=
  (collect round.val proof.val).bind (fun messages =>
    if fits : messages.length < 2 ^ 64 then some ⟨round, ⟨messages, fits⟩⟩ else none)

/-- All instances have the trusted common variable count after preflight. -/
theorem uniform_rounds (infos : List Info) (instances : List Instance) (numVars : ℕ)
    (shapes : List.Forall₂ FitsInfo infos instances)
    (common : ∀ info ∈ infos, info.numVariables.val = numVars) :
    ∀ certificate ∈ instances, certificate.val.length = numVars := by
  induction shapes with
  | nil => simp
  | @cons info certificate infos instances fits tail ih =>
    intro entry member
    rcases List.mem_cons.mp member with same | later
    · subst entry
      exact fits.1.trans (common info (by simp))
    · exact ih (fun info member => common info (by simp [member])) entry later

/-- Collection preserves statement order and obtains exactly the validated
message width for every equation, without a degree premise on received polynomials. -/
theorem collect_success (infos : List Info) (instances : List Instance) (round numVars : ℕ)
    (shapes : List.Forall₂ FitsInfo infos instances)
    (common : ∀ info ∈ infos, info.numVariables.val = numVars) (inside : round < numVars) :
    ∃ messages, collect round instances = some messages ∧
      List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1) infos messages := by
  induction shapes with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons info certificate infos instances fits tail ih =>
    have bound : round < certificate.val.length := by rw [fits.1, common info (by simp)]; exact inside
    obtain ⟨rest, found, related⟩ := ih (fun info member => common info (by simp [member]))
    refine ⟨certificate.val[round] :: rest, ?_, .cons (fits.2.2 _ (List.getElem_mem bound)) related⟩
    simp only [collect, List.getElem?_eq_getElem bound, Option.bind_some, found, Option.map_some]

theorem packet_success (statement : Statement) (proof : Proof) (round : Usize) (first : Info)
    (shape : proofShape statement proof = true) (dimensions : NativeScalarBatchPreflight.dimensions statement = true)
    (head : statement.infos.val.head? = some first) (inside : round.val < first.numVariables.val) :
    ∃ result, packet round proof = some result ∧ result.round = round ∧
      List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1)
        statement.infos.val result.messages.val ∧
      result.messages.val.length = statement.claims.val.length := by
  obtain ⟨nativeFirst, firstHead, count, _, metadata⟩ := dimensions_success statement dimensions
  have same := Option.some.inj (head.symm.trans firstHead)
  subst nativeFirst
  have common : ∀ info ∈ statement.infos.val, info.numVariables.val = first.numVariables.val := by
    intro info member
    exact congrArg Fin.val (metadata info member).1
  have shapes := proofShape_iff statement proof |>.mp shape
  obtain ⟨messages, found, related⟩ := collect_success statement.infos.val proof.val round.val
    first.numVariables.val shapes common inside
  have fits : messages.length < 2 ^ 64 := by
    rw [← related.length_eq, shapes.length_eq]
    exact proof.property
  refine ⟨⟨round, ⟨messages, fits⟩⟩, ?_, rfl, related, related.length_eq.symm.trans count⟩
  rw [packet, found, Option.bind_some, dite_eq_left fits]

/-- The first-two-evaluation access is safe for every matched equation. -/
theorem first_two_safe (statement : Statement) (accepted : NativeScalarBatchPreflight.dimensions statement = true)
    (info : Info) (member : info ∈ statement.infos.val) (message : Message)
    (width : message.evaluations.val.length = info.maxMultiplicands.val + 1) :
    2 ≤ message.evaluations.val.length := by
  obtain ⟨_, _, _, _, metadata⟩ := dimensions_success statement accepted
  have positive := (metadata info member).2.1
  omega

end FormalProof4FHE.HasteBoots.NativeScalarBatchRoundPacket
