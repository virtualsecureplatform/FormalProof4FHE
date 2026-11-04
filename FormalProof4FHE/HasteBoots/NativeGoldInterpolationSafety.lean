module

public import FormalProof4FHE.HasteBoots.NativeGoldInterpolation
public import FormalProof4FHE.HasteBoots.NativeInterpolationSafety
public import FormalProof4FHE.HasteBoots.NativeScalarBatchRoundPacket

@[expose] public section

/-!
# Native Goldilocks interpolation safety after the actual preflight

The raw representation theorem transports the field loop's totality back
to raw words. The nonzero-node hypotheses come from the literal native
preflight. Every matched message in an extracted round is therefore safe
for interpolation, with no caller-provided execution certificate.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldInterpolationSafety

open NativeFields NativeFieldWire NativeGoldExtensionArithmetic NativeExtensionFields
open NativeScalarBatchWire NativeScalarBatchPreflight

noncomputable section

theorem interpolate_safe (values : List Word) (point : Word) (positive : 0 < values.length)
    (nodes : nodesFrom (values.length - 1) NativeGoldLookup.zero = true) :
    ∃ value, NativeGoldInterpolation.interpolate values point = some value := by
  have nonzero : ∀ j, 0 < j → j ≤ values.length - 1 → (j : Goldilocks3) ≠ 0 := by
    simpa only [NativeGoldLookup.zero_value, zero_add] using (nodesFrom_iff _ _).mp nodes
  obtain ⟨value, success⟩ := NativeInterpolationSafety.interpolate_safe
    (values.map goldExtensionValue) (goldExtensionValue point)
    (by simpa only [List.length_map] using positive)
    (by simpa only [List.length_map] using nonzero)
  rw [← NativeGoldInterpolation.interpolate_value] at success
  cases executed : NativeGoldInterpolation.interpolate values point with
  | none => simp only [executed, Option.map_none] at success; contradiction
  | some result => exact ⟨result, rfl⟩

/-- Every known node returns the original raw received word, even when the
challenge or evaluation has a lazy representative. -/
theorem interpolate_at_node (values : List Word) (point : Word) (positive : 0 < values.length)
    (nodes : nodesFrom (values.length - 1) NativeGoldLookup.zero = true) (node : Fin values.length)
    (atNode : goldExtensionValue point = (node.val : Goldilocks3)) :
    NativeGoldInterpolation.interpolate values point = some values[node.val] := by
  have nonzero : ∀ j, 0 < j → j ≤ values.length - 1 → (j : Goldilocks3) ≠ 0 := by
    simpa only [NativeGoldLookup.zero_value, zero_add] using (nodesFrom_iff _ _).mp nodes
  have inside : node.val < values.length - 1 + 1 := by have bound := node.isLt; omega
  have matched := NativeInterpolationSafety.scan_at_node (values.length - 1) nonzero ⟨node.val, inside⟩
  have mapped := NativeInterpolationCore.scan_map NativeGoldInterpolation.arithmetic_hom point
    (values.length - 1) 0 ⟨NativeGoldLookup.zero, point, [point]⟩
  simp only [NativeInterpolationCore.mapScan, NativeGoldLookup.zero_value,
    List.map_cons, List.map_nil, atNode] at mapped
  rw [matched] at mapped
  have rawMatch : NativeInterpolationCore.scan NativeGoldInterpolation.arithmetic point
      (values.length - 1) 0 ⟨NativeGoldLookup.zero, point, [point]⟩ = .atNode node.val := by
    cases result : NativeInterpolationCore.scan NativeGoldInterpolation.arithmetic point
        (values.length - 1) 0 ⟨NativeGoldLookup.zero, point, [point]⟩ with
    | atNode index =>
      rw [result, NativeInterpolationCore.mapResult] at mapped
      exact congrArg NativeInterpolationCore.ScanResult.atNode
        (NativeInterpolationCore.ScanResult.atNode.inj mapped)
    | offNodes state =>
      rw [result, NativeInterpolationCore.mapResult] at mapped
      contradiction
  cases values with
  | nil => simp at positive
  | cons first rest =>
    change NativeInterpolationCore.interpolate NativeGoldInterpolation.arithmetic (first :: rest) point = _
    rw [NativeInterpolationCore.interpolate]
    simp only [show NativeGoldInterpolation.arithmetic.zero = NativeGoldLookup.zero from rfl]
    rw [rawMatch]
    exact List.getElem?_eq_getElem node.isLt

/-- A matched round message inherits its actual degree and node checks from
successful dimensions and the proved packet width. -/
theorem message_safe (statement : Statement) (accepted : dimensions statement = true)
    (info : Info) (member : info ∈ statement.infos.val) (message : Message)
    (width : message.evaluations.val.length = info.maxMultiplicands.val + 1) (point : Word) :
    ∃ value, NativeGoldInterpolation.interpolate message.evaluations.val point = some value := by
  have enough := NativeScalarBatchRoundPacket.first_two_safe statement accepted info member message width
  have nodeChecks : interpolationNodes statement = true := by
    rw [dimensions, Bool.and_eq_true] at accepted
    exact accepted.2
  change statement.infos.val.all (fun info => nodesFrom info.maxMultiplicands.val NativeGoldLookup.zero) = true at nodeChecks
  have nodes := (List.all_eq_true.mp nodeChecks) info member
  apply interpolate_safe message.evaluations.val point (by omega)
  simpa only [width, Nat.add_sub_cancel] using nodes

/-- All equations in one ordered round are safe at the common challenge. -/
theorem messages_safe (statement : Statement) (accepted : dimensions statement = true)
    (messages : List Message)
    (widths : List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1)
      statement.infos.val messages) (point : Word) :
    ∀ message ∈ messages, ∃ value, NativeGoldInterpolation.interpolate message.evaluations.val point = some value := by
  have paired : ∀ infos, List.Forall₂
      (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1) infos messages →
      (∀ info ∈ infos, info ∈ statement.infos.val) →
      ∀ message ∈ messages, ∃ value,
        NativeGoldInterpolation.interpolate message.evaluations.val point = some value := by
    clear widths
    intro infos related
    induction related with
    | nil => simp
    | @cons info message infos messages width related ih =>
      intro included entry member
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact message_safe statement accepted info (included info (by simp)) message width point
      · exact ih (fun info member => included info (by simp [member])) entry later
  exact paired statement.infos.val widths (fun _ member => member)

/-- Accepted proof shape/dimensions and an in-range round suffice for actual
packet extraction and all raw interpolation executions at any challenge. -/
theorem preflight_round_safe (statement : Statement) (proof : Proof)
    (round : NativeUsizeMessage.Usize) (first : Info)
    (shape : proofShape statement proof = true) (accepted : dimensions statement = true)
    (head : statement.infos.val.head? = some first) (inside : round.val < first.numVariables.val)
    (point : Word) :
    ∃ packet, NativeScalarBatchRoundPacket.packet round proof = some packet ∧
      packet.messages.val.length = statement.claims.val.length ∧
      ∀ message ∈ packet.messages.val, ∃ value,
        NativeGoldInterpolation.interpolate message.evaluations.val point = some value := by
  obtain ⟨packet, found, _, widths, count⟩ := NativeScalarBatchRoundPacket.packet_success
    statement proof round first shape accepted head inside
  exact ⟨packet, found, count, messages_safe statement accepted packet.messages.val widths point⟩

end

end FormalProof4FHE.HasteBoots.NativeGoldInterpolationSafety
