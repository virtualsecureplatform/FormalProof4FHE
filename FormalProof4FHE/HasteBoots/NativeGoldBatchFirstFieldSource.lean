module
public import FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
public import FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedSource
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldColumnLaw
@[expose] public section

/-! Recover from a later column history the source chosen just before the
same field stream's first positive read. This does not replace the source
by a later hash log or choose it from future accepted work. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFirstFieldSource
open InputIndexedOracle (Input World)
open NativeTranscript (Observation Execution)
open NativeRootMessage (Digest)
open NativeGoldBatchFieldInputView (View)
open NativeRootFamilySourceSelection (Log)
open NativeGoldColumnAuthentication (encoding)
noncomputable section

def input (field : View) : Input := TranscriptFrame.encodeMany field.frames

def recover (dummy : Digest) (history : List Observation) (field : View) : Option Log :=
  (CausalFirstStreamPrefix.recover (input field) history).map (fun before => NativeGoldBatchSelectedSource.log dummy before field)

theorem recover_none (dummy : Digest) (history : List Observation) (field : View) :
    recover dummy history field = none ↔ CausalStreamExposure.seen history (input field) = false := by
  simp only [recover,Option.map_eq_none_iff,CausalFirstStreamPrefix.recover_none]

theorem recover_exists (dummy : Digest) (history : List Observation) (field : View)
    (seen : CausalStreamExposure.seen history (input field) = true) : ∃ sourceLog, recover dummy history field = some sourceLog := by
  cases found : recover dummy history field with
  | none =>
    have unseen := (recover_none dummy history field).mp found
    rw [seen] at unseen
    contradiction
  | some sourceLog => exact ⟨sourceLog,rfl⟩

theorem recover_at (dummy : Digest) (before after : List Observation) (field : View) (offset : ℕ) (values : Input)
    (unseen : CausalStreamExposure.seen before (input field) = false) (positive : values ≠ []) :
    recover dummy (before++ .output (input field) offset values :: after) field = some (NativeGoldBatchSelectedSource.log dummy before field) := by
  unfold recover
  rw [CausalFirstStreamPrefix.recover_at _ _ _ _ unseen (by simp [CausalStreamExposure.touches,List.length_pos_iff,positive])]
  rfl

theorem recover_append (dummy : Digest) (before after : List Observation) (field : View) (sourceLog : Log)
    (found : recover dummy before field = some sourceLog) : recover dummy (before++after) field = some sourceLog := by
  obtain ⟨prefixLog,first,equal⟩ := Option.map_eq_some_iff.mp found
  simp only [recover,CausalFirstStreamPrefix.recover_append _ before after prefixLog first,Option.map_some,equal]

theorem recover_sound (dummy : Digest) (history : List Observation) (field : View) (sourceLog : Log)
    (found : recover dummy history field = some sourceLog) :
    ∃ before offset values after, CausalStreamExposure.seen before (input field) = false ∧ values ≠ [] ∧
      history = before++ .output (input field) offset values :: after ∧ sourceLog = NativeGoldBatchSelectedSource.log dummy before field := by
  obtain ⟨before,first,equal⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨unseen,offset,values,after,positive,split⟩ := CausalFirstStreamPrefix.recover_sound _ history before first
  exact ⟨before,offset,values,after,unseen,positive,split,equal.symm⟩

/-- Snapshot membership is derived from the recovered first-read prefix;
no checkpoint or common-log certificate is supplied. -/
theorem recover_snapshot (dummy : Digest) (history : List Observation) (field : View)
    (parsed : NativeGoldBatchFieldInputView.parse (input field) = some field) (sourceLog : Log)
    (found : recover dummy history field = some sourceLog) :
    ∀ index : NativeMerkleShapeFamily.Height, ⟨(field.data.context,index),⟨field.data.root,sourceLog⟩⟩ ∈
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints := by
  obtain ⟨before,offset,values,after,_,positive,split,same⟩ := recover_sound dummy history field sourceLog found
  rw [split,same]
  exact NativeGoldBatchSelectedSource.selected_snapshot dummy before after _ field parsed offset values positive

/-- The strict linked-column parser supplies the same canonical field input. -/
theorem linked_field_parsed (columnInput : Input) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse columnInput = some decoded) :
    NativeGoldBatchFieldInputView.parse (input decoded.field) = some decoded.field := by
  obtain ⟨column,_,linked⟩ := Option.bind_eq_some_iff.mp parsed
  have field := (NativeGoldBatchChallengeLink.readColumn_sound column decoded linked).2.2.1
  have same := (NativeGoldBatchFieldInputView.parse_sound _ decoded.field field (fun _ => 0)).1
  rw [NativeGoldBatchFieldInputView.phase_input] at same
  change input decoded.field = _ at same
  rw [same]
  exact field

/-- Posterior refinement by the actual auxiliary field collector retains
exactly the source recovered from the selecting column history. -/
theorem recover_after_collect {A : Type} (past : World → Execution A) (profile : Digest) (fuel : ℕ)
    (decoded : NativeGoldBatchChallengeLink.View) (world : World) (dummy : Digest) (sourceLog : Log)
    (found : recover dummy (past world).run.2 decoded.field = some sourceLog) :
    recover dummy (NativeGoldBatchFieldColumnLaw.extended past profile fuel decoded world).run.2 decoded.field = some sourceLog := by
  rw [NativeGoldBatchFieldColumnLaw.run_extended]
  exact recover_append dummy _ _ decoded.field sourceLog found
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFirstFieldSource
