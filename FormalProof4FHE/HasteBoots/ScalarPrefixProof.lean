module
public import FormalProof4FHE.HasteBoots.ScalarTranscriptPrefix
public import FormalProof4FHE.HasteBoots.NativeScalarBatchRoundPacket
@[expose] public section

/-! Transpose recovered original round rows into native per-equation
certificates. Unserialized future rows reuse the selected row; all serialized
rows remain exact. Native preflight still checks the completed proof. -/
namespace FormalProof4FHE.HasteBoots.ScalarPrefixProof
open NativeScalarBatchWire (Message RoundPacket Statement)
open NativeScalarBatchPreflight (Proof Instance)
open NativeUsizeMessage (Usize)

/-- The raw matrix layout used by native certificates. -/
def matrixProof {rounds equations : ℕ} (matrix : Fin rounds → Fin equations → Message)
    (roundFits : rounds < 2^64) (equationFits : equations < 2^64) : Proof :=
  ⟨List.ofFn (fun equation => (⟨List.ofFn (fun round => matrix round equation),by simpa using roundFits⟩ : Instance)),
    by simpa using equationFits⟩

private theorem collect_rows (round : ℕ) (instances : List Instance) (messages : List Message)
    (getters : List.Forall₂ (fun certificate message => certificate.val[round]? = some message) instances messages) :
    NativeScalarBatchRoundPacket.collect round instances = some messages := by
  induction getters with
  | nil => rfl
  | @cons certificate message instances messages getter tail ih =>
    simp only [NativeScalarBatchRoundPacket.collect,getter,Option.bind_some,ih,Option.map_some]

/-- Transposition preserves each raw row, including noncanonical field words. -/
theorem matrix_collect {rounds equations : ℕ} (matrix : Fin rounds → Fin equations → Message)
    (roundFits : rounds < 2^64) (equationFits : equations < 2^64) (round : Fin rounds) :
    NativeScalarBatchRoundPacket.collect round.val (matrixProof matrix roundFits equationFits).val =
      some (List.ofFn (matrix round)) := by
  apply collect_rows
  apply List.forall₂_iff_get.mpr
  constructor
  · simp [matrixProof]
  · intro index leftBound rightBound
    simp only [matrixProof,List.get_eq_getElem,List.getElem_ofFn]
    rw [List.getElem?_eq_getElem (by simp)]
    simp

def rowAt (view : ScalarTranscriptPrefix.View) (round : ℕ) : RoundPacket :=
  ((view.history.rounds.map Prod.fst)[round]?).getD view.packet

theorem rowAt_prior (view : ScalarTranscriptPrefix.View) (index : ℕ) (pair : RoundPacket × InputIndexedOracle.Input)
    (found : view.history.rounds[index]? = some pair) : rowAt view index = pair.1 := by
  simp only [rowAt,List.getElem?_map,found,Option.map_some,Option.getD_some]

theorem rowAt_current (view : ScalarTranscriptPrefix.View) : rowAt view view.history.rounds.length = view.packet := by
  simp [rowAt]

/-- Reconstruction uses the statement's original dimensions. Reusing the
selected packet only fills the unseen suffix. Missing original equation rows
or failed native preflight reject reconstruction. -/
def reconstruct (view : ScalarTranscriptPrefix.View) : Option Proof := do
  let first ← view.history.statement.infos.val.head?
  if widths : ∀ round : Fin first.numVariables.val,
      (rowAt view round.val).messages.val.length = view.history.statement.infos.val.length then
    let proof := matrixProof
      (fun round equation => (rowAt view round.val).messages.val[equation.val]'(by rw [widths round]; exact equation.isLt))
      first.numVariables.isLt view.history.statement.infos.property
    if NativeScalarBatchPreflight.proofShape view.history.statement proof &&
        NativeScalarBatchPreflight.dimensions view.history.statement &&
        decide (view.history.rounds.map (fun pair => pair.1.round.val) = List.range view.history.rounds.length ∧
          view.packet.round.val = view.history.rounds.length ∧ view.packet.round.val < first.numVariables.val) then some proof else none
  else none

/-- Recovered certificates pass the actual native guards; these are checked
facts about the synthesized proof, not caller-supplied shape certificates. -/
theorem reconstruct_preflight (view : ScalarTranscriptPrefix.View) (proof : Proof)
    (built : reconstruct view = some proof) :
    NativeScalarBatchPreflight.proofShape view.history.statement proof = true ∧
      NativeScalarBatchPreflight.dimensions view.history.statement = true := by
  unfold reconstruct at built
  obtain ⟨first,_,built⟩ := Option.bind_eq_some_iff.mp built
  dsimp only at built
  split at built
  next widths =>
    split at built
    next guards =>
      cases Option.some.inj built
      exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp guards).1
    next => contradiction
  next => contradiction

/-- Every native round getter in the reconstructed proof returns the exact
recovered row. No field normalization or default message is introduced. -/
theorem reconstruct_collect (view : ScalarTranscriptPrefix.View) (proof : Proof)
    (built : reconstruct view = some proof) (first : NativeScalarBatchWire.Info)
    (head : view.history.statement.infos.val.head? = some first) (round : Fin first.numVariables.val) :
    NativeScalarBatchRoundPacket.collect round.val proof.val = some (rowAt view round.val).messages.val := by
  unfold reconstruct at built
  simp only [head,Option.bind_eq_bind,Option.bind_some] at built
  split at built
  next widths =>
    split at built
    next guards =>
      cases Option.some.inj built
      have native := matrix_collect
        (fun r e => (rowAt view r.val).messages.val[e.val]'(by rw [widths r]; exact e.isLt))
        first.numVariables.isLt view.history.statement.infos.property round
      have restored : List.ofFn (fun e : Fin view.history.statement.infos.val.length =>
          (rowAt view round.val).messages.val[e.val]'(by rw [widths round]; exact e.isLt)) =
            (rowAt view round.val).messages.val := by
        apply List.ext_getElem
        · simp [widths round]
        · intro index leftBound rightBound
          simp
      rw [restored] at native
      exact native
    next => contradiction
  next => contradiction

/-- Original round ordinals are checked along with native preflight. -/
theorem reconstruct_ordinals (view : ScalarTranscriptPrefix.View) (proof : Proof)
    (built : reconstruct view = some proof) (first : NativeScalarBatchWire.Info)
    (head : view.history.statement.infos.val.head? = some first) :
    view.history.rounds.map (fun pair => pair.1.round.val) = List.range view.history.rounds.length ∧
      view.packet.round.val = view.history.rounds.length ∧ view.packet.round.val < first.numVariables.val := by
  unfold reconstruct at built
  simp only [head,Option.bind_eq_bind,Option.bind_some] at built
  split at built
  next widths =>
    split at built
    next guards => exact of_decide_eq_true (Bool.and_eq_true_iff.mp guards).2
    next => contradiction
  next => contradiction

/-- The selected packet is the actual original native getter's result. -/
theorem reconstruct_current (view : ScalarTranscriptPrefix.View) (proof : Proof)
    (built : reconstruct view = some proof) (first : NativeScalarBatchWire.Info)
    (head : view.history.statement.infos.val.head? = some first) :
    NativeScalarBatchRoundPacket.packet view.packet.round proof = some view.packet := by
  have ordinal := reconstruct_ordinals view proof built first head
  have collected := reconstruct_collect view proof built first head ⟨view.packet.round.val,ordinal.2.2⟩
  dsimp only at collected
  rw [ordinal.2.1,rowAt_current] at collected
  unfold NativeScalarBatchRoundPacket.packet
  rw [ordinal.2.1,collected,Option.bind_some,dite_eq_left view.packet.messages.property]

/-- Preceding packets are also original native getters, in their checked order. -/
theorem reconstruct_prior (view : ScalarTranscriptPrefix.View) (proof : Proof)
    (built : reconstruct view = some proof) (first : NativeScalarBatchWire.Info)
    (head : view.history.statement.infos.val.head? = some first)
    (index : ℕ) (pair : RoundPacket × InputIndexedOracle.Input)
    (found : view.history.rounds[index]? = some pair) :
    NativeScalarBatchRoundPacket.packet pair.1.round proof = some pair.1 := by
  have ordinal := reconstruct_ordinals view proof built first head
  have indexBound := (List.getElem?_eq_some_iff.mp found).1
  have order := congrArg (fun rows => rows[index]?) ordinal.1
  simp only [List.getElem?_map,found,Option.map_some,List.getElem?_range indexBound] at order
  have roundEq := Option.some.inj order
  have bound : index < first.numVariables.val := by omega
  have collected := reconstruct_collect view proof built first head ⟨index,bound⟩
  dsimp only at collected
  rw [rowAt_prior view index pair found] at collected
  unfold NativeScalarBatchRoundPacket.packet
  rw [roundEq,collected,Option.bind_some,dite_eq_left pair.1.messages.property]

end FormalProof4FHE.HasteBoots.ScalarPrefixProof
