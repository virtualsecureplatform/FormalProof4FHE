module
public import FormalProof4FHE.HasteBoots.ScalarExecutionTranscript
@[expose] public section

/-! Completeness of the checked certificate reconstruction for well-shaped
original round rows. Every guard is discharged by native metadata and row
facts; no assumption that reconstruction succeeds is needed. -/
namespace FormalProof4FHE.HasteBoots.ScalarReconstructionCompleteness
open NativeScalarBatchWire (Statement Info Message RoundPacket)
open NativeScalarBatchPreflight (Proof)

/-- Padding future rows with a well-shaped selected row preserves actual
native preflight, even if future recurrence checks would differ. -/
theorem matrix_shape (statement : Statement) (first : Info)
    (head : statement.infos.val.head? = some first)
    (admitted : NativeScalarBatchPreflight.dimensions statement = true)
    (matrix : Fin first.numVariables.val → Fin statement.infos.val.length → Message)
    (width : ∀ round equation, (matrix round equation).evaluations.val.length =
      statement.infos.val[equation.val].maxMultiplicands.val + 1) :
    NativeScalarBatchPreflight.proofShape statement
      (ScalarPrefixProof.matrixProof matrix first.numVariables.isLt statement.infos.property) = true := by
  obtain ⟨native,nativeHead,_,_,metadata⟩ := NativeScalarBatchPreflight.dimensions_success statement admitted
  cases Option.some.inj (nativeHead.symm.trans head)
  apply (NativeScalarBatchPreflight.proofShape_iff statement _).mpr
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [ScalarPrefixProof.matrixProof],?_⟩
  intro index infoBound certificateBound
  have data := metadata _ (List.getElem_mem infoBound)
  simp only [List.get_eq_getElem,ScalarPrefixProof.matrixProof,List.getElem_ofFn,NativeScalarBatchPreflight.FitsInfo,List.length_ofFn]
  refine ⟨(congrArg Fin.val data.1).symm,?_,?_⟩
  · have bound : NativeFields.goldilocksModulus < 2^64 := by decide +kernel
    omega
  · intro message member
    obtain ⟨round,rfl⟩ := List.mem_ofFn.mp member
    exact width round ⟨index,infoBound⟩

theorem rowAt_member (view : ScalarTranscriptPrefix.View) (index : ℕ) :
    ScalarPrefixProof.rowAt view index ∈ view.history.rounds.map Prod.fst ++ [view.packet] := by
  unfold ScalarPrefixProof.rowAt
  cases found : (view.history.rounds.map Prod.fst)[index]? with
  | none => simp
  | some packet =>
    exact List.mem_append_left _ (List.mem_of_getElem? found)

/-- Original row shapes and consecutive ordinals imply successful checked
reconstruction. Future rows need no supplied messages or recurrence facts. -/
theorem reconstruct (view : ScalarTranscriptPrefix.View) (first : Info)
    (head : view.history.statement.infos.val.head? = some first)
    (admitted : NativeScalarBatchPreflight.dimensions view.history.statement = true)
    (ordinals : view.history.rounds.map (fun pair => pair.1.round.val) = List.range view.history.rounds.length)
    (current : view.packet.round.val = view.history.rounds.length)
    (inside : view.packet.round.val < first.numVariables.val)
    (rows : ∀ packet ∈ view.history.rounds.map Prod.fst ++ [view.packet],
      List.Forall₂ (fun info message => message.evaluations.val.length = info.maxMultiplicands.val + 1)
        view.history.statement.infos.val packet.messages.val) :
    ∃ proof : Proof, ScalarPrefixProof.reconstruct view = some proof := by
  have shapes := fun index => rows _ (rowAt_member view index)
  have widths : ∀ round : Fin first.numVariables.val,
      (ScalarPrefixProof.rowAt view round.val).messages.val.length = view.history.statement.infos.val.length :=
    fun round => (shapes round.val).length_eq.symm
  let matrix := fun (round : Fin first.numVariables.val) (equation : Fin view.history.statement.infos.val.length) =>
    (ScalarPrefixProof.rowAt view round.val).messages.val[equation.val]'(by rw [widths round]; exact equation.isLt)
  let proof := ScalarPrefixProof.matrixProof matrix first.numVariables.isLt view.history.statement.infos.property
  have shape : NativeScalarBatchPreflight.proofShape view.history.statement proof = true := by
    apply matrix_shape view.history.statement first head admitted matrix
    intro round equation
    have pair := (List.forall₂_iff_get.mp (shapes round.val)).2 equation.val equation.isLt
      (by rw [widths round]; exact equation.isLt)
    simpa only [matrix,List.get_eq_getElem] using pair
  refine ⟨proof,?_⟩
  simp only [ScalarPrefixProof.reconstruct,head,Option.bind_eq_bind,Option.bind_some,dite_eq_left widths]
  change (if NativeScalarBatchPreflight.proofShape view.history.statement proof &&
      NativeScalarBatchPreflight.dimensions view.history.statement &&
      decide (view.history.rounds.map (fun pair => pair.1.round.val) = List.range view.history.rounds.length ∧
        view.packet.round.val = view.history.rounds.length ∧ view.packet.round.val < first.numVariables.val)
    then some proof else none) = some proof
  have guarded : decide (view.history.rounds.map (fun pair => pair.1.round.val) = List.range view.history.rounds.length ∧
      view.packet.round.val = view.history.rounds.length ∧ view.packet.round.val < first.numVariables.val) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨ordinals,current,inside⟩
  simp only [shape,admitted,Bool.true_and,guarded,ite_true]

end FormalProof4FHE.HasteBoots.ScalarReconstructionCompleteness
