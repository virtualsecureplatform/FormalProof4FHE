module
public import FormalProof4FHE.HasteBoots.SingleOpeningSamplingReceipt
public import FormalProof4FHE.HasteBoots.NativeFieldMatrixLaw
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
@[expose] public section

/-! The exact native single-opening collector gives the rectangular random
matrix. Its joint conditional law preserves rejection/abort completion mass.
Causal first positive exposure derives freshness from the full mixed history;
global event coverage and lifetime charge composition remain separate. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningRandomLaw
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeFields (Goldilocks goldilocksModulus)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (Input World law)
open SingleOpeningSamplingReceipt (Receipt)
open SingleOpeningRectangularData (Row Weights rowEquiv)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section
variable {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}

def phase (receipt : Receipt ctx world work sample) := NativePrimeRequest.phase goldilocksModulus receipt.bound .vector
  NativeGoldPcsPrelude.randomLabel work.geometry.randomCount

theorem count (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    work.geometry.randomCount.val = work.geometry.rows*ctx.parameters.width.val := by
  have spec := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (SingleOpeningRectangularData.geometry ctx world work prepared)
  rw [spec.computed]
  rfl

theorem prepared_values (receipt : Receipt ctx world work sample) :
    NativeFieldVectorLaw.values goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val (phase receipt) world =
      some (fun index => ((receipt.state.values[index.val]?.getD 0 : ℕ) : Goldilocks)) :=
  NativeFieldVectorLaw.finished_values goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val
    (NativePrimeRequest.prepare receipt.bound .vector) NativeGoldPcsPrelude.randomLabel world receipt.state receipt.next receipt.field

theorem prepared_word (receipt : Receipt ctx world work sample) (index : Fin work.geometry.randomCount.val) :
    NativeGoldColumnChecks.view work.random index.val = ((receipt.state.values[index.val]?.getD 0 : ℕ) : Goldilocks) := by
  have facts := NativePrimeRequest.finished_gold_exact ctx.fieldFuel receipt.bound .vector NativeGoldPcsPrelude.randomLabel
    work.geometry.randomCount world receipt.state receipt.next receipt.field
  have bounded : index.val < receipt.state.values.length := by rw [facts.1]; exact index.isLt
  have exactWord := (facts.2 receipt.state.values[index.val] (List.getElem_mem bounded)).1
  rw [receipt.random]
  simp only [NativeGoldColumnChecks.view,NativeGoldPcsColumns.random,List.getElem?_map,
    List.getElem?_eq_getElem bounded,Option.map_some,Option.getD_some]
  change ((NativePrimeRequest.goldWord receipt.state.values[index.val]).val : Goldilocks) = _
  rw [exactWord]

def matrix (receipt : Receipt ctx world work sample) (other : World) :=
  NativeFieldMatrixLaw.values goldilocksModulus ctx.fieldFuel ctx.parameters.width.val work.geometry.rows (phase receipt) other

theorem prepared_matrix (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    matrix receipt world = some (fun lane : Fin ctx.parameters.width.val => fun row : Fin work.geometry.rows =>
      NativeGoldColumnChecks.view work.random (lane.val*work.geometry.rows+row.val)) := by
  have drawn : NativeFieldVectorLaw.values goldilocksModulus ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) (phase receipt) world =
      some (fun index => ((receipt.state.values[index.val]?.getD 0 : ℕ) : Goldilocks)) := by
    rw [← count prepared]
    exact prepared_values receipt
  unfold matrix NativeFieldMatrixLaw.values
  rw [drawn,Option.map_some]
  apply congrArg some
  funext lane row
  rw [NativeFieldMatrixLaw.reshape_apply]
  have bounded : lane.val*work.geometry.rows+row.val < work.geometry.randomCount.val := by
    rw [count prepared]
    have a := lane.isLt; have b := row.isLt
    nlinarith
  exact (prepared_word receipt ⟨_,bounded⟩).symm

def reindex (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    (Fin ctx.parameters.width.val → Fin work.geometry.rows → Goldilocks) ≃
      (Fin ctx.parameters.width.val → Row ctx → Goldilocks) :=
  Equiv.piCongrRight (fun _ => Equiv.arrowCongr (rowEquiv ctx world work prepared).symm (Equiv.refl Goldilocks))

def rectangular (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (other : World) :=
  (matrix receipt other).map (reindex prepared)

theorem prepared_rectangular (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    rectangular receipt prepared world = some (Weights ctx world work prepared work.random) := by
  unfold rectangular
  rw [prepared_matrix receipt prepared,Option.map_some]
  rfl

theorem uniform_reindex (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (event : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → Prop) :
    Pr{let values ← $ᵗ (Fin ctx.parameters.width.val → Fin work.geometry.rows → Goldilocks)}[event (reindex prepared values)] =
      Pr{let values ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[event values] :=
  SampleableType.prEvent_uniformSample_equiv (reindex prepared) event

/-- Exact joint matrix law, retaining the real shared-candidate-budget
completion factor. Completed requests are not renormalized to probability one. -/
theorem conditional_uniform {Cfg Payload P : Type} (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) (phase receipt).pending.input (phase receipt).consumed.length)
    (event : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (rectangular receipt prepared other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) *
        Pr{let values ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[event values] := by
  have result := NativeFieldMatrixLaw.conditional_uniform replay world enc dummy shape state hashStart goldilocksModulus (by decide +kernel)
    ctx.fieldFuel ctx.parameters.width.val work.geometry.rows (phase receipt) fresh (fun values => event (reindex prepared values))
  rw [uniform_reindex] at result
  simpa only [rectangular,matrix,Option.elim_map,Function.comp_def] using result

/-- All analysis prefixes of this same native stream are covered. There is no
native retry cap or assumption that the collector returns. -/
theorem eventual_le_uniform {Cfg Payload P : Type} (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) (phase receipt).pending.input (phase receipt).consumed.length)
    (event : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, ((NativeFieldMatrixLaw.values goldilocksModulus fuel ctx.parameters.width.val work.geometry.rows (phase receipt) other).map
        (reindex prepared)).elim False event} ≤
        Pr{let values ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[event values] := by
  have result := NativeFieldMatrixLaw.eventual_le_uniform replay world enc dummy shape state hashStart goldilocksModulus (by decide +kernel)
    ctx.parameters.width.val work.geometry.rows (phase receipt) fresh (fun values => event (reindex prepared values))
  rw [uniform_reindex] at result
  simpa only [Option.elim_map,Function.comp_def] using result

theorem first_read_uniform {Cfg Payload S A : Type} (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (phase receipt).pending.input)
    (event : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (rectangular receipt prepared other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) *
        Pr{let values ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[event values] :=
  conditional_uniform receipt prepared replay enc dummy shape state hashStart
    (CausalStreamExposure.firstRead_fresh step (past world).run _ selected world (phase receipt).consumed.length) event

theorem first_read_eventual_le_uniform {Cfg Payload S A : Type} (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (phase receipt).pending.input)
    (event : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, ((NativeFieldMatrixLaw.values goldilocksModulus fuel ctx.parameters.width.val work.geometry.rows (phase receipt) other).map
        (reindex prepared)).elim False event} ≤
        Pr{let values ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[event values] :=
  eventual_le_uniform receipt prepared replay enc dummy shape state hashStart
    (CausalStreamExposure.firstRead_fresh step (past world).run _ selected world (phase receipt).consumed.length) event

end
end FormalProof4FHE.HasteBoots.SingleOpeningRandomLaw
