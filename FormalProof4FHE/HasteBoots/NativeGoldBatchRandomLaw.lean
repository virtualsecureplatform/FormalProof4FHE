module
public import FormalProof4FHE.HasteBoots.NativeFieldMatrixLaw
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularChecks
@[expose] public section

/-! The sampler matrix law is connected to the checked native batch's actual
Goldilocks random array and its one rectangular row reindexing. The fresh-tail
premise still has to be supplied by production first-exposure/causal lineage. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRandomLaw
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (description)
open NativeGoldBatchLinearEquations (Weights)
open NativeGoldBatchRectangularChecks (lane)
open NativeFields (Goldilocks goldilocksModulus)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (Input World)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def phase (work : Prepared) := NativePrimeRequest.phase goldilocksModulus work.binding.parent .vector
  NativeGoldBatchPrelude.randomLabel work.geometry.randomCount

theorem prepared_request (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ∃ next, (run (NativeGoldBatchPrelude.sample work.geometry ctx.fieldFuel work.binding.parent) world).run.1 = .finished work.state next := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  exact ⟨next,(NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.2.2⟩

theorem prepared_count (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    work.geometry.randomCount.val = work.geometry.rows*ctx.parameters.width.val := by
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  rw [spec.computed]
  rfl

theorem prepared_values (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    NativeFieldVectorLaw.values goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val (phase work) world =
      some (fun index => ((work.state.values[index.val]?.getD 0 : ℕ) : Goldilocks)) := by
  obtain ⟨next,finished⟩ := prepared_request ctx world work prepared
  exact NativeFieldVectorLaw.finished_values goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val
    (NativePrimeRequest.prepare work.binding.parent .vector) NativeGoldBatchPrelude.randomLabel world work.state next finished

theorem prepared_word (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.geometry.randomCount.val) :
    NativeGoldColumnChecks.view work.random index.val = ((work.state.values[index.val]?.getD 0 : ℕ) : Goldilocks) := by
  obtain ⟨next,finished⟩ := prepared_request ctx world work prepared
  have facts := NativePrimeRequest.finished_gold_exact ctx.fieldFuel work.binding.parent .vector NativeGoldBatchPrelude.randomLabel work.geometry.randomCount world work.state next finished
  have bounded : index.val < work.state.values.length := by rw [facts.1]; exact index.isLt
  have exactWord := (facts.2 work.state.values[index.val] (List.getElem_mem bounded)).1
  simp only [NativeGoldColumnChecks.view,NativeGoldBatchPcsProgram.Prepared.random,List.getElem?_map,
    List.getElem?_eq_getElem bounded,Option.map_some,Option.getD_some]
  change ((NativePrimeRequest.goldWord work.state.values[index.val]).val : Goldilocks) = _
  rw [exactWord]

def matrix (ctx : Context) (work : Prepared) (world : World) :=
  NativeFieldMatrixLaw.values goldilocksModulus ctx.fieldFuel ctx.parameters.width.val work.geometry.rows (phase work) world

/-- The native random array is exactly the matrix sampled by the derived
joint law, including the checked lane-major stride and raw-word conversion. -/
theorem prepared_matrix (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    matrix ctx work world = some (fun index row => Weights work work.random (lane ctx world work prepared index) row) := by
  have drawn : NativeFieldVectorLaw.values goldilocksModulus ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) (phase work) world =
      some (fun index => ((work.state.values[index.val]?.getD 0 : ℕ) : Goldilocks)) := by
    rw [← prepared_count ctx world work prepared]
    exact prepared_values ctx world work prepared
  unfold matrix NativeFieldMatrixLaw.values
  rw [drawn,Option.map_some]
  apply congrArg some
  funext index row
  rw [NativeFieldMatrixLaw.reshape_apply]
  have bounded : index.val*work.geometry.rows+row.val < work.geometry.randomCount.val := by
    rw [prepared_count ctx world work prepared]
    have a := index.isLt; have b := row.isLt
    nlinarith
  simpa only [Weights,lane,Fin.val_cast] using (prepared_word ctx world work prepared ⟨_,bounded⟩).symm

def reindex (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    (Fin ctx.parameters.width.val → Fin work.geometry.rows → Goldilocks) ≃
      (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks) :=
  Equiv.piCongrRight (fun _ => Equiv.arrowCongr (NativeGoldBatchRectangularWeights.rowEquiv ctx world work prepared).symm (Equiv.refl Goldilocks))

/-- The rectangular kernel's random matrix is a query-independent bijective
row reindexing of the same native collector result. -/
def rectangular (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (other : World) :=
  (matrix ctx work other).map (reindex ctx world work prepared)

theorem prepared_rectangular (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    rectangular ctx world work prepared world = some (NativeGoldBatchRectangularChecks.random ctx world work prepared) := by
  unfold rectangular
  rw [prepared_matrix ctx world work prepared,Option.map_some]
  rfl
/-- Uniformity of the whole matrix is preserved by the common source-row
bijection; no entrywise independence certificate is supplied. -/
theorem uniform_reindex (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (event : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks) → Prop) :
    Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → Fin work.geometry.rows → Goldilocks)}[event (reindex ctx world work prepared matrix)] =
      Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks)}[event matrix] :=
  SampleableType.prEvent_uniformSample_equiv (reindex ctx world work prepared) event

/-- Exact conditional native matrix law, with the actual shared-budget
completion mass retained. Causal lineage must establish fresh-tail eligibility. -/
theorem conditional_uniform {Cfg Payload P : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload) (dummy : NativeRootMessage.Digest)
    (shape : Cfg → BinaryTree.Skeleton) (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) (phase work).pending.input (phase work).consumed.length)
    (event : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks) → Prop) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | (rectangular ctx world work prepared other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) *
        Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks)}[event matrix] := by
  have result := NativeFieldMatrixLaw.conditional_uniform replay world enc dummy shape state hashStart goldilocksModulus (by decide +kernel)
    ctx.fieldFuel ctx.parameters.width.val work.geometry.rows (phase work) fresh (fun values => event (reindex ctx world work prepared values))
  rw [uniform_reindex] at result
  simpa only [rectangular,matrix,Option.elim_map,Function.comp_def] using result

/-- All analysis prefixes of this same native matrix request are included;
there is no native retry cap and no success-probability normalization. -/
theorem eventual_le_uniform {Cfg Payload P : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload) (dummy : NativeRootMessage.Digest)
    (shape : Cfg → BinaryTree.Skeleton) (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) (phase work).pending.input (phase work).consumed.length)
    (event : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks) → Prop) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, ((NativeFieldMatrixLaw.values goldilocksModulus fuel ctx.parameters.width.val work.geometry.rows (phase work) other).map
        (reindex ctx world work prepared)).elim False event} ≤
        Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks)}[event matrix] := by
  have result := NativeFieldMatrixLaw.eventual_le_uniform replay world enc dummy shape state hashStart goldilocksModulus (by decide +kernel)
    ctx.parameters.width.val work.geometry.rows (phase work) fresh (fun values => event (reindex ctx world work prepared values))
  rw [uniform_reindex] at result
  simpa only [Option.elim_map,Function.comp_def] using result

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRandomLaw
