module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
@[expose] public section

/-! Computed batch responses are codewords of their original message lanes.
The constructor fixes symbol width and polynomial degree independently of the
number of random-test rows. Primitive-root correctness remains a backend premise;
no supplied encoded-response or encoder-correctness certificate is used. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchResponseMeaning
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables Stored encoding logSize description)
open NativeUsizeMessage (Usize)
open NativeFieldRepresentation (GoldWord goldValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def Lane (ctx : Context) (work : Prepared) (words : List GoldWord) (lane : ℕ) :=
  NativeGoldResponseMeaning.laneWord (encoding ctx.parameters.code work.planRoot) words lane

theorem lane_value (ctx : Context) (work : Prepared) (words : List GoldWord) (lane : ℕ)
    (symbol : Fin (2^(logSize ctx.parameters.code))) (component : Fin ctx.parameters.code.blockWidth.val) :
    Lane ctx work words lane symbol component = NativeGoldColumnChecks.view words
      (lane*(2^(logSize ctx.parameters.code)*ctx.parameters.code.blockWidth.val)+symbol.val*ctx.parameters.code.blockWidth.val+component.val) := by
  change goldValue (words[lane*(2^(logSize ctx.parameters.code)*ctx.parameters.code.blockWidth.val)+(finProdFinEquiv (symbol,component)).val]?.getD 0) = _
  rw [finProdFinEquiv_apply_val]
  unfold NativeGoldColumnChecks.view
  congr 3; ring

def Domain (ctx : Context) (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :=
  NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) primitive

theorem prepared_geometry (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    NativeBrakedownParameters.build description ctx.parameters = some work.geometry := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  exact (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).1

theorem prepared_test (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    ∀ lane < work.width,
      Lane ctx work work.test lane = BlockEncoder.encode (Domain ctx primitive)
        (NativeGoldRowMeaning.coefficients (encoding ctx.parameters.code work.planRoot) ctx.parameters.code.messageBlocks.val
          ((ctx.opening.test.val.drop (lane*ctx.parameters.code.messageLength.val)).take ctx.parameters.code.messageLength.val)) ∧
      Lane ctx work work.test lane ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,_,_,encoded,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  exact NativeGoldBlockCodeMeaning.response_lanes constructorTables message block blowup ctx.parameters.code constructed planRoot _ _ _ encoded primitive

/-- Every original response has its computed encoded vector at the same index;
all lanes are interpreted in the retained code's domain. -/
theorem prepared_evaluation (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (index : Fin work.evaluations.length) :
    ∃ original : NativeLookupRequestWire.Row, ctx.opening.evaluations.val[index.val]? = some original ∧
      ∀ lane < work.width,
        Lane ctx work (work.evaluations.get index) lane = BlockEncoder.encode (Domain ctx primitive)
          (NativeGoldRowMeaning.coefficients (encoding ctx.parameters.code work.planRoot) ctx.parameters.code.messageBlocks.val
            ((original.val.drop (lane*ctx.parameters.code.messageLength.val)).take ctx.parameters.code.messageLength.val)) ∧
        Lane ctx work (work.evaluations.get index) lane ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,_,_,_,encoded,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  have paired := NativeGoldBatchPcsProgram.encodeAll_spec ctx.parameters planRoot ctx.opening.evaluations.val evaluations encoded
  have bound : index.val < ctx.opening.evaluations.val.length := by rw [paired.length_eq]; exact index.isLt
  refine ⟨ctx.opening.evaluations.val[index.val],List.getElem?_eq_getElem bound,?_⟩
  exact NativeGoldBlockCodeMeaning.response_lanes constructorTables message block blowup ctx.parameters.code constructed planRoot _ _ _
    (paired.get bound index.isLt) primitive

/-- The actual zip has the original response counts, so every checked group
has coded lanes; duplicate left-prefix groups need no extra authentication. -/
theorem prepared_groups (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    ∀ response ∈ work.groups, ∀ lane < work.width,
      Lane ctx work response.2 lane ∈ BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val := by
  intro response member lane bound
  have present : response.2 ∈ work.evaluations := List.of_mem_zip member |>.2
  obtain ⟨index,same⟩ := List.mem_iff_get.mp present
  obtain ⟨original,_,coded⟩ := prepared_evaluation ctx world work executed constructorTables message block blowup constructed primitive index
  rw [← same]
  exact (coded lane bound).2

theorem height_power (exponent : ℕ) : NativeBrakedownParameters.height (2^exponent) = exponent := by
  have upper := NativeBrakedownParameters.height_minimal (2^exponent) exponent (by rfl)
  have lower := NativeBrakedownParameters.leaves_cover (2^exponent) (by positivity)
  by_contra different
  have smaller : NativeBrakedownParameters.height (2^exponent) < exponent := by omega
  have strict := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) smaller
  omega

/-- Actual successful preparation and the retained constructor identify the
flat response address, symbol width and Merkle height with the polynomial code. -/
theorem prepared_layout (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code) :
    work.geometry.blocks = 2^(logSize ctx.parameters.code) ∧
      work.geometry.blockWidth = ctx.parameters.code.blockWidth.val ∧
      work.geometry.stride = 2^(logSize ctx.parameters.code)*ctx.parameters.code.blockWidth.val ∧
      work.geometry.height = logSize ctx.parameters.code := by
  have sizes := NativeBrakedownParameters.computed_sizes description ctx.parameters work.geometry (prepared_geometry ctx world work executed)
  have blocks : work.geometry.blocks = 2^(logSize ctx.parameters.code) := sizes.2.1.trans (NativeGoldBlockCodeMeaning.constructor_log constructorTables message block blowup ctx.parameters.code constructed).2
  have width : work.geometry.blockWidth = ctx.parameters.code.blockWidth.val := sizes.2.2.1
  exact ⟨blocks,width,by rw [sizes.2.2.2.2.1,blocks,width],by rw [sizes.2.2.2.2.2.2.2.1,blocks,height_power]⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchResponseMeaning
