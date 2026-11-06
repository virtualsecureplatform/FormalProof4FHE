module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchResponseMeaning
public import FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
public import FormalProof4FHE.HasteBoots.StructuredOpening
@[expose] public section

/-! Native flattened coordinate checks become linear checks on one immutable
available matrix. Test width and code-symbol width remain independent. This
is deterministic semantic transport, not a challenge-freshness or soundness
probability theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchLinearEquations
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize)
open NativeFieldRepresentation (GoldWord)
open NativeFields (Goldilocks)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open NativeGoldBatchResponseMeaning (Lane)
open NativeMerkleShapeFamily (height tag)
open OracleProgram (run)
open scoped BigOperators
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Weights (work : Prepared) (words : List GoldWord) (lane : Fin work.width) : Fin work.geometry.rows → Goldilocks :=
  fun row => NativeGoldColumnChecks.view words (lane.val*work.geometry.rows+row.val)

def Word (ctx : Context) (work : Prepared) (values : ℕ → ℕ → Goldilocks) :
    Fin (2^(logSize ctx.parameters.code)) → Fin work.geometry.rows → Fin ctx.parameters.code.blockWidth.val → Goldilocks :=
  fun symbol row component => values symbol.val (row.val*ctx.parameters.code.blockWidth.val+component.val)

/-- Vector equalities at a code symbol are exactly the native lane/coordinate
checks, with the actual prepared stride and symbol width. -/
theorem column_equations {Cfg : Type} {familyHeight : Cfg → ℕ} (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request familyHeight))
    (values : ℕ → ℕ → Goldilocks) (symbol : Fin (2^(logSize ctx.parameters.code)))
    (equations : NativeGoldBatchRawAvailability.Equations (NativeGoldBatchRawAvailability.view work requests) (values symbol.val) symbol.val) :
    ∀ response ∈ work.groups, ∀ lane : Fin work.width,
      StructuredOpening.combine (Weights work work.random lane) (Word ctx work values) symbol = Lane ctx work work.test lane symbol ∧
      StructuredOpening.combine (Weights work response.1 lane) (Word ctx work values) symbol = Lane ctx work response.2 lane symbol := by
  have layout := NativeGoldBatchResponseMeaning.prepared_layout ctx world work executed constructorTables message block blowup constructed
  intro response member lane
  have checked := equations response member lane.val lane.isLt
  dsimp only [NativeGoldBatchRawAvailability.view] at checked
  constructor
  · ext component
    have equal := (checked component.val (by rw [layout.2.1]; exact component.isLt)).1
    rw [NativeGoldBatchResponseMeaning.lane_value]
    simpa +instances only [NativeGoldBatchRawAvailability.view,StructuredOpening.combine,Weights,Word,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      layout.2.1,layout.2.2.1] using equal
  · ext component
    have equal := (checked component.val (by rw [layout.2.1]; exact component.isLt)).2
    rw [NativeGoldBatchResponseMeaning.lane_value]
    simpa +instances only [NativeGoldBatchRawAvailability.view,StructuredOpening.combine,Weights,Word,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      layout.2.1,layout.2.2.1] using equal

/-- One complete context/root checkpoint word, interpreted at the retained
code's symbols. Only actual sampled positions are used in the transport proof. -/
def Frozen (dummy context : Digest) (work : Prepared) (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest) :
    ℕ → ℕ → Goldilocks :=
  fun symbol => NativeGoldRawAvailability.frozenValue dummy height (tag context work) ⟨work.root,log⟩
    (Fin.ofNat (2^(height (tag context work))) symbol)

theorem source_combinations (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (history : List Observation) (source : NativeGoldBatchAnySourceRisk.HasSource dummy ctx work history world) :
    ∃ (context : Digest) (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request height))
      (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest),
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      NativeGoldBatchFamilyRequests.prepare context work = some requests ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests, ∃ bound : entry.2.position.val < 2^(logSize ctx.parameters.code),
        ∀ response ∈ work.groups, ∀ lane : Fin work.width,
          StructuredOpening.combine (Weights work work.random lane) (Word ctx work (Frozen dummy context work log)) ⟨entry.2.position.val,bound⟩ =
            Lane ctx work work.test lane ⟨entry.2.position.val,bound⟩ ∧
          StructuredOpening.combine (Weights work response.1 lane) (Word ctx work (Frozen dummy context work log)) ⟨entry.2.position.val,bound⟩ =
            Lane ctx work response.2 lane ⟨entry.2.position.val,bound⟩ := by
  obtain ⟨context,requests,log,hashed,computed,snapshots,checks⟩ := source
  refine ⟨context,requests,log,hashed,computed,snapshots,?_⟩
  have layout := NativeGoldBatchResponseMeaning.prepared_layout ctx world work executed constructorTables message block blowup constructed
  have sameHeight : height (tag context work) = logSize ctx.parameters.code :=
    (NativeMerkleShapeFamily.tag_height context ctx world work executed).trans layout.2.2.2
  have requestSpec := NativeGoldBatchRawRequests.prepare_spec height (tag context work) work requests computed
  intro entry member
  obtain ⟨inside,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (tag context work) work.root entry.1 entry.2 (requestSpec.2 entry member)
  have bounded : entry.2.position.val < 2^(logSize ctx.parameters.code) := by
    rw [same]
    simpa only [sameHeight] using inside
  refine ⟨bounded,?_⟩
  apply column_equations ctx world work executed constructorTables message block blowup constructed requests (Frozen dummy context work log) ⟨entry.2.position.val,bounded⟩
  have equations := (checks entry member).2
  have values : Frozen dummy context work log entry.2.position.val =
      NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position := by
    rw [same]
    unfold Frozen
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt inside
  rw [values]
  exact equations
/-- An actual accepted native run supplies its own availability and preparation
witnesses; only the shared global no-disagreement event is excluded. -/
theorem accepted_combinations {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (history : List Observation) (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history)) :
    ∃ (context : Digest) (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request height))
      (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest),
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      NativeGoldBatchFamilyRequests.prepare context work = some requests ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests, ∃ bound : entry.2.position.val < 2^(logSize ctx.parameters.code),
        ∀ response ∈ work.groups, ∀ lane : Fin work.width,
          StructuredOpening.combine (Weights work work.random lane) (Word ctx work (Frozen dummy context work log)) ⟨entry.2.position.val,bound⟩ =
            Lane ctx work work.test lane ⟨entry.2.position.val,bound⟩ ∧
          StructuredOpening.combine (Weights work response.1 lane) (Word ctx work (Frozen dummy context work log)) ⟨entry.2.position.val,bound⟩ =
            Lane ctx work response.2 lane ⟨entry.2.position.val,bound⟩ := by
  have source := NativeGoldBatchAnySourceRisk.accepted_has_source dummy world history truthful ctx choose fuel memory work accepted noDisagreement
  obtain ⟨_,completion,parent,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  exact source_combinations dummy ctx world work prepared constructorTables message block blowup constructed history source

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchLinearEquations
