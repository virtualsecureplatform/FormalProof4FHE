module
public import FormalProof4FHE.HasteBoots.MixedWidthRequestSharedLookup
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthStagedSharedLookupSoundness
@[expose] public section

/-! Request-specific data is compiled to the shared job schedule. The trusted
compiler fixes each job's table, multiplicities, source slots and sampled pair.
The source tuple interpretation is fixed at the pre-pair source checkpoint.
Native byte/field/layout association and original-owner reuse remain separate. -/
open OracleSpec OracleComp BinaryTree Matrix
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.PaddedMixedWidthRequestSharedLookup
noncomputable section

def request {requests : ℕ} (repetitions : Fin requests → ℕ) (job : Fin (∑ i, repetitions i)) : Fin requests :=
  (finSigmaFinEquiv.symm job).1

theorem request_job {requests : ℕ} (repetitions : Fin requests → ℕ) (index : Fin requests)
    (repetition : Fin (repetitions index)) : request repetitions (finSigmaFinEquiv ⟨index,repetition⟩) = index :=
  congrArg Sigma.fst ((finSigmaFinEquiv (n := repetitions)).symm_apply_apply ⟨index,repetition⟩)

/-- Public request data and prover behavior. The compiler supplies the actual
sampled-pair projection; the behavior factory cannot replace it. -/
abbrev Parameters (F K Message Memory Cfg Input Digest SourceMemory HelperMemory : Type)
    (d padding c row count requests : ℕ) (widths sizes repetitions : Fin requests → ℕ) (mode : Mode)
    [Field F] [Field K] [Algebra F K] :=
  MixedWidthRequestSharedLookup.Parameters F K Message Memory Cfg Input Digest
    SourceMemory HelperMemory d padding c row count requests widths sizes repetitions mode

variable {F K Message Memory Cfg Input Digest SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}

/-- Compile request-major/repetition-minor jobs while preserving literal
request tables and original global source slots. Every used source remains
covered because every configured request has at least one repetition. -/
def toParameters
    (config : Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory d padding c row count requests widths sizes repetitions mode) :
    PaddedMixedWidthStagedSharedLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions)
      d padding c row count (∑ i, repetitions i)
      (fun job => widths (request repetitions job)) (fun job => sizes (request repetitions job)) mode where
  basis := config.basis
  shape := config.shape
  jobsPositive := lt_of_lt_of_le (config.repetitionsPositive ⟨0,config.requestsPositive⟩)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  slots job := config.slots (request repetitions job)
  coverage source := by
    obtain ⟨index,column,equal⟩ := config.coverage source
    refine ⟨finSigmaFinEquiv ⟨index,⟨0,config.repetitionsPositive index⟩⟩,?_⟩
    rw [request_job]
    exact ⟨column,equal⟩
  active job := config.active (request repetitions job)
  inactive job := config.inactive (request repetitions job)
  logicalShape job := config.logicalShape (request repetitions job)
  fullShape full job := config.fullShape full (request repetitions job)
  tables job := config.tables (request repetitions job)
  multiplicities first job := config.multiplicities first (request repetitions job)
  pairs := RequestLookupPairMiddle.pairs
  driver := config.driver
  sumDegree := config.sumDegree
  identityDegree := config.identityDegree

variable [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg}
  {g : Geometry c row count (∑ i, repetitions i)}

def columns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (first : PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (source : Fin count) : MatrixFold.Cube row → Fin (d + padding) → F :=
  QueryHighZeroPadding.source (g.extra (.inl source)) <|
  PackedQueryArity.table (g.sourceArity source)
    (SubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source))
      (word enc dummy heights (tag (.inl source)) ⟨first.1.1 source,first.2.hash.log⟩))

def tuples (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory d padding c row count requests widths sizes repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (first : PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    (index : Fin requests) → Fin (config.active index) → Fin (widths index) → F :=
  fun index => LookupPairArithmetic.activeTuples (config.logicalShape index)
    (fun column => LookupSourceFlattening.flatten config.shape (columns enc dummy domain capacity radius first (config.slots index column)))

omit [DecidableEq Input] in
/-- All shared jobs pass exactly when each sampled request vector passes on
its own original pre-pair tuple family and prefix-fixed multiplicities. -/
theorem allPass_iff (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory d padding c row count requests widths sizes repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (first : PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : RequestLookupPairMiddle.Emission K Digest HelperMemory repetitions ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    PaddedMixedWidthStagedSharedLookup.AllPass enc dummy (toParameters config) domain capacity radius first second ↔
      ∀ index, LookupPairVector.AllPass (tuples enc dummy config domain capacity radius first index) (config.tables index)
        (fun i => algebraMap F K (config.multiplicities first.1 index i)) (second.1.2.1 index) := by
  let pass := fun index : (index : Fin requests) × Fin (repetitions index) =>
    TupleLookupPair.Passes (tuples enc dummy config domain capacity radius first index.1) (config.tables index.1)
      (fun i => algebraMap F K (config.multiplicities first.1 index.1 i)) (LookupPairVector.forget (second.1.2.1 index.1 index.2))
  change (∀ job, pass (finSigmaFinEquiv.symm job)) ↔ ∀ index repetition, pass ⟨index,repetition⟩
  constructor
  · intro all index repetition
    exact (congrArg pass ((finSigmaFinEquiv (n := repetitions)).symm_apply_apply ⟨index,repetition⟩)).mp
      (all (finSigmaFinEquiv ⟨index,repetition⟩))
  · intro all job
    exact all (finSigmaFinEquiv.symm job).1 (finSigmaFinEquiv.symm job).2
end
end FormalProof4FHE.HasteBoots.PaddedMixedWidthRequestSharedLookup
