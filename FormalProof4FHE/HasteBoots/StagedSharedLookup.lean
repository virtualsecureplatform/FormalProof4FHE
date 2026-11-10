module
public import FormalProof4FHE.HasteBoots.SharedLookupPCSAlgebra
public import FormalProof4FHE.HasteBoots.StagedCommitmentException
@[expose] public section

/-! Source commitments precede pair/helper work; helper commitments precede
ordered EQ, one common scalar batch, computed terminal selection and grouped
PCS. Each job retains its own table and original registry slots. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.SharedLookupOpeningFamily
open FormalProof4FHE.HasteBoots.SharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.StagedSharedLookup
noncomputable section
abbrev Pair (K : Type) [Zero K] := K × {r : K // r ≠ 0}
def pairValues {K : Type} [Zero K] {jobs : ℕ} (pairs : Fin jobs → Pair K) : Fin jobs → K × K :=
  fun job => ((pairs job).1,(pairs job).2.val)
abbrev SourceEmission (count : ℕ) (Digest SourceMemory : Type) :=
  StagedHeterogeneousBatchOpening.SourceEmission (Fin count) Digest SourceMemory
abbrev HelperEmission (jobs : ℕ) (Digest HelperMemory : Type) :=
  StagedHeterogeneousBatchOpening.HelperEmission (Fin jobs) Digest HelperMemory
abbrev Emission (count jobs : ℕ) (Digest SourceMemory HelperMemory : Type) :=
  SharedLookupPCS.Emission count jobs Digest SourceMemory HelperMemory

/-- Public geometry, literal job tables, prefix-dependent prover behavior and
syntactic message degrees. No source truth, acceptance, hash safety, or random
challenge law is included in this data. -/
structure Parameters (F K Message Memory Cfg Input Digest SourceMemory HelperMemory : Type)
    (d padding c row count jobs : ℕ) (columns sizes : Fin jobs → ℕ) (mode : Mode)
    [Field F] [Field K] [Algebra F K] where
  basis : Module.Basis (Fin d) F K
  shape : d + padding = 2 ^ c
  jobsPositive : 0 < jobs
  slots : (job : Fin jobs) → Fin (columns job) → Fin count
  coverage : ∀ source, ∃ job column, slots job column = source
  active : Fin jobs → ℕ
  inactive : Fin jobs → ℕ
  logicalShape : ∀ job, active job + inactive job = 2 ^ (c + row)
  fullShape : mode = .full → ∀ job, active job = 2 ^ (c + row)
  tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F
  multiplicities : SourceEmission count Digest SourceMemory → (job : Fin jobs) → Fin (sizes job) → F
  pairs : HelperEmission jobs Digest HelperMemory → Fin jobs → Pair K
  driver : Emission count jobs Digest SourceMemory HelperMemory → Driver F K Message Memory Cfg Input Digest (d + padding) count jobs (c + row)
  sumDegree : ∀ emission points message job, ((driver emission).schedule.interpret points message (job,false)).natDegree ≤ 1
  identityDegree : ∀ emission points message job, ((driver emission).schedule.interpret points message (job,true)).natDegree ≤ degree mode

variable {F K L Message Memory Cfg Input Digest Response SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count jobs : ℕ} {columns sizes : Fin jobs → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count jobs → Cfg} {g : Geometry c row count jobs}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

abbrev Config := Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory d padding c row count jobs columns sizes mode

def verifier (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
    (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
    (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (emission : Emission count jobs Digest SourceMemory HelperMemory) :=
  SharedLookupPCSAlgebra.run p small config.basis config.shape config.jobsPositive config.slots (pairValues (config.pairs emission.2.2))
    config.active (fun job => by have := config.logicalShape job; omega) config.tables (config.multiplicities emission.2.1) (config.driver emission)

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → SharedLookupPCS.Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory) (second : HelperEmission jobs Digest HelperMemory) :=
  SharedLookupPCS.program enc config.basis config.shape domain fallback (verifier config p small) behavior
    (StagedHeterogeneousBatchOpening.emission first second)

def AllPass (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count jobs → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission jobs Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  ∀ job, TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples (config.logicalShape job)
      (fun column => LookupSourceFlattening.flatten config.shape (sourceTables domain capacity radius
        (SharedLookupGroupedOpening.words enc dummy g (StagedHeterogeneousBatchOpening.snapshots heights tag first second)) (config.slots job column))))
    (config.tables job) (fun i => algebraMap F K (config.multiplicities first.1 job i)) (pairValues (config.pairs second.1) job)

def badIndex (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count jobs → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission jobs Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (bad : ¬AllPass enc dummy config domain capacity radius first second) : Fin jobs := Classical.choose (not_forall.mp bad)

def ArithmeticEvent (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count jobs → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → SharedLookupPCS.Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission jobs Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : SharedLookupPCS.Result (F := F) (K := K) (Digest := Digest) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  if bad : ¬AllPass enc dummy config domain capacity radius first second then
    let selected := badIndex enc dummy config domain capacity radius first second bad
    let checkpoint := StagedHeterogeneousBatchOpening.snapshots heights tag first second
    let emission := StagedHeterogeneousBatchOpening.emission first.1 second.1
    SharedLookupPCSAlgebra.Arithmetic mode config.basis config.shape config.slots config.active (pairValues (config.pairs second.1))
      (sourceTables domain capacity radius (SharedLookupGroupedOpening.words enc dummy g checkpoint))
      (helperTables domain capacity radius (SharedLookupGroupedOpening.words enc dummy g checkpoint)) selected last.1.1 ∨
    SharedSequence.AnyBad (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius
      (SharedLookupGroupedOpening.build config.basis config.shape g (SharedLookupPCS.packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results
  else False

def pcsError (L : Type) [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F) (radius : Root count jobs → ℕ) : ENNReal :=
  ((StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange jobs)).map
    (fun root => JointMatrixOpening.error (K := L) (m := g.m root) (b := d + padding)
      (queries := g.queries root) (domain root) (radius root))).sum
end
end FormalProof4FHE.HasteBoots.StagedSharedLookup
