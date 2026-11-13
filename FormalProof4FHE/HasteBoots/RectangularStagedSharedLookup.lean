module
public import FormalProof4FHE.HasteBoots.MixedWidthStagedSharedLookup
public import FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS
public import FormalProof4FHE.HasteBoots.StagedCommitmentException
@[expose] public section

/-! Source commitments precede pair/helper work; helper commitments precede
ordered EQ, one common scalar batch, computed terminal selection and grouped
PCS. Each job retains its own table and original registry slots. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
noncomputable section
abbrev Pair (K : Type) [Zero K] := K × {r : K // r ≠ 0}
def pairValues {K : Type} [Zero K] {jobs : ℕ} (pairs : Fin jobs → Pair K) : Fin jobs → K × K :=
  fun job => ((pairs job).1,(pairs job).2.val)
abbrev SourceEmission (count : ℕ) (Digest SourceMemory : Type) :=
  RectangularStagedOpening.SourceEmission (Fin count) Digest SourceMemory
abbrev HelperEmission (jobs : ℕ) (Digest HelperMemory : Type) :=
  RectangularStagedOpening.HelperEmission (Fin jobs) Digest HelperMemory
abbrev Emission (count jobs : ℕ) (Digest SourceMemory HelperMemory : Type) :=
  RectangularSharedLookupPCS.Emission count jobs Digest SourceMemory HelperMemory

/-- Public geometry, literal job tables, prefix-dependent prover behavior and
syntactic message degrees. No source truth, acceptance, hash safety, or random
challenge law is included in this data. -/
abbrev Parameters (F K Message Memory Cfg Input Digest SourceMemory HelperMemory : Type)
    (d padding c row count jobs : ℕ) (columns sizes : Fin jobs → ℕ) (mode : Mode)
    [Field F] [Field K] [Algebra F K] :=
  MixedWidthStagedSharedLookup.Parameters F K Message Memory Cfg Input Digest
    SourceMemory HelperMemory d padding c row count jobs columns sizes mode

variable {F K Message Memory Cfg Input Digest Response SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count jobs : ℕ} {columns sizes : Fin jobs → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count jobs → Cfg} {g : Geometry c row count jobs} {symbolWidth : Root count jobs → ℕ}
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

abbrev Config := Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory d padding c row count jobs columns sizes mode

def verifier (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
    (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
    (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (emission : Emission count jobs Digest SourceMemory HelperMemory) :=
  MixedWidthSharedLookupPCSAlgebra.run p small config.basis config.shape config.jobsPositive config.slots (pairValues (config.pairs emission.2.2))
    config.active (fun job => by have := config.logicalShape job; omega) config.tables (config.multiplicities emission.2.1) (config.driver emission)

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → RectangularSharedLookupPCS.Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory) (second : HelperEmission jobs Digest HelperMemory) :=
  RectangularSharedLookupPCS.program enc config.basis config.shape domain fallback (verifier config p small) behavior
    (RectangularStagedOpening.emission first second)

def AllPass (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count jobs → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission jobs Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  ∀ job, TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples (config.logicalShape job)
      (fun column => LookupSourceFlattening.flatten config.shape (RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius
        (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g (RectangularStagedOpening.snapshots heights tag first second)) (config.slots job column))))
    (config.tables job) (fun i => algebraMap F K (config.multiplicities first.1 job i)) (pairValues (config.pairs second.1) job)

def badIndex (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count jobs → ℕ)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission jobs Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (bad : ¬AllPass (helperPadding := helperPadding) enc dummy config domain capacity radius first second) : Fin jobs := Classical.choose (not_forall.mp bad)

def ArithmeticEvent (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : Config (F := F) (K := K) (Message := Message) (Memory := Memory) (Cfg := Cfg) (Input := Input) (Digest := Digest)
      (SourceMemory := SourceMemory) (HelperMemory := HelperMemory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (columns := columns) (sizes := sizes) (mode := mode))
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count jobs → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → RectangularSharedLookupPCS.Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (first : SourceEmission count Digest SourceMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission jobs Digest HelperMemory × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : RectangularSharedLookupPCS.Result (symbolWidth := symbolWidth) (F := F) (K := K) (Digest := Digest) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (helperPadding := helperPadding) (c := c) (row := row)
      (count := count) (jobs := jobs) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  if bad : ¬AllPass (helperPadding := helperPadding) enc dummy config domain capacity radius first second then
    let selected := badIndex (helperPadding := helperPadding) enc dummy config domain capacity radius first second bad
    let checkpoint := RectangularStagedOpening.snapshots heights tag first second
    let emission := RectangularStagedOpening.emission first.1 second.1
    MixedWidthSharedLookupPCSAlgebra.Arithmetic mode config.basis config.shape config.slots config.active (pairValues (config.pairs second.1))
      (RectangularPaddedLookupOpeningFamily.sourceTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint))
      (RectangularPaddedLookupOpeningFamily.helperTables (d := d) (padding := padding) (helperPadding := helperPadding) domain capacity radius (RectangularLookupGroupedOpening.words (d := d) (padding := padding) (helperPadding := helperPadding) enc dummy g checkpoint)) selected last.1.1 ∨
    SharedSequence.AnyBad (fun _ => RectangularRecordedOpening.Arithmetic enc dummy domain capacity radius
      (RectangularLookupGroupedOpening.build (d := d) (padding := padding) (helperPadding := helperPadding) config.basis config.shape g (RectangularSharedLookupPCS.packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results
  else False

def pcsError [Fintype F]
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F) (radius : Root count jobs → ℕ) : ENNReal :=
  ((RectangularStagedOpening.factors (List.finRange count) (List.finRange jobs)).map
    (fun root => RectangularVariableWidthOpening.error (domain root) (g.m root) (symbolWidth root) (packedWidth (d + padding) (d + helperPadding) root) (g.queries root) (radius root))).sum
end
end FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
