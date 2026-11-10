module
public import FormalProof4FHE.HasteBoots.SharedLookupTerminal
public import FormalProof4FHE.HasteBoots.MixedWidthLookupPairTerminal
public import FormalProof4FHE.HasteBoots.SharedLookupBatchArithmetic
@[expose] public section

/-! Successful computed shared lookup terminals expose their actual batch
arithmetic event or a wrong original source/helper opening. Jobs gather their
own source slots at the common point. Source tables are analysis only; native
byte/transcript refinement and complete grouped-PCS composition remain open. -/
open OracleSpec OracleComp BinaryTree
open scoped Classical
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
namespace FormalProof4FHE.HasteBoots.MixedWidthSharedLookupTerminalReduction
noncomputable section
variable {F K Memory : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count jobs : ℕ} {columns : Fin jobs → ℕ}

/-- Exact sum and identity obligations on the original global source family
and per-job helpers. No source roots are replaced or duplicated per job. -/
def Wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (packet : MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs) : Prop :=
  ∃ job, MixedWidthLookupOpeningFamily.WrongOpenings basis shape (fun column => sources (slots job column)) (helpers job)
    (MixedWidthLookupOpeningFamily.pairPacket slots packet job).sumClaim
    (MixedWidthLookupOpeningFamily.pairPacket slots packet job).zeroClaim
    (MixedWidthLookupOpeningFamily.pairPacket slots packet job).values.sources
    (MixedWidthLookupOpeningFamily.pairPacket slots packet job).values.helper

/-- The terminal's wrong-opening event on decoded original checkpoint
words is exactly the grouped PCS family's wrong-value event. Coverage is the
structural request-slot property already proved for the radix schedule. -/
theorem wrong_iff_global {Cfg : Type} [DecidableEq F]
    {heights : Cfg → ℕ} {tag : MixedWidthLookupOpeningFamily.Root count jobs → Cfg}
    {g : MixedWidthLookupOpeningFamily.Geometry c row count jobs}
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (coverage : ∀ source, ∃ job column, slots job column = source)
    (packet : MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * MixedWidthLookupOpeningFamily.packedWidth (d + padding) (d + helperPadding) root)
    (radius : MixedWidthLookupOpeningFamily.Root count jobs → ℕ)
    (words : ∀ root, Fin (2 ^ heights (tag root)) → (Fin (2 ^ g.front root) × Fin (MixedWidthLookupOpeningFamily.packedWidth (d + padding) (d + helperPadding) root)) → Fin (MixedWidthLookupOpeningFamily.packedWidth (d + padding) (d + helperPadding) root) → F) :
    Wrong basis shape slots (MixedWidthLookupOpeningFamily.sourceTables domain capacity radius words)
      (MixedWidthLookupOpeningFamily.helperTables domain capacity radius words) packet ↔
    ∃ root claim, MixedWidthLookupOpeningFamily.WrongValue basis shape packet domain capacity radius words root claim :=
  MixedWidthLookupOpeningFamily.any_job_wrong_iff basis shape packet slots coverage domain capacity radius words

omit [Field F] [Algebra F K] in
/-- The local lookup arithmetic predicates are exactly the earlier shared
batch predicates on the returned claims, not a second scalar experiment. -/
theorem pair_joint_iff {Factor Term : Type} [Fintype Term]
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (claims : SharedLookupBatchSequence.Equation jobs → Subclaim K 1 (c + row))
    (valid : SharedScalarBatchQuery.Valid (some (claims,()))) (reference : Fin jobs × Bool)
    (rawSources : Fin count → Fin (d + padding) → F) (helperValues : Fin jobs → K)
    (points : SharedLookupBatchSequence.Points K jobs (c + row)) (earlierMemory batchMemory : Memory)
    (selected : Fin jobs) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin (c + row) → K) → Factor → MatrixFold.Cube (c + row) → K)
    (helpers : MatrixFold.Cube (c + row) → K) :
    let packet := MixedWidthLookupOpeningFamily.ofBatch claims reference rawSources helperValues points
    let pair := MixedWidthLookupOpeningFamily.pairPacket slots packet selected
    LookupPairSequence.JointTruthful arity coefficient indices tables helpers
      (some (pair.sumClaim,()),some (pair.eqPoint,some (pair.zeroClaim,()))) ↔
    SharedLookupBatchSequence.JointTruthful selected arity coefficient indices tables helpers
      ((points,earlierMemory),some (claims,batchMemory)) := by
  dsimp only
  rw [MixedWidthLookupOpeningFamily.pairPacket_ofBatch slots claims valid reference rawSources helperValues points selected]
  rfl

/-- A checked partial-table packet whose subclaims come from this batch
forces the selected joint arithmetic event or a wrong original opening. -/
theorem partial_packet_or_wrong
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (jobsPositive : 0 < jobs)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (earlier : SharedLookupBatchSequence.Result K Memory jobs (c + row))
    (claims : SharedLookupBatchSequence.Equation jobs → Subclaim K 1 (c + row)) (batchMemory : Memory)
    (batchEq : earlier.2 = some (claims,batchMemory)) (valid : SharedScalarBatchQuery.Valid (some (claims,())))
    (packet : MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs)
    (origin : packet = MixedWidthLookupOpeningFamily.ofBatch claims (⟨0,jobsPositive⟩,false)
      packet.sources packet.helpers earlier.1.1)
    (accepted : SharedLookupTerminal.guard basis shape slots pairs active enough packet = true)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F) (selected : Fin jobs) :
    SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
      (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)) (active selected))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) earlier ∨
    Wrong basis shape slots sources helpers packet := by
  have checked := (SharedLookupTerminal.guard_spec basis shape slots pairs active enough packet accepted selected).2
  let pair := MixedWidthLookupOpeningFamily.pairPacket slots packet selected
  have localResult := MixedWidthLookupPairTerminal.partial_joint_or_wrong basis shape (packet.equalityPoints selected)
    (pairs selected).2 (pairs selected).1 (active selected) (enough selected)
    (fun column => sources (slots selected column)) (helpers selected) pair.sumClaim pair.zeroClaim
    pair.values.sources pair.values.helper (by simpa only [pair,MixedWidthLookupOpeningFamily.pairPacket,ScalarSumcheckQuery.point_query] using checked)
  rcases localResult with arithmetic | wrong
  · left
    have adapted := pair_joint_iff slots claims valid (⟨0,jobsPositive⟩,false) packet.sources packet.helpers earlier.1.1
      earlier.1.2 batchMemory selected ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
      (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)) (active selected))
      (fun cell => PaddedExtension.decode basis (helpers selected cell))
    have localTrue : LookupPairSequence.JointTruthful ExtensionLookupIdentity.partialArity
        (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
        (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1
          (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
          (fun cell => PaddedExtension.decode basis (helpers selected cell)) (active selected))
        (fun cell => PaddedExtension.decode basis (helpers selected cell))
        (some (pair.sumClaim,()),some (pair.eqPoint,some (pair.zeroClaim,()))) := arithmetic
    dsimp only [pair] at localTrue
    rw [origin] at localTrue
    have truthful := adapted.mp localTrue
    simpa only [SharedLookupBatchSequence.JointTruthful,SharedLookupBatchSequence.SumTruthful,
      SharedLookupBatchSequence.IdentityTruthful,batchEq] using truthful
  · exact Or.inr ⟨selected,wrong⟩
/-- A checked full-table packet whose subclaims come from this batch
forces the selected joint arithmetic event or a wrong original opening. -/
theorem full_packet_or_wrong
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c) (jobsPositive : 0 < jobs)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (earlier : SharedLookupBatchSequence.Result K Memory jobs (c + row))
    (claims : SharedLookupBatchSequence.Equation jobs → Subclaim K 1 (c + row)) (batchMemory : Memory)
    (batchEq : earlier.2 = some (claims,batchMemory)) (valid : SharedScalarBatchQuery.Valid (some (claims,())))
    (packet : MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs)
    (origin : packet = MixedWidthLookupOpeningFamily.ofBatch claims (⟨0,jobsPositive⟩,false)
      packet.sources packet.helpers earlier.1.1)
    (accepted : SharedLookupTerminal.guard basis shape slots pairs active enough packet = true)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F) (selected : Fin jobs)
    (selectedFull : active selected = 2 ^ (c + row)) :
    SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) earlier ∨
    Wrong basis shape slots sources helpers packet := by
  have checked := (SharedLookupTerminal.guard_spec basis shape slots pairs active enough packet accepted selected).2
  let pair := MixedWidthLookupOpeningFamily.pairPacket slots packet selected
  have localResult := MixedWidthLookupPairTerminal.full_joint_or_wrong basis shape (packet.equalityPoints selected)
    (pairs selected).2 (pairs selected).1
    (fun column => sources (slots selected column)) (helpers selected) pair.sumClaim pair.zeroClaim
    pair.values.sources pair.values.helper (by simpa only [selectedFull,pair,MixedWidthLookupOpeningFamily.pairPacket,ScalarSumcheckQuery.point_query] using checked)
  rcases localResult with arithmetic | wrong
  · left
    have adapted := pair_joint_iff slots claims valid (⟨0,jobsPositive⟩,false) packet.sources packet.helpers earlier.1.1
      earlier.1.2 batchMemory selected ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)))
      (fun cell => PaddedExtension.decode basis (helpers selected cell))
    have localTrue : LookupPairSequence.JointTruthful ExtensionLookupIdentity.fullArity
        (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
        (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1
          (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
          (fun cell => PaddedExtension.decode basis (helpers selected cell)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell))
        (some (pair.sumClaim,()),some (pair.eqPoint,some (pair.zeroClaim,()))) := arithmetic
    dsimp only [pair] at localTrue
    rw [origin] at localTrue
    have truthful := adapted.mp localTrue
    simpa only [SharedLookupBatchSequence.JointTruthful,SharedLookupBatchSequence.SumTruthful,
      SharedLookupBatchSequence.IdentityTruthful,batchEq] using truthful
  · exact Or.inr ⟨selected,wrong⟩
variable {Cfg Input Digest Payload Message : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

/-- Accepted operational partial terminals expose arithmetic or wrong original
openings. Packet provenance and common-query validity come from execution. -/
theorem partial_acceptance_or_wrong (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs (c + row))
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (totals : Fin jobs → K) (memory : Memory)
    (receiver : SharedLookupTerminal.Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : (SharedLookupBatchSequence.Result K Memory jobs (c + row) ×
      Option (MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs × Memory)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (SharedLookupTerminal.program p small schedule basis shape jobsPositive slots pairs active enough totals memory receiver)).run before))
    (packet : MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs) (finalMemory : Memory)
    (returned : outcome.1.2 = some (packet,finalMemory))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F) (selected : Fin jobs) :
    SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
      (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)) (active selected))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) outcome.1.1 ∨
    Wrong basis shape slots sources helpers packet := by
  obtain ⟨claims,batchMemory,batchEq,valid,origin,checked⟩ := SharedLookupTerminal.accepted_data enc dummy workerShape
    p small schedule basis shape jobsPositive slots pairs active enough totals memory receiver before outcome supported packet finalMemory returned
  exact partial_packet_or_wrong basis shape jobsPositive slots pairs active enough outcome.1.1 claims batchMemory batchEq valid
    packet origin checked sources helpers selected

/-- Full-table version keeps the selected job's degree-three arithmetic event. -/
theorem full_acceptance_or_wrong (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs (c + row))
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (totals : Fin jobs → K) (memory : Memory)
    (receiver : SharedLookupTerminal.Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : (SharedLookupBatchSequence.Result K Memory jobs (c + row) ×
      Option (MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs × Memory)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (SharedLookupTerminal.program p small schedule basis shape jobsPositive slots pairs active enough totals memory receiver)).run before))
    (packet : MixedWidthLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs) (finalMemory : Memory)
    (returned : outcome.1.2 = some (packet,finalMemory))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F) (selected : Fin jobs)
    (selectedFull : active selected = 2 ^ (c + row)) :
    SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1
        (fun column => LookupSourceFlattening.flatten shape (sources (slots selected column)))
        (fun cell => PaddedExtension.decode basis (helpers selected cell)))
      (fun cell => PaddedExtension.decode basis (helpers selected cell)) outcome.1.1 ∨
    Wrong basis shape slots sources helpers packet := by
  obtain ⟨claims,batchMemory,batchEq,valid,origin,checked⟩ := SharedLookupTerminal.accepted_data enc dummy workerShape
    p small schedule basis shape jobsPositive slots pairs active enough totals memory receiver before outcome supported packet finalMemory returned
  exact full_packet_or_wrong basis shape jobsPositive slots pairs active enough outcome.1.1 claims batchMemory batchEq valid
    packet origin checked sources helpers selected selectedFull

end
end FormalProof4FHE.HasteBoots.MixedWidthSharedLookupTerminalReduction
