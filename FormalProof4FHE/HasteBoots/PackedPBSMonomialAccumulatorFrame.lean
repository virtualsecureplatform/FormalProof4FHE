module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorRotationCoverage
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionAccumulatorInputs
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorMonomialSources
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialProduct
public import FormalProof4FHE.HasteBoots.MonomialSourceAssociation
@[expose] public section

/-! Actual accumulator rotations follow from the native monomial continuation
in the same full PBS prefix, retaining its original source owners and history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSMonomialAccumulatorFrame
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open scoped BigOperators
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows d c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n (2^lanes))] [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]

variable (length : 2^c*(2^lanes) = 2^(cells+lanes)) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^((cells+lanes)+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2^lanes) c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory (2^lanes) n front suffix m queries height)
  (nodesEnough : 2*(2^lanes) ≤ q) (radix : ℕ)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (2^lanes) front suffix m queries height)

variable {FirstRetained Selection FirstRoot Data : Type} {firstRepetitions : Fin d → ℕ}

variable {SecondRetained SecondSelection SecondRoot SecondData : Type} {secondRepetitions : Fin d → ℕ}

variable {AccResponse : Type} {accFront accSuffix accM accQueries accHeight : ℕ}

  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) (2^lanes))]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin (rows+1) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]


variable (dummy : Digest)
  (first : PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, firstRepetitions i) → Digest) × FirstRetained)
    (Selection × ShortCircuitSequence.Outcome FirstRoot Data Memory) d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, secondRepetitions i) → Digest) × SecondRetained)
    (SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory) d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (2^lanes) front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference)
  (factory : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
    (2^lanes) cells rows accFront accSuffix accM accQueries accHeight)
  (evaluations : PackedPBSMonomialReferences.Evaluations)
  (monoBase : Bool → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
    (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : PackedPBSMonomialNTT.AfterAccumulator (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := 2^lanes) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (suffix := suffix) (queries := queries) (height := height) (AccResponse := AccResponse)
    (accB := 2^lanes) (accC := cells) (accR := rows) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
    first second)
  (ntts : PackedPBSMonomialNTT.MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg)
    (Memory := Memory) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoB := 2^lanes)
    (monoC := cells) (monoR := rows+1) (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries)
    (monoHeight := monoHeight) first.heights)
variable (traceRounds : PackedAccumulatorTrace.Rounds rows)
variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]
variable (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
  (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
  (rotations : Fin traceRounds.count → Fin (2*(2^(cells+lanes))))
  (zeroBase : Memory → AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
    (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
    Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight)
  (product : PackedPBSMonomialProduct.ProductOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
    (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
    (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) first.heights)
  (supported : ((before,some ntts),some product) ∈ support (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- Recover the actual monomial NTT prefix from the reached product. -/
theorem prefixSupported : (before,some ntts) ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough
    (radix : ZMod q) linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial) :=
  PackedPBSAccumulatorRotationCoverage.prefixSupported length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported

/-- The literal accumulator return that enabled this actual continuation. -/
def accumulatorChild := PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- The same retained accumulator has support in the complete native prefix. -/
theorem accumulatorSupported : (before.1,some (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)) ∈ support (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough
    (radix : ZMod q) linearBase dummy first second secondBase accumulators factory initial) :=
  PackedPBSAccumulatorMonomialSources.accumulatorSupported length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- Reaching the monomial NTT derives both actual accumulator acceptance gates. -/
theorem accumulatorAccepted : (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported).2.1.1.accepted = true ∧ (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported).2.1.2.accepted = true := by
  have gate := (Classical.choose_spec (PackedPBSMonomialNTT.reached_ntt length psi primitive family inputs base hs nodesEnough (radix : ZMod q)
    linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported))).2.1
  exact Bool.and_eq_true_iff.mp gate

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- All accumulator checkpoints survive both concrete NTTs and the actual
public monomial product; no separate owner availability is assumed. -/
theorem accumulatorRetained : CheckpointHistoryChain.Retains (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported).2.2 product.2.2 := by
  intro tag saved recorded
  have afterNTTs := AmbientNTTSequenceSoundness.retains
    (AmbientMonomialNTT.factory hs.encoding (Nat.pow_add 2 cells lanes).symm psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
    first.heights hs.encoding dummy [false,true] (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported).2.2 ntts
    (PackedPBSAccumulatorMonomialSources.nttExecuted length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)) tag saved recorded
  exact AmbientPublicZeroCheck.retains first.heights
    (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory))
    dummy ntts.2 product (PackedPBSAccumulatorRotationCoverage.productExecuted length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) tag saved afterNTTs

/-- Both interfaces decode exactly the same original input table. -/
theorem input_table (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ) :
    (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before.1 (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) (accumulatorSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) capacity radius).input =
      PackedPBSAccumulatorRotationCoverage.accumulatorTables length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported capacity radius 0 := rfl

/-- Both interfaces decode exactly the same original product table. -/
theorem product_table (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ) :
    (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before.1 (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) (accumulatorSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) capacity radius).product =
      PackedPBSAccumulatorRotationCoverage.accumulatorTables length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported capacity radius 1 := rfl

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts traceRounds firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- The actual final product state inherits the native audit through the full
prefix and the real geometry transition, with explicit public compatibility. -/
theorem final_audited
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) product.2.2 :=
  PackedPBSMonomialProduct.audited_witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory
    (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial compatible restricted audited
    ((before,some ntts),some product) supported

end
end FormalProof4FHE.HasteBoots.PackedPBSMonomialAccumulatorFrame
