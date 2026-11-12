module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulator
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
@[expose] public section

/-! Conditional accumulator rates are averaged on the actual whole-prefix
execution, with inherited audits and one shared final exception. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulatorProbability
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
open PackedPBSAccumulator (accumulator beforeState finalState)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev Outcome := PackedPBSFirstReconstruction.Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height) ×
  Option (PackedPBSFirstReconstruction.LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (d := d) (front := front) (suffix := suffix)
    (queries := queries) (height := height))

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)


local notation "Prior" => Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
  (front := front) (suffix := suffix) (queries := queries) (height := height)

variable {Helper Selection Root Data : Type}


abbrev ComparisonReturn := Selection × ShortCircuitSequence.Outcome Root Data Memory

local notation "Return" => ComparisonReturn (Selection := Selection) (Root := Root) (Data := Data) (Memory := Memory)

abbrev Before (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) :=
  Prior × Option (PackedPBSComparisonStage.Outcome s)

local notation "Reached" => Before (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

abbrev LinearOutcome (heights : Cfg → ℕ) :=
  AmbientLinear.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) (count := 2*d+2) ×
  AmbientLinear.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response)
    (Memory := Memory) (count := 2*d+2) (b := b) (front := front) (suffix := suffix) (height := height) (queries := queries)


local notation "Child" => LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (d := d) (b := b) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

abbrev SecondBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) :=
  Reached first × Option (Child first.heights)

local notation "Previous" => SecondBefore (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {SecondHelper SecondSelection SecondRoot SecondData : Type}
local notation "Return2" => SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory

abbrev ComparisonOutcome (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  PackedPBSComparisonStage.Outcome (sharedScheme first.heights second)

abbrev BeforeAccumulator (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  Previous first × Option (ComparisonOutcome first second)

local notation "Decomposed" => BeforeAccumulator (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {AccResponse : Type} {accB accC accR accFront accSuffix accM accQueries accHeight : ℕ}
  [SampleableType (Fin accB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) accB)]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

local notation "AccScheme" => AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight

abbrev AccumulatorOutcome (heights : Cfg → ℕ) :=
  AmbientAccumulator.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := Memory) ×
  AmbientAccumulator.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := AccResponse)
    (Memory := Memory) (b := accB) (c := accC) (r := accR) (front := accFront) (queries := accQueries) (height := accHeight)

local notation "AccChild" => AccumulatorOutcome (q := q) (Input := Input) (Cfg := Cfg) (AccResponse := AccResponse)
  (Memory := Memory) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront)
  (accQueries := accQueries) (accHeight := accHeight)

/-- Earlier events cannot gain probability through adaptive accumulator work. -/
theorem earlier_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Decomposed first second → Prop) :
    Pr{let outcome ← (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)}[
      event outcome.1] ≤
    Pr{let before ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)}[event before] := by
  unfold PackedPBSAccumulator.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  cases equal : before.2 with
  | none => simp [PackedPBSAccumulator.finish,equal,prEvent_norm,outside]
  | some compared =>
    by_cases passed : compared.2.2.1.2.accepted = true
    · simp only [PackedPBSAccumulator.finish,equal,passed,ite_true,prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => outside accepted)
    · simp [PackedPBSAccumulator.finish,equal,passed,prEvent_norm,outside]

/-- Earlier safe events transfer to the same extended final exception without
another hash charge or a losslessness assumption for the adaptive prover. -/
theorem earlier_safe_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Decomposed first second → Prop) :
    Pr{let outcome ← (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    Pr{let before ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)}[
      event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)] := by
  have included := prEvent_mono_of_support
    (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome))
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1))
    (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro bad
      exact accepted.2 (PackedPBSAccumulator.bad_persistent length psi primitive family inputs base hs nodesEnough radix linearBase
        dummy first second secondBase accumulators factory initial outcome supported bad))
  exact included.trans (earlier_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial
    (fun before => event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)))

variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType ((Fin (2^accFront) × Fin accB) → P)]

/-- False original-owner accumulator tuples have the derived native arithmetic/PCS
rate on their actually reached prefix, with no local authentication charge. -/
theorem safe_original_accumulator_bound [NeZero accM] [NeZero accB] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (basis : Module.Basis (Fin accB) (ZMod q) P)
    (enough : accM ≤ Fintype.card (Fin (2^accHeight))) (capacity : 2^accSuffix ≤ accM*accB)
    (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, first.heights ((factory memory).tag factor) = accHeight)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (factory memory).domain) accM :
        Set (Fin (2^accHeight) → P)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      ((((1+accR)+accC : ℕ) : ENNReal) * (((((2*accB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^accB))) +
        7 * JointMatrixOpening.error (K := P) (m := accM) (b := accB) (queries := accQueries)
          (factory memory).domain radius ≤ epsilon)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)}[
      ∃ compared child, outcome.1.2 = some compared ∧ outcome.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk first.heights
          (accumulator family inputs hs accumulators factory compared.2.2.1.2.memory) dummy capacity radius child ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) child.2.2] ≤ epsilon := by
  unfold PackedPBSAccumulator.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have incoming := PackedPBSAccumulator.before_audited length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase initial compatible restricted audited before supported
  cases equal : before.2 with
  | none => simp [PackedPBSAccumulator.finish,equal,prEvent_norm]
  | some compared =>
    by_cases passed : compared.2.2.1.2.accepted = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) compared.2.2.2 := by
        simpa only [beforeState,PackedPBSSecondComparisons.finalState,equal] using incoming
      let childScheme := accumulator family inputs hs accumulators factory compared.2.2.1.2.memory
      have conditional := OwnedAmbientAccumulator.original_safe_bound first.heights childScheme
        (geometry compared.2.2.1.2.memory) basis dummy enough capacity radius
        (small compared.2.2.1.2.memory) compared.2.2.2 stateAudit
      have bound := conditional.trans (calibrated compared.2.2.1.2.memory)
      simp only [PackedPBSAccumulator.finish,equal,passed,ite_true,prEvent_norm]
      convert bound using 1
      apply prEvent_congr
      intro child
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨selected,actual,sameSelected,sameActual,risk,clear⟩
        subst selected
        subst actual
        exact ⟨risk,clear⟩
      · rintro ⟨risk,clear⟩
        exact ⟨compared,child,rfl,rfl,risk,clear⟩
    · simp [PackedPBSAccumulator.finish,equal,passed,prEvent_norm]

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulatorProbability
