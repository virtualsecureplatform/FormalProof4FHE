module
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialNTT
@[expose] public section

/-! The two-call original-source rate is averaged over actual accumulator
returns and earlier risks share the same extended final exception. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSMonomialNTTProbability
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
open PackedPBSMonomialNTT (beforeState finalState)
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

abbrev AfterAccumulator (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  Decomposed first second × Option (AccChild first.heights)

local notation "Finished" => AfterAccumulator (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)

variable {MonoResponse MonoCommitMemory : Type} {monoB monoC monoR monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin monoR → ZMod q)] [SampleableType (Fin monoB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) monoB)]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

local notation "MonoScheme" => AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  monoB monoC monoR monoK monoFront monoSuffix monoM monoQueries monoHeight

abbrev MonomialOutcome (heights : Cfg → ℕ) :=
  AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
    (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
    (b := monoB) (c := monoC) (r := monoR) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

local notation "MonoChild" => MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoB := monoB) (monoC := monoC) (monoR := monoR)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)

/-- Earlier events cannot gain probability through the adaptive NTT loop. -/
theorem earlier_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Finished first second → Prop) :
    Pr{let outcome ← (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)}[event outcome.1] ≤
    Pr{let before ← (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)}[event before] := by
  unfold PackedPBSMonomialNTT.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  cases equal : before.2 with
  | none => simp [PackedPBSMonomialNTT.finish,equal,prEvent_norm,outside]
  | some child =>
    by_cases passed : (child.2.1.1.accepted && child.2.1.2.accepted) = true
    · simp only [PackedPBSMonomialNTT.finish,equal,passed,ite_true,prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => outside accepted)
    · simp [PackedPBSMonomialNTT.finish,equal,passed,prEvent_norm,outside]

/-- Earlier safe arithmetic risks transfer to the one extended final exception,
without independence, losslessness or another authentication charge. -/
theorem earlier_safe_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Finished first second → Prop) :
    Pr{let outcome ← (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    Pr{let before ← (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)}[
      event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)] := by
  have included := prEvent_mono_of_support
    (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome))
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1))
    (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro bad
      exact accepted.2 (PackedPBSMonomialNTT.bad_persistent length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial outcome supported bad))
  exact included.trans (earlier_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial
    (fun before => event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)))

variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType (ZMod q)] [SampleableType (Fin monoR → ZMod q)]
  [SampleableType ((Fin (2^monoFront) × Fin monoB) → P)]

/-- The native two-call original-owner rate is derived on the actually reached
prefix, using the computed accumulator flags and inherited audits/memory. -/
theorem safe_original_ntt_bound [NeZero monoM] [NeZero monoB] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (basis : Module.Basis (Fin monoB) (ZMod q) P)
    (enough : monoM ≤ Fintype.card (Fin (2^monoHeight))) (capacity : 2^monoSuffix ≤ monoM*monoB)
    (radius : Bool → ℕ) (epsilon : Bool → ENNReal)
    (geometry : ∀ side memory source, first.heights ((monoBase side memory).tag source) = monoHeight)
    (small : ∀ side memory, (radius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (monoBase side memory).domain) monoM :
        Set (Fin (2^monoHeight) → P)) : ℚ≥0)/3)
    (calibrated : ∀ side memory,
      ((((monoR : ENNReal)/Fintype.card (ZMod q))^monoK) +
        (monoC : ENNReal)*(((((2*monoB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^monoB))) +
      (JointMatrixOpening.error (K := P) (m := monoM) (b := monoB) (queries := monoQueries) (monoBase side memory).domain (radius side) +
        JointMatrixOpening.error (K := P) (m := monoM) (b := monoB) (queries := monoQueries) (monoBase side memory).domain (radius side)) ≤ epsilon side)
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)}[
      ∃ ntts, outcome.2 = some ntts ∧
        AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) first.heights dummy capacity radius ntts.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) ntts.2] ≤ epsilon false + epsilon true := by
  unfold PackedPBSMonomialNTT.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have incoming := PackedPBSMonomialNTT.before_audited length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial compatible restricted audited before supported
  cases equal : before.2 with
  | none => simp [PackedPBSMonomialNTT.finish,equal,prEvent_norm]
  | some child =>
    by_cases passed : (child.2.1.1.accepted && child.2.1.2.accepted) = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) child.2.2 := by
        simpa only [beforeState,PackedPBSAccumulator.finalState,equal] using incoming
      have conditional := AmbientMonomialNTT.original_safe_bound hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy basis enough capacity radius epsilon
        geometry small calibrated child.2.1.2.memory child.2.2 stateAudit
      simp only [PackedPBSMonomialNTT.finish,equal,passed,ite_true,prEvent_norm]
      convert conditional using 1
      apply prEvent_congr
      intro ntts
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨actual,same,risk,clear⟩
        subst actual
        exact ⟨risk,clear⟩
      · rintro ⟨risk,clear⟩
        exact ⟨ntts,rfl,risk,clear⟩
    · simp [PackedPBSMonomialNTT.finish,equal,passed,prEvent_norm]

end
end FormalProof4FHE.HasteBoots.PackedPBSMonomialNTTProbability
