module
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialProduct
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialNTTProbability
@[expose] public section

/-! The native public-plan product follows actual monomial NTT acceptance in
the existing PBS prefix, retaining its memory, source owners and entire history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSMonomialProductProbability
open PackedPBSMonomialProduct (beforeState finalState)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
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

variable {lanes cells rows rounds : ℕ}
variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin (rows+1) → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

local notation "MonoScheme" => AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight

abbrev MonomialOutcome (heights : Cfg → ℕ) :=
  AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
    (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
    (b := (2^lanes)) (c := cells) (r := (rows+1)) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

local notation "MonoChild" => MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)


abbrev BeforeProduct (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  Finished first second × Option (MonoChild first.heights)

local notation "NTTBefore" => BeforeProduct (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)

variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

local notation "ZeroScheme" => AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight

abbrev ProductOutcome (heights : Cfg → ℕ) :=
  AmbientPublicZeroCheck.Prefix heights (Private := Bool) (Input := Input) (Digest := Digest) (CommitMemory := ZeroCommitMemory) ×
  AmbientPublicZeroCheck.RunResult heights (F := ZMod q) (Private := Bool) (Input := Input) (Digest := Digest)
    (Response := ZeroResponse) (Memory := Memory) (b := 2^lanes) (n := cells+rows) (front := zeroFront) (queries := zeroQueries) (height := zeroHeight)

local notation "ProductChild" => ProductOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The continuation cannot increase any event on the retained PBS prefix. -/
theorem earlier_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (event : NTTBefore first second → Prop) :
    Pr{let outcome ← (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)}[event outcome.1] ≤
    Pr{let before ← (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)}[event before] := by
  unfold PackedPBSMonomialProduct.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  cases equal : before.2 with
  | none => simp [PackedPBSMonomialProduct.finish,equal,prEvent_norm,outside]
  | some ntts =>
    by_cases passed : ntts.1.accepted = true
    · simp only [PackedPBSMonomialProduct.finish,equal,passed,ite_true,prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => outside accepted)
    · simp [PackedPBSMonomialProduct.finish,equal,passed,prEvent_norm,outside]

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier safe events transfer to the complete product prefix's final
exception without another local authentication charge. -/
theorem earlier_safe_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (event : NTTBefore first second → Prop) :
    Pr{let outcome ← (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    Pr{let before ← (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)}[
      event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)] := by
  have included := prEvent_mono_of_support (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome))
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1))
    (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro bad
      exact accepted.2 (PackedPBSMonomialProduct.bad_persistent length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial outcome supported bad))
  exact included.trans (earlier_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial
    (fun before => event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)))

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^zeroFront) × Fin (2^lanes)) → K)]

/-- The product's original-owner soundness is derived at the actual accepted
NTT return. The prior PBS audit is derived through full-state projection; only
explicit code geometry and a uniform numeric calibration are supplied. -/
theorem safe_original_product_bound [NeZero zeroM] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (enough : zeroM ≤ Fintype.card (Fin (2^zeroHeight))) (capacity : 2^zeroSuffix ≤ zeroM*(2^lanes))
    (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, first.heights ((zeroBase memory).tag factor) = zeroHeight)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (zeroBase memory).domain) zeroM : Set (Fin (2^zeroHeight) → K)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := zeroM) (b := 2^lanes) (queries := zeroQueries) (zeroBase memory).domain radius +
        JointMatrixOpening.error (K := K) (m := zeroM) (b := 2^lanes) (queries := zeroQueries) (zeroBase memory).domain radius) ≤ epsilon)

    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)}[
      ∃ ntts product, outcome.1.2 = some ntts ∧ outcome.2 = some product ∧
        AmbientPublicZeroCheck.OriginalRisk first.heights
          (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy capacity radius product ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) product.2.2] ≤ epsilon := by
  unfold PackedPBSMonomialProduct.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have incoming := PackedPBSMonomialNTT.audited_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial compatible restricted audited before supported
  cases equal : before.2 with
  | none => simp [PackedPBSMonomialProduct.finish,equal,prEvent_norm]
  | some ntts =>
    by_cases passed : ntts.1.accepted = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) ntts.2 := by
        simpa only [PackedPBSMonomialNTT.finalState,equal] using incoming
      have conditional := (MonomialPublicZeroCheck.original_safe_bound firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots
        (zeroBase ntts.1.memory) first.heights (geometry ntts.1.memory) basis dummy enough capacity radius (small ntts.1.memory) ntts.2 stateAudit).trans (calibrated ntts.1.memory)
      simp only [PackedPBSMonomialProduct.finish,equal,passed,ite_true,prEvent_norm]
      convert conditional using 1
      apply prEvent_congr
      intro product
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨actualNtt,actualProduct,sameNtt,sameProduct,risk,clear⟩
        subst actualNtt
        subst actualProduct
        exact ⟨risk,clear⟩
      · rintro ⟨risk,clear⟩
        exact ⟨ntts,product,rfl,rfl,risk,clear⟩
    · simp [PackedPBSMonomialProduct.finish,equal,passed,prEvent_norm]

variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType (Fin (rows+1) → ZMod q)]
  [SampleableType ((Fin (2^monoFront) × Fin (2^lanes)) → P)]

/-- Both monomial NTTs and the public product receive their derived joint
native rate at the actual accepted accumulator return. The same final exclusion
covers the entire extended PBS prefix; no component hash charge is added. -/
theorem safe_native_monomial_bound [NeZero monoM] [NeZero zeroM] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (monoBasis : Module.Basis (Fin (2^lanes)) (ZMod q) P)
    (monoEnough : monoM ≤ Fintype.card (Fin (2^monoHeight))) (monoCapacity : 2^monoSuffix ≤ monoM*(2^lanes))
    (monoRadius : Bool → ℕ) (monoEpsilon : Bool → ENNReal)
    (monoGeometry : ∀ side memory source, first.heights ((monoBase side memory).tag source) = monoHeight)
    (monoSmall : ∀ side memory, (monoRadius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (monoBase side memory).domain) monoM :
        Set (Fin (2^monoHeight) → P)) : ℚ≥0)/3)
    (monoCalibrated : ∀ side memory,
      (((((rows+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^monoK) +
        (cells : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := P) (m := monoM) (b := 2^lanes) (queries := monoQueries) (monoBase side memory).domain (monoRadius side) +
        JointMatrixOpening.error (K := P) (m := monoM) (b := 2^lanes) (queries := monoQueries) (monoBase side memory).domain (monoRadius side)) ≤ monoEpsilon side)
    (zeroBasis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (zeroEnough : zeroM ≤ Fintype.card (Fin (2^zeroHeight))) (zeroCapacity : 2^zeroSuffix ≤ zeroM*(2^lanes))
    (zeroRadius : ℕ) (zeroEpsilon : ENNReal)
    (zeroGeometry : ∀ memory factor, first.heights ((zeroBase memory).tag factor) = zeroHeight)
    (zeroSmall : ∀ memory, (zeroRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (zeroBase memory).domain) zeroM : Set (Fin (2^zeroHeight) → K)) : ℚ≥0)/3)
    (zeroCalibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := zeroM) (b := 2^lanes) (queries := zeroQueries) (zeroBase memory).domain zeroRadius +
        JointMatrixOpening.error (K := K) (m := zeroM) (b := 2^lanes) (queries := zeroQueries) (zeroBase memory).domain zeroRadius) ≤ zeroEpsilon)

    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)}[
      ((∃ ntts, outcome.1.2 = some ntts ∧ AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) first.heights dummy monoCapacity monoRadius ntts.1) ∨
        (∃ ntts product, outcome.1.2 = some ntts ∧ outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
        (monoEpsilon false + monoEpsilon true) + zeroEpsilon := by
  rw [PackedPBSMonomialProduct.witness_factorization length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial]
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have incoming := PackedPBSMonomialNTT.before_audited length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial compatible restricted audited before supported
  cases equal : before.2 with
  | none => simp [PackedPBSMonomialProduct.finishAccumulator,equal,prEvent_norm]
  | some child =>
    by_cases passed : (child.2.1.1.accepted && child.2.1.2.accepted) = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) child.2.2 := by
        simpa only [PackedPBSMonomialNTT.beforeState,PackedPBSAccumulator.finalState,equal] using incoming
      have conditional := AmbientMonomialProduct.native_safe_joint_bound firstSmall roundSmall zeroNodesEnough hs.encoding monoLength psi primitive rotations
        (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase zeroBase first.heights dummy child.2.1.2.memory child.2.2
        monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated
        zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated stateAudit
      simp only [PackedPBSMonomialProduct.finishAccumulator,equal,passed,ite_true,prEvent_norm]
      convert conditional using 1
      apply prEvent_congr
      intro component
      cases productState : component.2 <;>
        simp [PackedPBSMonomialProduct.finalState,beforeState,PackedPBSMonomialNTT.finalState,AmbientMonomialProduct.finalState,productState]
    · simp [PackedPBSMonomialProduct.finishAccumulator,equal,passed,prEvent_norm]

end
end FormalProof4FHE.HasteBoots.PackedPBSMonomialProductProbability
