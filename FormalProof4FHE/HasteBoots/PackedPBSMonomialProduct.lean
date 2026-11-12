module
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialNTT
public import FormalProof4FHE.HasteBoots.AmbientMonomialProduct
@[expose] public section

/-! The native public-plan product follows actual monomial NTT acceptance in
the existing PBS prefix, retaining its memory, source owners and entire history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSMonomialProduct
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

def eraseBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : NTTBefore first second) :=
  (PackedPBSMonomialNTT.eraseBefore first second before.1,before.2.map (fun ntts => AmbientNTTSequence.erase first.heights ntts.1))

def beforeState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : NTTBefore first second) :=
  PackedPBSMonomialNTT.finalState first second before

/-- Only the already executed NTT loop's actual acceptance enables the product.
No NTT is rerun, and the exact loop memory selects the continuation factory. -/
def program (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme) := do
  let before ← PackedPBSMonomialNTT.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase
  match before.2 with
  | none => pure (before,none)
  | some ntts =>
    if ntts.accepted then
      let product ← AuthenticatedPublicZeroCheck.program
        (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.memory))
      pure (before,some product)
    else pure (before,none)

def finish (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (evaluations : PackedPBSMonomialReferences.Evaluations)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (before : NTTBefore first second) : ProbComp (NTTBefore first second × Option (ProductChild first.heights)) := do
  match before.2 with
  | none => pure (before,none)
  | some ntts =>
    if ntts.1.accepted then
      let product ← AmbientPublicZeroCheck.witness first.heights
        (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2
      pure (before,some product)
    else pure (before,none)

def witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial
  finish psi hs dummy first second evaluations firstSmall roundSmall zeroNodesEnough rotations zeroBase before

/-- A probability factorization of the same execution, retaining the
accepted accumulator return before the complete native monomial component. -/
def finishAccumulator (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference)
    (monoLength : 2^cells*(2^lanes) = 2^log)
    (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (before : Finished first second) : ProbComp (NTTBefore first second × Option (ProductChild first.heights)) := do
  match before.2 with
  | none => pure ((before,none),none)
  | some child =>
    if child.2.1.1.accepted && child.2.1.2.accepted then
      let component ← AmbientMonomialProduct.witness firstSmall roundSmall zeroNodesEnough hs.encoding monoLength psi primitive rotations
        (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase zeroBase first.heights dummy child.2.1.2.memory child.2.2
      pure ((before,some component.1),component.2)
    else pure ((before,none),none)

def finalState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (outcome : NTTBefore first second × Option (ProductChild first.heights)) :=
  match outcome.2 with
  | none => beforeState first second outcome.1
  | some product => product.2.2

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Reassociating the retained binds exposes the complete monomial component
at the actual accumulator return. This equality introduces no runtime replay. -/
theorem witness_factorization (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial = (do
      let before ← PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial
      finishAccumulator psi primitive hs dummy first second accumulators monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase before) := by
  simp only [witness,PackedPBSMonomialNTT.witness,bind_assoc]
  congr 1
  funext before
  cases equal : before.2 with
  | none => simp [PackedPBSMonomialNTT.finish,finishAccumulator,finish,equal]
  | some child =>
    by_cases passed : (child.2.1.1.accepted && child.2.1.2.accepted) = true
    · simp only [PackedPBSMonomialNTT.finish,finishAccumulator,equal,passed,ite_true,
        AmbientMonomialProduct.witness,bind_assoc]
      congr 1
      funext ntts
      simp only [pure_bind,finish,AmbientMonomialProduct.finish]
      split <;> simp only [pure_bind,bind_assoc]
    · simp [PackedPBSMonomialNTT.finish,finishAccumulator,finish,equal,passed]

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Full-state projection preserves the existing PBS prefix and the new native
continuation, including every skipped or rejected branch. -/
theorem project_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((eraseBefore first second outcome.1,outcome.2.map (fun product => (product.1.1,product.2.1))),finalState first second outcome)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←PackedPBSMonomialNTT.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial compatible restricted]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  cases equal : before.2 with
  | none => simp [finish,eraseBefore,finalState,beforeState,equal,map_pure,simulateQ_pure,StateT.run_pure]
  | some ntts =>
    simp only [eraseBefore,Option.map_some,AmbientNTTSequence.erase]
    by_cases passed : ntts.1.accepted = true
    · simp only [finish,equal,passed,ite_true,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      have projected := AmbientPublicZeroCheck.project_witness first.heights
        (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2
      change _ = (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
        (AuthenticatedPublicZeroCheck.program
          (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)))).run ntts.2 at projected
      simp only [PackedPBSMonomialNTT.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
    · simp [finish,equal,passed,finalState,beforeState,map_pure,simulateQ_pure,StateT.run_pure]

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Reaching the product derives the actual supported PBS prefix, an accepted
NTT loop, and the exact incoming private memory and ambient state. -/
theorem reached_product (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : NTTBefore first second) (product : ProductChild first.heights)
    (supported : (before,some product) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)) :
    ∃ ntts, before.2 = some ntts ∧ ntts.1.accepted = true ∧
      before ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial) ∧
      product ∈ support (AmbientPublicZeroCheck.witness first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none => simp [finish,equal] at remainder
  | some ntts =>
    by_cases passed : ntts.1.accepted = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have sameBefore : before = selected := congrArg Prod.fst same
      have sameProduct : product = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨ntts,equal,passed,selectedSupported,actualSupported⟩
    · simp [finish,equal,passed] at remainder

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The product's two private roots are the exact caller evaluation roots
already used by the monomial NTTs, including rejected product executions. -/
theorem product_roots (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : NTTBefore first second) (product : ProductChild first.heights)
    (supported : (before,some product) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)) :
    product.1.1.1 = evaluations.roots := by
  obtain ⟨ntts,_,_,_,present⟩ := reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial before product supported
  exact MonomialPublicZeroCheck.witness_roots firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots
    (zeroBase ntts.1.memory) first.heights dummy ntts.2 product present

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The old prefix is retained on every supported branch, even if the product
or an opening rejects. No losslessness of the continuation is assumed. -/
theorem before_supported (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : NTTBefore first second × Option (ProductChild first.heights))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)) :
    outcome.1 ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none =>
    simp [finish,equal] at remainder
    subst outcome
    exact selectedSupported
  | some ntts =>
    by_cases passed : ntts.1.accepted = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,_,same⟩ := remainder
      subst outcome
      exact selectedSupported
    · simp [finish,equal,passed] at remainder
      subst outcome
      exact selectedSupported

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Any previously recorded owner survives all new work on the full PBS
history. There is no source re-recording or geometry reset in this handoff. -/
theorem retains (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : NTTBefore first second × Option (ProductChild first.heights))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest first.heights tag)
    (recorded : ⟨tag,saved⟩ ∈ (beforeState first second outcome.1).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ (finalState first second outcome).checkpoints.checkpoints := by
  cases equal : outcome.2 with
  | none => simpa only [finalState,equal] using recorded
  | some product =>
    have present : (outcome.1,some product) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial) := by
      simpa only [←equal] using supported
    obtain ⟨ntts,same,_,_,childSupported⟩ := reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial outcome.1 product present
    have incoming : ⟨tag,saved⟩ ∈ ntts.2.checkpoints.checkpoints := by
      simpa only [beforeState,PackedPBSMonomialNTT.finalState,same] using recorded
    simpa only [finalState,equal] using AmbientPublicZeroCheck.retains first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2 product childSupported tag saved incoming

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier source-monitor and collision failures persist through every
new native branch, so the extended execution needs only its final exception. -/
theorem bad_persistent (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : NTTBefore first second × Option (ProductChild first.heights))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  cases equal : outcome.2 with
  | none => simpa only [finalState,equal] using bad
  | some product =>
    have present : (outcome.1,some product) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial) := by
      simpa only [←equal] using supported
    obtain ⟨ntts,same,_,_,childSupported⟩ := reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial outcome.1 product present
    have incoming : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) ntts.2 := by
      simpa only [beforeState,PackedPBSMonomialNTT.finalState,same] using bad
    simpa only [finalState,equal] using AmbientPublicZeroCheck.bad_persistent first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2 product childSupported incoming

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- A reached product entails both NTT calls in trusted order, so its source
coverage cannot hide a skipped NTT suffix. -/
theorem accepted_ntt_indices (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : NTTBefore first second) (product : ProductChild first.heights)
    (supported : (before,some product) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)) :
    ∃ ntts, before.2 = some ntts ∧ ntts.1.results.map Prod.fst = [false,true] := by
  obtain ⟨ntts,same,passed,present,_⟩ := reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial before product supported
  have oldSupported : (before.1,some ntts) ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial) := by
    simpa only [←same] using present
  exact ⟨ntts,same,PackedPBSMonomialNTT.accepted_indices length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before.1 ntts oldSupported passed⟩

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Each actual original NTT source owner is still recorded at the end of
its product continuation. No substituted root or new owner is introduced. -/
theorem retained_source_recorded (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : NTTBefore first second) (product : ProductChild first.heights)
    (supported : (before,some product) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial))
    (ntts : MonoChild first.heights) (same : before.2 = some ntts)
    (entry : Bool × Memory × AmbientMonomialNTT.Child first.heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
      (b := 2^lanes) (c := cells) (r := rows+1) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight))
    (member : entry ∈ ntts.1.results) (source : Bool) :
    ⟨(monoBase entry.1 entry.2.1).tag source,
      AmbientCommittedBatchSafeBound.snapshots first.heights (monoBase entry.1 entry.2.1).tag entry.2.2.1 source⟩ ∈
        product.2.2.checkpoints.checkpoints := by
  have present := before_supported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some product) supported
  have oldSupported : (before.1,some ntts) ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial) := by
    simpa only [←same] using present
  have recorded := PackedPBSMonomialNTT.retained_source_recorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before.1 ntts oldSupported entry member source
  have incoming : ⟨(monoBase entry.1 entry.2.1).tag source,
      AmbientCommittedBatchSafeBound.snapshots first.heights (monoBase entry.1 entry.2.1).tag entry.2.2.1 source⟩ ∈
        (beforeState first second before).checkpoints.checkpoints := by
    simpa only [beforeState,PackedPBSMonomialNTT.finalState,same] using recorded
  exact retains length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some product) supported _ _ incoming

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The entire prefix inherits the transported caller audit, including on
all early-return and rejected paths. -/
theorem audited_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (outcome : NTTBefore first second × Option (ProductChild first.heights))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  have actual : ((eraseBefore first second outcome.1,outcome.2.map (fun product => (product.1.1,product.2.1))),finalState first second outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
        (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial)) := by
    rw [←project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- One charge covers the entire PBS program through the public monomial
product, including all earlier rejected work and native private openings. -/
theorem final_bad_le_charge [Fintype Digest] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) compatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape first.heights)
    (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSMonomialProduct
