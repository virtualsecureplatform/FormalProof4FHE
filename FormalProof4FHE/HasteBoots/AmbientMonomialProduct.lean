module
public import FormalProof4FHE.HasteBoots.AmbientMonomialNTT
public import FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck
@[expose] public section

/-! Native monomial NTTs followed by the public-plan product check, on one
ambient state and the actual returned private memory. -/
namespace FormalProof4FHE.HasteBoots.AmbientMonomialProduct
open OracleSpec OracleComp
open InteractiveAuthenticatedOpening
noncomputable section
variable {q lanes cells rows rounds : ℕ} [Fact q.Prime]
variable {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Input] [DecidableEq Digest]
  {front suffix m queries height : ℕ}

variable [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))] [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (TestMatrix (ZMod q) (2^front) (2^lanes))] [SampleableType (Fin queries → Fin (2^height))]


variable {NTTResponse NTTCommitMemory : Type} {nttK nttFront nttSuffix nttM nttQueries nttHeight log : ℕ}
  [SampleableType (Fin nttK → Fin (rows+1) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^nttFront) (2^lanes))]
  [SampleableType (Fin nttQueries → Fin (2^nttHeight))]

abbrev Before (heights : Cfg → ℕ) := AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest)
  (Cfg := Cfg) (Response := NTTResponse) (Memory := Memory) (CommitMemory := NTTCommitMemory)
  (b := (2^lanes)) (c := cells) (r := (rows+1)) (k := nttK) (front := nttFront) (queries := nttQueries) (height := nttHeight) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

local notation "Previous" => Before (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
  (NTTResponse := NTTResponse) (Memory := Memory) (NTTCommitMemory := NTTCommitMemory)
  (lanes := lanes) (cells := cells) (rows := rows) (nttK := nttK) (nttFront := nttFront)
  (nttQueries := nttQueries) (nttHeight := nttHeight)

abbrev Child (heights : Cfg → ℕ) :=
  AmbientPublicZeroCheck.Prefix heights (Private := Bool) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
  AmbientPublicZeroCheck.RunResult heights (F := ZMod q) (Private := Bool) (Input := Input) (Digest := Digest)
    (Response := Response) (Memory := Memory) (b := 2^lanes) (n := cells+rows) (front := front) (queries := queries) (height := height)

variable (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
  (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (length : 2^cells*(2^lanes) = 2^log)
  (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (coefficients evaluations : Bool → Digest)
  (nttBase : Bool → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg NTTResponse Memory NTTCommitMemory
    (2^lanes) cells (rows+1) nttK nttFront nttSuffix nttM nttQueries nttHeight)
  (zeroBase : Memory → AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
    (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
    Input Digest Cfg Response Memory CommitMemory (2^lanes) (cells+rows) front suffix m queries height)

/-- Runtime composition has a single gate, after both actual NTT calls. -/
def program (memory : Memory) := do
  let ntts ← AmbientMonomialNTT.program enc length psi primitive coefficients evaluations nttBase memory
  if ntts.accepted then
    let product ← AuthenticatedPublicZeroCheck.program
      (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase ntts.memory))
    pure (ntts,some product)
  else pure (ntts,none)

/-- Retain the old trace and source owners; the private continuation enters at
its actual returned memory, and every call uses the inherited ambient handler. -/
def finish (heights : Cfg → ℕ) (dummy : Digest) (before : Previous heights) :
    ProbComp (Previous heights × Option (Child heights (q := q) (lanes := lanes) (cells := cells) (rows := rows)
      (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (front := front) (queries := queries) (height := height))) := do
  if before.1.accepted then
    let product ← AmbientPublicZeroCheck.witness heights
      (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase before.1.memory)) dummy before.2
    pure (before,some product)
  else pure (before,none)

def witness (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) := do
  let before ← AmbientMonomialNTT.witness enc length psi primitive coefficients evaluations nttBase heights dummy memory initial
  finish firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before

def finalState (heights : Cfg → ℕ) (outcome : Previous heights × Option (Child heights (q := q)
    (lanes := lanes) (cells := cells) (rows := rows) (Input := Input) (Digest := Digest) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (front := front) (queries := queries) (height := height))) :=
  match outcome.2 with
  | none => outcome.1.2
  | some product => product.2.2

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Analysis erasure preserves the complete native composition and final state,
including rejected NTT prefixes and rejected public-product openings. -/
theorem project_witness (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((AmbientNTTSequence.erase heights outcome.1.1,
      outcome.2.map (fun product => (product.1.1,product.2.1))),finalState heights outcome)) <$>
      witness firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights))
      (program firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase memory)).run initial := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←AmbientMonomialNTT.project_witness enc length psi primitive coefficients evaluations nttBase heights dummy memory initial]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  by_cases passed : before.1.accepted = true
  · simp only [finish,passed,ite_true,AmbientNTTSequence.erase,map_bind,map_pure,
      simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
    have projected := AmbientPublicZeroCheck.project_witness heights
      (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase before.1.memory)) dummy before.2
    change _ = (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights))
      (AuthenticatedPublicZeroCheck.program
        (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase before.1.memory)))).run before.2 at projected
    rw [←projected]
    simp only [bind_map_left]
  · simp [finish,passed,AmbientNTTSequence.erase,finalState,map_pure,simulateQ_pure,StateT.run_pure]


local notation "ProductChild" => Child (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
  (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (lanes := lanes)
  (cells := cells) (rows := rows) (front := front) (queries := queries) (height := height)
local notation "Result" => fun heights => Previous heights × Option (ProductChild heights)
local notation "Experiment" => witness firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase
local notation "Stage" => fun memory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase memory)

variable (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- A reached product check entails both NTTs accepted and support at their
exact returned memory and ambient state. -/
theorem reached_product (before : Previous heights) (product : ProductChild heights)
    (supported : (before,some product) ∈ support (Experiment heights dummy memory initial)) :
    before.1.accepted = true ∧
      before ∈ support (AmbientMonomialNTT.witness enc length psi primitive coefficients evaluations nttBase heights dummy memory initial) ∧
      product ∈ support (AmbientPublicZeroCheck.witness heights (Stage before.1.memory) dummy before.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  by_cases passed : selected.1.accepted = true
  · simp only [finish,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
    obtain ⟨actual,actualSupported,same⟩ := remainder
    have sameBefore : before = selected := congrArg Prod.fst same
    have sameChild : product = actual := Option.some.inj (congrArg Prod.snd same)
    subst selected
    subst actual
    exact ⟨passed,selectedSupported,actualSupported⟩
  · simp [finish,passed] at remainder

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Reaching the public-plan stage proves the trusted two-call NTT order. -/
theorem accepted_indices (before : Previous heights) (product : ProductChild heights)
    (supported : (before,some product) ∈ support (Experiment heights dummy memory initial)) :
    before.1.results.map Prod.fst = [false,true] := by
  obtain ⟨passed,present,_⟩ := reached_product firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  exact AmbientNTTSequenceSoundness.accepted_indices
    (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights enc dummy [false,true] memory initial before present passed

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The product opens exactly the retained evaluation root pair of the NTTs. -/
theorem product_roots (before : Previous heights) (product : ProductChild heights)
    (supported : (before,some product) ∈ support (Experiment heights dummy memory initial)) :
    product.1.1.1 = evaluations := by
  obtain ⟨_,_,present⟩ := reached_product firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  exact MonomialPublicZeroCheck.witness_roots firstSmall roundSmall nodesEnough enc psi rotations evaluations
    (zeroBase before.1.memory) heights dummy before.2 product present

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Every original NTT owner remains recorded after the product continuation,
including a rejected product check or rejected private opening. -/
theorem before_retains (before : Previous heights) (product : ProductChild heights)
    (supported : (before,some product) ∈ support (Experiment heights dummy memory initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ before.2.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ product.2.2.checkpoints.checkpoints := by
  obtain ⟨_,_,present⟩ := reached_product firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  exact AmbientPublicZeroCheck.retains heights (Stage before.1.memory) dummy before.2 product present tag saved recorded

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- One final exception also covers every exception already present at the
NTT loop's end. No fresh handler or local availability charge is introduced. -/
theorem before_bad_persistent (outcome : Result heights)
    (supported : outcome ∈ support (Experiment heights dummy memory initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.1.2) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome) := by
  cases equal : outcome.2 with
  | none => simpa only [finalState,equal] using bad
  | some product =>
    have present : (outcome.1,some product) ∈ support (Experiment heights dummy memory initial) := by
      simpa only [←equal] using supported
    obtain ⟨_,_,childSupported⟩ := reached_product firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial outcome.1 product present
    simpa only [finalState,equal] using AmbientPublicZeroCheck.bad_persistent heights (Stage outcome.1.1.memory) dummy outcome.1.2 product childSupported bad

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The complete native composition inherits the caller's audit on all paths. -/
theorem audited_witness (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial)
    (outcome : Result heights) (supported : outcome ∈ support (Experiment heights dummy memory initial)) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) (finalState heights outcome) := by
  have actual : ((AmbientNTTSequence.erase heights outcome.1.1,
      outcome.2.map (fun product => (product.1.1,product.2.1))),finalState heights outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights))
        (program firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase memory)).run initial) := by
    rw [←project_witness firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights)
    (program firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase memory) initial audited _ actual

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The retained NTT trace is supported even when the product continuation
rejects or fails to return; no independence or losslessness is used. -/
theorem before_supported (outcome : Result heights)
    (supported : outcome ∈ support (Experiment heights dummy memory initial)) :
    outcome.1 ∈ support (AmbientMonomialNTT.witness enc length psi primitive coefficients evaluations nttBase heights dummy memory initial) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  by_cases passed : selected.1.accepted = true
  · simp only [finish,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
    obtain ⟨actual,_,same⟩ := remainder
    subst outcome
    exact selectedSupported
  · simp [finish,passed] at remainder
    subst outcome
    exact selectedSupported

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier events cannot gain probability through the actual continuation. -/
theorem earlier_event_le (event : Previous heights → Prop) :
    Pr{let outcome ← (Experiment heights dummy memory initial)}[event outcome.1] ≤
    Pr{let before ← (AmbientMonomialNTT.witness enc length psi primitive coefficients evaluations nttBase heights dummy memory initial)}[event before] := by
  unfold witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  by_cases passed : before.1.accepted = true
  · simp only [finish,passed,ite_true,prEvent_norm]
    exact prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => outside accepted)
  · simp [finish,passed,prEvent_norm,outside]

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier arithmetic risks transfer under the shared final exception. -/
theorem earlier_safe_event_le (event : Previous heights → Prop) :
    Pr{let outcome ← (Experiment heights dummy memory initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)] ≤
    Pr{let before ← (AmbientMonomialNTT.witness enc length psi primitive coefficients evaluations nttBase heights dummy memory initial)}[
      event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) before.2] := by
  have included := prEvent_mono_of_support (Experiment heights dummy memory initial)
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome))
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.1.2)
    (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro bad
      exact accepted.2 (before_bad_persistent firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial outcome supported bad))
  exact included.trans (earlier_event_le firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial
    (fun before => event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) before.2))

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Every original source owner recorded by either NTT survives through the
actual product check, including rejection. Equal root digests alone are not
substituted for checkpoint ownership. -/
theorem retained_source_recorded (before : Previous heights) (product : ProductChild heights)
    (supported : (before,some product) ∈ support (Experiment heights dummy memory initial))
    (entry : Bool × Memory × AmbientMonomialNTT.Child heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := NTTResponse) (Memory := Memory) (CommitMemory := NTTCommitMemory)
      (b := 2^lanes) (c := cells) (r := rows+1) (k := nttK) (front := nttFront) (queries := nttQueries) (height := nttHeight))
    (member : entry ∈ before.1.results) (source : Bool) :
    ⟨(nttBase entry.1 entry.2.1).tag source,
      AmbientCommittedBatchSafeBound.snapshots heights (nttBase entry.1 entry.2.1).tag entry.2.2.1 source⟩ ∈
        product.2.2.checkpoints.checkpoints := by
  obtain ⟨_,present,_⟩ := reached_product firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  obtain ⟨incoming,childSupported⟩ := AmbientNTTSequenceSoundness.retained_child_support
    (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights enc dummy [false,true] memory initial before present entry member
  have recorded := AmbientNTT.fresh_recorded heights
    (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase entry.1 entry.2.1) dummy incoming entry.2.2 childSupported source
  have atEnd := AmbientNTTSequenceSoundness.child_retains
    (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights enc dummy [false,true] memory initial before present entry member
    ((nttBase entry.1 entry.2.1).tag source)
    (AmbientCommittedBatchSafeBound.snapshots heights (nttBase entry.1 entry.2.1).tag entry.2.2.1 source) recorded
  exact before_retains firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported _ _ atEnd

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The sole component-level charge covers all actually executed NTT,
ZeroCheck and private-opening work, including rejected paths. -/
theorem final_bad_le_charge [Fintype Digest] :
    Pr{let outcome ← (Experiment heights dummy memory (CheckpointExecution.empty (AmbientMatrixSource.Shape heights)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape heights))
      (program firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase memory)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape heights)) := by
  have projected := project_witness firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory
    (CheckpointExecution.empty (AmbientMatrixSource.Shape heights))
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (program firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase memory)
  rw [←projected,prEvent_map] at bound
  exact bound

section ProductBound
variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin (2^lanes)) → K)]

/-- Native product soundness is averaged over the actual accepted NTT returns.
The incoming audit is derived, and only local code geometry and a uniform
numeric calibration are assumed. There is no child security hypothesis. -/
theorem safe_original_product_bound [NeZero m]
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes))
    (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, heights ((zeroBase memory).tag factor) = height)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (zeroBase memory).domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius) ≤ epsilon)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (Experiment heights dummy memory initial)}[
      ∃ product, outcome.2 = some product ∧
        AmbientPublicZeroCheck.OriginalRisk heights (Stage outcome.1.1.memory) dummy capacity radius product ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) product.2.2] ≤ epsilon := by
  unfold witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  by_cases passed : before.1.accepted = true
  · have incoming := AmbientNTTSequenceSoundness.audited_witness
      (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights enc dummy [false,true] memory initial before supported audited
    have conditional := (MonomialPublicZeroCheck.original_safe_bound firstSmall roundSmall nodesEnough enc psi rotations evaluations
      (zeroBase before.1.memory) heights (geometry before.1.memory) basis dummy enough capacity radius (small before.1.memory) before.2 incoming).trans (calibrated before.1.memory)
    simp only [finish,passed,ite_true,prEvent_norm]
    convert conditional using 1
    apply prEvent_congr
    intro product
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨actual,same,risk,clear⟩
      subst actual
      exact ⟨risk,clear⟩
    · rintro ⟨risk,clear⟩
      exact ⟨product,rfl,risk,clear⟩
  · simp [finish,passed,prEvent_norm]

end ProductBound

section NTTBound
variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType (Fin (rows+1) → ZMod q)] [SampleableType ((Fin (2^nttFront) × Fin (2^lanes)) → P)]

omit [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Both original-source NTT rates transfer to the end of the native product
continuation, outside its same final exception. -/
theorem safe_original_ntt_bound [NeZero nttM]
    (nttBasis : Module.Basis (Fin (2^lanes)) (ZMod q) P)
    (nttEnough : nttM ≤ Fintype.card (Fin (2^nttHeight))) (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes))
    (nttRadius : Bool → ℕ) (nttEpsilon : Bool → ENNReal)
    (nttGeometry : ∀ side memory source, heights ((nttBase side memory).tag source) = nttHeight)
    (nttSmall : ∀ side memory, (nttRadius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (nttBase side memory).domain) nttM :
        Set (Fin (2^nttHeight) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ side memory,
      (((((rows+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^nttK) +
        (cells : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side) +
        JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side)) ≤ nttEpsilon side)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (Experiment heights dummy memory initial)}[
      AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius outcome.1.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)] ≤ nttEpsilon false + nttEpsilon true := by
  have lifted := earlier_safe_event_le firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial
    (fun before => AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius before.1)
  exact lifted.trans (AmbientMonomialNTT.original_safe_bound enc length psi primitive coefficients evaluations nttBase heights dummy nttBasis nttEnough nttCapacity nttRadius nttEpsilon
    nttGeometry nttSmall nttCalibrated memory initial audited)

end NTTBound

variable {K P : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType ((Fin (2^front) × Fin (2^lanes)) → K)]
  [SampleableType (Fin (rows+1) → ZMod q)] [SampleableType ((Fin (2^nttFront) × Fin (2^lanes)) → P)]

/-- All arithmetic risks of the complete native monomial component add
under one final exclusion. Both child rates are derived here, not supplied as
security hypotheses; callbacks may depend on the preceding returned memory. -/
theorem native_safe_joint_bound [NeZero m] [NeZero nttM]
    (nttBasis : Module.Basis (Fin (2^lanes)) (ZMod q) P)
    (nttEnough : nttM ≤ Fintype.card (Fin (2^nttHeight))) (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes))
    (nttRadius : Bool → ℕ) (nttEpsilon : Bool → ENNReal)
    (nttGeometry : ∀ side memory source, heights ((nttBase side memory).tag source) = nttHeight)
    (nttSmall : ∀ side memory, (nttRadius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (nttBase side memory).domain) nttM :
        Set (Fin (2^nttHeight) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ side memory,
      (((((rows+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^nttK) +
        (cells : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side) +
        JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side)) ≤ nttEpsilon side)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes))
    (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, heights ((zeroBase memory).tag factor) = height)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (zeroBase memory).domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius) ≤ epsilon)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (Experiment heights dummy memory initial)}[
      (AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius outcome.1.1 ∨
        (∃ product, outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (Stage outcome.1.1.memory) dummy capacity radius product)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)] ≤
        (nttEpsilon false + nttEpsilon true) + epsilon := by
  have left := safe_original_ntt_bound firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial
    nttBasis nttEnough nttCapacity nttRadius nttEpsilon nttGeometry nttSmall nttCalibrated audited
  have right := safe_original_product_bound firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial
    basis enough capacity radius epsilon geometry small calibrated audited
  have included := prEvent_mono (Experiment heights dummy memory initial)
    (fun outcome =>
      (AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius outcome.1.1 ∨
        (∃ product, outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (Stage outcome.1.1.memory) dummy capacity radius product)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome))
    (fun outcome =>
      (AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius outcome.1.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)) ∨
      (∃ product, outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (Stage outcome.1.1.memory) dummy capacity radius product ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) product.2.2))
    (by
      intro outcome accepted
      obtain ⟨risk,clear⟩ := accepted
      obtain ntt | product := risk
      · exact Or.inl ⟨ntt,clear⟩
      · obtain ⟨product,same,risk⟩ := product
        exact Or.inr ⟨product,same,risk,by simpa only [finalState,same] using clear⟩)
  exact included.trans ((prEvent_or_le _ _ _).trans (add_le_add left right))


/-- A complete native monomial run pays its derived arithmetic rate and ONE
whole-program availability/collision charge. This charge is still the generic
execution hazard; identifying physical attacker work is a separate obligation. -/
theorem native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero nttM]
    (nttBasis : Module.Basis (Fin (2^lanes)) (ZMod q) P)
    (nttEnough : nttM ≤ Fintype.card (Fin (2^nttHeight))) (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes))
    (nttRadius : Bool → ℕ) (nttEpsilon : Bool → ENNReal)
    (nttGeometry : ∀ side memory source, heights ((nttBase side memory).tag source) = nttHeight)
    (nttSmall : ∀ side memory, (nttRadius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (nttBase side memory).domain) nttM :
        Set (Fin (2^nttHeight) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ side memory,
      (((((rows+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^nttK) +
        (cells : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side) +
        JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side)) ≤ nttEpsilon side)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes))
    (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, heights ((zeroBase memory).tag factor) = height)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (zeroBase memory).domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius) ≤ epsilon)
    : Pr{let outcome ← (Experiment heights dummy memory (CheckpointExecution.empty (AmbientMatrixSource.Shape heights)))}[
      (AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius outcome.1.1 ∨ (∃ product, outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (Stage outcome.1.1.memory) dummy capacity radius product)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)] ≤
        ((nttEpsilon false + nttEpsilon true) + epsilon) +
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape heights))
      (program firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase memory)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape heights)) := by
  have good := CheckpointExecution.good_empty enc dummy (AmbientMatrixSource.Shape heights)
  have audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
    ⟨good.1,fun _ => good.2.2⟩
  have safe := native_safe_joint_bound firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory
    (CheckpointExecution.empty (AmbientMatrixSource.Shape heights))
    nttBasis nttEnough nttCapacity nttRadius nttEpsilon nttGeometry nttSmall nttCalibrated basis enough capacity radius epsilon geometry small calibrated audited
  have failure := final_bad_le_charge firstSmall roundSmall nodesEnough enc length psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory
  refine (prEvent_mono _ _ (fun outcome =>
    ((AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc length psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius outcome.1.1 ∨ (∃ product, outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (Stage outcome.1.1.memory) dummy capacity radius product)) ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)) ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add safe failure))
  intro outcome event
  obtain arithmetic | bad := event
  · by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (finalState heights outcome)
    · exact Or.inr bad
    · exact Or.inl ⟨arithmetic,bad⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.AmbientMonomialProduct
