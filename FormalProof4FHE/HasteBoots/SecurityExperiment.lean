module

public import FormalProof4FHE.HasteBoots.ApplicationKnowledge
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# Contract for the complete security experiment

This is the target interface, not an implementation of the native verifier
or a security certificate. A chronological trace retains all submissions and
charged activity through rejection and stopping. Setup and verifier activity
are separate from attacker work. Primitive counts are observations; their
conversion to machine work must be proved for an execution implementation.
-/

namespace FormalProof4FHE.HasteBoots.SecurityExperiment

noncomputable section

inductive Actor where
  | attacker | verifier | setup
  deriving DecidableEq

/-- Counts of actual primitive operations, rather than input-length bounds.
Repeated and cached operations must be recorded according to execution. -/
structure PrimitiveWork where
  sha512Blocks : ℕ
  shakeAbsorbBlocks : ℕ
  shakeSqueezeBlocks : ℕ
  deriving DecidableEq

/-- The fields have different units; none is silently identified with a
machine instruction count. The native implementation must justify each. -/
structure Work where
  primitive : PrimitiveWork
  constructedBytes : ℕ
  memoryOperations : ℕ
  machineSteps : ℕ
  deriving DecidableEq

inductive Event (Input Output : Type) where
  | work (actor : Actor) (amount : Work)
  | submission (input : Input) (output : Output) (accepted : Bool)

abbrev Trace (Input Output : Type) := List (Event Input Output)

/-- Submitting does not create an assumed work charge. Its actual cost must
appear in the implementation's work events and be justified by refinement. -/
def eventSteps {Input Output : Type} (actor : Actor) : Event Input Output → ℕ
  | .work owner amount => if owner = actor then amount.machineSteps else 0
  | .submission _ _ _ => 0

def steps {Input Output : Type} (actor : Actor) (trace : Trace Input Output) : ℕ :=
  (trace.map (eventSteps actor)).sum

/-- A false statement is defined independently of verifier acceptance. All
earlier accepted false submissions remain bad after later rejection. -/
def Bad {Input Output : Type} (relation : Input → Output → Prop) (trace : Trace Input Output) : Prop :=
  ∃ input output, Event.submission input output true ∈ trace ∧ ¬relation input output

theorem steps_append {Input Output : Type} (actor : Actor) (first last : Trace Input Output) :
    steps actor (first ++ last) = steps actor first + steps actor last := by
  simp [steps, List.map_append, List.sum_append]

theorem bad_persists {Input Output : Type} (relation : Input → Output → Prop)
    (first last : Trace Input Output) (bad : Bad relation first) : Bad relation (first ++ last) := by
  obtain ⟨input, output, reached, falseStatement⟩ := bad
  exact ⟨input, output, List.mem_append_left _ reached, falseStatement⟩

theorem other_actor_zero {Input Output : Type} (owner actor : Actor) (different : owner ≠ actor) (amount : Work) :
    steps actor ([.work owner amount] : Trace Input Output) = 0 := by
  simp [steps, eventSteps, different]

variable {Input Output : Type}
/-- A global observation clock admits finite and infinite executions. -/
abbrev History (Input Output : Type) := ℕ → Option (Event Input Output)

local instance : MeasurableSpace (Option (Event Input Output)) := ⊤

/-- Countable product sigma algebra; no discrete sigma algebra on the whole
infinite history space is assumed. -/
local instance : MeasurableSpace (History Input Output) := MeasurableSpace.pi

def prefixSteps (actor : Actor) (history : History Input Output) (depth : ℕ) : ℕ :=
  ∑ i ∈ Finset.range depth, (history i).elim 0 (eventSteps actor)

def totalSteps (actor : Actor) (history : History Input Output) : ENNReal :=
  ⨆ depth, (prefixSteps actor history depth : ENNReal)

def HistoryBad (relation : Input → Output → Prop) (history : History Input Output) : Prop :=
  ∃ time input output, history time = some (.submission input output true) ∧ ¬relation input output

/-- A law must be supplied by the actual joint execution, including adaptive
prequeries, input selection, retries and all verifier submissions. -/
def expectedAttackerWork (law : MeasureTheory.Measure (History Input Output)) : ENNReal :=
  ∫⁻ history, totalSteps .attacker history ∂law

def falseAcceptance (relation : Input → Output → Prop)
    (law : MeasureTheory.Measure (History Input Output)) : ENNReal := law {history | HistoryBad relation history}

/-- Intermediate bounds retain initial risk as an explicit term. -/
def RiskBound (relation : Input → Output → Prop) (law : MeasureTheory.Measure (History Input Output))
    (initial coefficient : ENNReal) : Prop :=
  falseAcceptance relation law ≤ initial + coefficient * expectedAttackerWork law

/-- Final goal over an explicit adversary class and implemented experiment.
No finite-work, success-floor or query-budget premise is inserted here. -/
def ExpectedWorkSecurity (Adversary : Type) (experiment : Adversary → MeasureTheory.Measure (History Input Output))
    (relation : Input → Output → Prop) (bits : ℕ) : Prop :=
  ∀ adversary, (2 : ENNReal) ^ bits * falseAcceptance relation (experiment adversary) ≤
    expectedAttackerWork (experiment adversary)

/-- Work refinement has to establish this pointwise inequality; merely
counting verifier or setup operations cannot discharge it. -/
theorem expectedWork_mono (law : MeasureTheory.Measure (History Input Output))
    (lower : History Input Output → ENNReal)
    (justified : ∀ history, lower history ≤ totalSteps .attacker history) :
    (∫⁻ trace, lower trace ∂law) ≤ expectedAttackerWork law :=
  MeasureTheory.lintegral_mono justified

end

end FormalProof4FHE.HasteBoots.SecurityExperiment
