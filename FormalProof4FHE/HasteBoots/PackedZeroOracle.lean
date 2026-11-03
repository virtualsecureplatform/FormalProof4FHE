module

public import FormalProof4FHE.HasteBoots.PackedSumcheckOracle
public import FormalProof4FHE.HasteBoots.PackedZeroTerminal
public import FormalProof4FHE.HasteBoots.IndexedPublicEquality

@[expose] public section

/-!
# Source-independent packed ZeroCheck on the shared oracle

Equality points precede an arbitrary adaptive first-message program in this
private-coin experiment. A rejected boundary skips mixing, callbacks and all
remaining sumcheck work. Accepted subclaims retain the special first matrix,
ordinary query and verifier-computed public EQ terminal; only original factors
will require authentication. Native verification prechecks its static message
before transcript-derived equality points; that preflight/Fiat--Shamir/Rust
refinement is separate from this interactive arithmetic interface.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PackedZeroOracle

noncomputable section

attribute [local instance] Classical.propDecidable

structure Subclaim (F : Type) (k n : ℕ) where
  points : PackedZeroReduction.Points F n k
  coins : PackedZeroReduction.Coins F k
  rest : PackedSumcheckSubclaim.Subclaim F k n

variable {F Factor Term FirstMessage RoundMessage Memory Cfg Input Digest Payload : Type}
  [Field F] {k n : ℕ}

namespace Subclaim

def query (nodes : PackedSumcheckRound.Node k ↪ F) (claim : Subclaim F k n) : Query F k (n + 1) :=
  .cons (PackedSumcheckRound.challengePair nodes claim.coins.2) claim.rest.query

def equality (claim : Subclaim F k n) : Fin k → F :=
  IndexedPublicEquality.evaluate claim.rest.query claim.points claim.coins.1

def Truthful [Fintype Term] (nodes : PackedSumcheckRound.Node k ↪ F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) (claim : Subclaim F k n) : Prop :=
  claim.rest.Truthful (fun term => arity term + 1) coefficient (PackedZeroFirst.reducedIndices arity indices)
    (PackedZeroCube.reducedTables nodes tables claim.points claim.coins)

/-- The original factors follow the full query; the public EQ factor follows
only the suffix query and the native ordered mixing-column recurrence. -/
theorem reduced_folds (nodes : PackedSumcheckRound.Node k ↪ F)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) (claim : Subclaim F k n) :
    (fun factor => claim.rest.query.fold (PackedZeroCube.reducedTables nodes tables claim.points claim.coins factor)) =
      Sum.elim (fun factor => (query nodes claim).fold (tables factor)) (fun _ => equality claim) := by
  funext factor
  cases factor with
  | inl factor => rfl
  | inr tag => exact IndexedPublicEquality.fold_eq_evaluate claim.rest.query claim.points claim.coins.1

/-- Native terminal checking uses no supplied EQ value or EQ opening. -/
def check [DecidableEq F] [Fintype Term] (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (values : Factor → Fin k → F) (claim : Subclaim F k n) : Bool :=
  PackedZeroTerminal.check arity coefficient indices values (equality claim) claim.rest.expected

theorem check_folds_iff [DecidableEq F] [Fintype Term] (nodes : PackedSumcheckRound.Node k ↪ F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) (claim : Subclaim F k n) :
    check arity coefficient indices (fun factor => (query nodes claim).fold (tables factor)) claim = true ↔
      Truthful nodes arity coefficient indices tables claim := by
  rw [check, PackedZeroTerminal.check_iff]
  have expressions (lane : Fin k) :
      PackedSumcheckRound.expression (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices)
        (fun factor => claim.rest.query.fold (PackedZeroCube.reducedTables nodes tables claim.points claim.coins factor) lane) =
      PackedSumcheckRound.expression arity coefficient indices
        (fun factor => (query nodes claim).fold (tables factor) lane) * equality claim lane := by
    have values :
        (fun factor => claim.rest.query.fold (PackedZeroCube.reducedTables nodes tables claim.points claim.coins factor) lane) =
          Sum.elim (fun factor => (query nodes claim).fold (tables factor) lane) (fun _ => equality claim lane) := by
      funext factor
      have folded := congrFun (reduced_folds nodes tables claim) factor
      cases factor <;> exact congrFun folded lane
    rw [values, PackedZeroFirst.reduced_expression, mul_comm]
  constructor
  · intro checked
    change claim.rest.expected = _
    exact funext (fun lane => ((expressions lane).trans (checked lane)).symm)
  · intro truthful lane
    have checked := congrFun truthful lane
    exact (expressions lane).symm.trans checked.symm

/-- A checked terminal either states the true reduced relation or contains a
wrong original-factor value. The public EQ factor is computed, never supplied. -/
theorem checked_truthful_or_wrong [DecidableEq F] [Fintype Term]
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (values : Factor → Fin k → F) (claim : Subclaim F k n)
    (checked : check arity coefficient indices values claim = true) :
    Truthful nodes arity coefficient indices tables claim ∨
      ∃ factor, values factor ≠ (query nodes claim).fold (tables factor) := by
  classical
  by_cases correct : ∀ factor, values factor = (query nodes claim).fold (tables factor)
  · left
    have equal : values = fun factor => (query nodes claim).fold (tables factor) := funext correct
    rw [equal] at checked
    exact (check_folds_iff nodes arity coefficient indices tables claim).mp checked
  · exact Or.inr (not_forall.mp correct)

end Subclaim

def wrapResult (points : PackedZeroReduction.Points F n k) (coins : PackedZeroReduction.Coins F k)
    (result : Option (PackedSumcheckSubclaim.Subclaim F k n × Memory)) : Option (Subclaim F k n × Memory) :=
  result.map (fun entry => (⟨points, coins, entry.1⟩, entry.2))

def TruthfulResult [Fintype Term] (nodes : PackedSumcheckRound.Node k ↪ F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) : Option (Subclaim F k n × Memory) → Prop
  | none => False
  | some entry => entry.1.Truthful nodes arity coefficient indices tables

theorem truthful_wrap_iff [Fintype Term] (nodes : PackedSumcheckRound.Node k ↪ F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (points : PackedZeroReduction.Points F n k) (coins : PackedZeroReduction.Coins F k)
    (result : Option (PackedSumcheckSubclaim.Subclaim F k n × Memory)) :
    TruthfulResult nodes arity coefficient indices tables (wrapResult points coins result) ↔
      PackedSumcheckOracle.TruthfulResult (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices) (PackedZeroCube.reducedTables nodes tables points coins) result := by
  cases result <;> rfl

variable [SampleableType (PackedZeroReduction.Points F n k)]
  [SampleableType (PackedZeroReduction.Coins F k)] [SampleableType (Fin k → F)]

/-- No source tables are inputs to this operational verifier. -/
def program (nodes : PackedSumcheckRound.Node k ↪ F)
    (interpretFirst : FirstMessage → Fin k → Polynomial F) (interpretRound : RoundMessage → Polynomial F)
    (firstRespond : PackedZeroReduction.Points F n k → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (FirstMessage × Memory))
    (afterFirst : PackedZeroReduction.Points F n k → FirstMessage × Memory → PackedZeroReduction.Coins F k →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (RoundMessage × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (memory : Memory) : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)) := do
  let points ← PrivateSampling.embed Cfg Input Digest ($ᵗ (PackedZeroReduction.Points F n k))
  let first ← firstRespond points memory
  if PackedZeroFirst.Boundary nodes (interpretFirst first.1) then
    let coins ← PrivateSampling.embed Cfg Input Digest ($ᵗ (PackedZeroReduction.Coins F k))
    let nextState ← afterFirst points first coins
    let result ← PackedSumcheckOracle.program nodes interpretRound send afterChallenge n
      (PackedZeroFirst.reduce (interpretFirst first.1) coins.1 coins.2) nextState
    pure (wrapResult points coins result)
  else pure none

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Exact law of the actual shared run, including first-message rejection
before mixing and every accepted-path callback and ordinary round. -/
theorem run_program (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F)
    (interpretFirst : FirstMessage → Fin k → Polynomial F) (interpretRound : RoundMessage → Polynomial F)
    (firstRespond : PackedZeroReduction.Points F n k → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (FirstMessage × Memory))
    (afterFirst : PackedZeroReduction.Points F n k → FirstMessage × Memory → PackedZeroReduction.Coins F k →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (RoundMessage × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes interpretFirst interpretRound firstRespond afterFirst send afterChallenge memory)).run state =
    (do
      let points ← $ᵗ (PackedZeroReduction.Points F n k)
      let first ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (firstRespond points memory)).run state
      if PackedZeroFirst.Boundary nodes (interpretFirst first.1.1) then
        let coins ← $ᵗ (PackedZeroReduction.Coins F k)
        let nextState ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (afterFirst points first.1 coins)).run first.2
        let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (PackedSumcheckOracle.program nodes interpretRound send afterChallenge n
            (PackedZeroFirst.reduce (interpretFirst first.1.1) coins.1 coins.2) nextState.1)).run nextState.2
        pure (wrapResult points coins result.1, result.2)
      else pure (none, first.2)) := by
  rw [program, simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp, bind_map_left]
  congr 1
  funext points
  rw [simulateQ_bind, StateT.run_bind]
  congr 1
  funext first
  by_cases checked : PackedZeroFirst.Boundary nodes (interpretFirst first.1.1)
  · simp only [checked, reduceIte, simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp,
      bind_map_left, simulateQ_pure, StateT.run_pure]
  · simp only [checked, reduceIte, simulateQ_pure, StateT.run_pure]

end

end FormalProof4FHE.HasteBoots.PackedZeroOracle
