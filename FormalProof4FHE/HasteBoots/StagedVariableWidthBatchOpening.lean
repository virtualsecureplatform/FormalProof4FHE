module

public import FormalProof4FHE.HasteBoots.StagedCommitmentPrefix
public import FormalProof4FHE.HasteBoots.RecordedVariableWidthBatchOpening

@[expose] public section

/-!
# Original source roots before pair challenges, helpers afterwards

The source phase emits and records original roots. The adaptive middle phase
may draw pair challenges and commit all helpers, whose roots are then recorded.
Only then does algebra/query selection and native grouped PCS verification run.
The source and helper words use their own original logs; their equality at a
later prefix is neither assumed nor needed. One complete-run charge covers both.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening

namespace FormalProof4FHE.HasteBoots.StagedVariableWidthBatchOpening

noncomputable section

variable {F Source Helper Input Digest Cfg Response Memory SourceMemory HelperMemory QueryData : Type}
  {width : (Source ⊕ Helper) → ℕ} [DecidableEq Input] [DecidableEq Digest]

abbrev SourceEmission (Source Digest SourceMemory : Type) := (Source → Digest) × SourceMemory
abbrev HelperEmission (Helper Digest HelperMemory : Type) := (Helper → Digest) × HelperMemory
abbrev CommitMemory (Source Helper Digest SourceMemory HelperMemory : Type) :=
  SourceEmission Source Digest SourceMemory × HelperEmission Helper Digest HelperMemory

def emission (first : SourceEmission Source Digest SourceMemory) (second : HelperEmission Helper Digest HelperMemory) :
    ((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory :=
  (Sum.elim first.1 second.1, first, second)

def factors (sources : List Source) (helpers : List Helper) : List (Source ⊕ Helper) :=
  helpers.map Sum.inr ++ sources.map Sum.inl

theorem factors_complete (sources : List Source) (helpers : List Helper)
    (sourceComplete : ∀ source, source ∈ sources) (helperComplete : ∀ helper, helper ∈ helpers) :
    ∀ factor, factor ∈ factors sources helpers := by
  intro factor
  cases factor with
  | inl source => exact List.mem_append_right _ (List.mem_map_of_mem (sourceComplete source))
  | inr helper => exact List.mem_append_left _ (List.mem_map_of_mem (helperComplete helper))

def sourceRequests (tag : (Source ⊕ Helper) → Cfg) (sources : List Source)
    (first : SourceEmission Source Digest SourceMemory) : List (Cfg × Digest) :=
  sources.map (fun source => (tag (.inl source), first.1 source))

def helperRequests (tag : (Source ⊕ Helper) → Cfg) (helpers : List Helper)
    (_ : SourceEmission Source Digest SourceMemory) (second : HelperEmission Helper Digest HelperMemory) : List (Cfg × Digest) :=
  helpers.map (fun helper => (tag (.inr helper), second.1 helper))

def snapshots (heights : Cfg → ℕ) (tag : (Source ⊕ Helper) → Cfg)
    (first : SourceEmission Source Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission Helper Digest HelperMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    RecordedVariableWidthBatchOpening.Snapshots Input Digest heights tag :=
  fun factor => match factor with
  | .inl source => ⟨first.1.1 source, first.2.hash.log⟩
  | .inr helper => ⟨second.1.1 helper, second.2.hash.log⟩

omit [DecidableEq Input] [DecidableEq Digest] in
/-- Every chosen checkpoint belongs to its original emitted root, independently
of collisions, payload availability or whether either phase is honest. -/
theorem snapshots_roots (heights : Cfg → ℕ) (tag : (Source ⊕ Helper) → Cfg)
    (first : SourceEmission Source Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission Helper Digest HelperMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    ∀ factor, (snapshots heights tag first second factor).root = (emission first.1 second.1).1 factor := by
  intro factor
  cases factor <;> rfl

variable [SampleableType Digest]

/-- Source history survives the actual adaptive middle program and helper
recording; helper snapshots use exactly the later helper-commit log. -/
theorem snapshots_recorded (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : (Source ⊕ Helper) → Cfg) (sources : List Source) (helpers : List Helper)
    (sourceComplete : ∀ source, source ∈ sources) (helperComplete : ∀ helper, helper ∈ helpers)
    (helperCommit : SourceEmission Source Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission Helper Digest HelperMemory))
    (first : SourceEmission Source Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : HelperEmission Helper Digest HelperMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : second ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (helperCommit first.1)).run (RecordRoots.state _ (sourceRequests tag sources first.1) first.2))) :
    ∀ factor, ⟨tag factor, snapshots heights tag first second factor⟩ ∈
      (RecordRoots.state _ (helperRequests tag helpers first.1 second.1) second.2).checkpoints.checkpoints := by
  intro factor
  cases factor with
  | inl source =>
    have earlier := RecordRoots.recorded (fun cfg => Skeleton.perfect (heights cfg))
      (sourceRequests tag sources first.1) first.2 (tag (.inl source), first.1.1 source)
      (List.mem_map_of_mem (sourceComplete source))
    have retained := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun cfg => Skeleton.perfect (heights cfg)) (tag (.inl source)) (snapshots heights tag first second (.inl source))
      (helperCommit first.1) (RecordRoots.state _ (sourceRequests tag sources first.1) first.2) earlier second supported
    exact RecordRoots.retains _ _ second.2 _ _ retained
  | inr helper =>
    exact RecordRoots.recorded _ (helperRequests tag helpers first.1 second.1) second.2
      (tag (.inr helper), second.1.1 helper) (List.mem_map_of_mem (helperComplete helper))

variable [Field F] [DecidableEq F]
  {heights : Cfg → ℕ} {tag : (Source ⊕ Helper) → Cfg} {layout : (Source ⊕ Helper) → Layout}
  [∀ factor, SampleableType (TestMatrix F (2 ^ (layout factor).front) (width factor))]
  [∀ factor, SampleableType (Fin (layout factor).queries → Fin (2 ^ heights (tag factor)))]

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      QueryData → (factor : Source ⊕ Helper) → Protocol F Input Digest Cfg Response Memory width heights tag layout factor)
    (selectQuery : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Bool)
    (start : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Memory)
    (sources : List Source) (helpers : List Helper)
    (first : SourceEmission Source Digest SourceMemory) (second : HelperEmission Helper Digest HelperMemory) :=
  VariableWidthBatchOpening.continuation enc domain build selectQuery enabled start (factors sources helpers) (emission first second)

variable {K : (Source ⊕ Helper) → Type} [Fintype Digest] [∀ factor, Field (K factor)] [∀ factor, Algebra F (K factor)] [Fintype F]
  [∀ factor, Fintype (K factor)] [∀ factor, DecidableEq (K factor)]
  [∀ factor, SampleableType ((Fin (2 ^ (layout factor).front) × Fin (width factor)) → K factor)]

/-- Sources freeze before the adaptive middle phase, helpers afterwards. The
native arithmetic bounds and global authentication charge are derived for that
actual two-prefix execution, without a source-stability equality assumption. -/
theorem soundness_from_empty [∀ factor, NeZero (width factor)] [∀ factor, NeZero (layout factor).m]
    (basis : ∀ factor, Module.Basis (Fin (width factor)) F (K factor))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sources : List Source) (helpers : List Helper)
    (sourceComplete : ∀ source, source ∈ sources) (helperComplete : ∀ helper, helper ∈ helpers)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (enough : ∀ factor, (layout factor).m ≤ Fintype.card (Fin (2 ^ heights (tag factor))))
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * width factor) (radius : (Source ⊕ Helper) → ℕ)
    (build : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      QueryData → (factor : Source ⊕ Helper) → Protocol F Input Digest Cfg Response Memory width heights tag layout factor)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission Source Digest SourceMemory))
    (helperCommit : SourceEmission Source Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission Helper Digest HelperMemory))
    (selectQuery : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Bool)
    (start : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Memory)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K factor) (domain factor)) (layout factor).m :
        Set (Fin (2 ^ heights (tag factor)) → K factor)) : ℚ≥0) / 3) :
    let next := continuation enc domain build selectQuery enabled start sources helpers
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (sourceRequests tag sources) (helperRequests tag helpers) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        RecordedVariableWidthBatchOpening.Wrong enc dummy domain capacity radius build (emission outcome.1.1 outcome.2.1.1)
          (snapshots heights tag outcome.1 outcome.2.1) outcome.2.2] ≤
      ((factors sources helpers).map (fun factor => JointMatrixOpening.error (K := K factor) (m := (layout factor).m) (b := width factor)
        (queries := (layout factor).queries) (domain factor) (radius factor))).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program (sourceRequests tag sources) (helperRequests tag helpers) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  apply StagedCommitmentPrefix.event_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (sourceRequests tag sources) (helperRequests tag helpers) sourceCommit helperCommit
    (continuation enc domain build selectQuery enabled start sources helpers)
    (fun first second last => RecordedVariableWidthBatchOpening.Wrong enc dummy domain capacity radius build
      (emission first.1 second.1) (snapshots heights tag first second) last)
    (fun first second last => SharedSequence.AnyBad
      (fun _ => RecordedVariableWidthBatchOpening.Arithmetic enc dummy domain capacity radius build
        (emission first.1 second.1) (snapshots heights tag first second) last.1.1) last.1.2.results) _
  · intro first second
    exact RecordedVariableWidthBatchOpening.arithmetic_bound basis enc dummy (factors sources helpers) domain enough capacity radius
      build selectQuery enabled start (emission first.1 second.1) (snapshots heights tag first second) _ small
  · intro first _ second secondSupported last lastSupported wrong
    exact RecordedVariableWidthBatchOpening.reduce_wrong enc dummy (factors sources helpers)
      (factors_complete sources helpers sourceComplete helperComplete) domain capacity radius build selectQuery enabled start
      (emission first.1 second.1) (snapshots heights tag first second) (snapshots_roots heights tag first second) _
      (snapshots_recorded enc dummy heights tag sources helpers sourceComplete helperComplete helperCommit first second secondSupported)
      last lastSupported wrong

end

end FormalProof4FHE.HasteBoots.StagedVariableWidthBatchOpening
