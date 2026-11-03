module

public import FormalProof4FHE.HasteBoots.RepeatedLookupAlgebra
public import FormalProof4FHE.HasteBoots.LookupGroupedOpening

@[expose] public section

/-!
# The actual repeated algebra selector followed by native grouped PCS

The selector's computed flag gates all opening work. Its successful memory
starts the native opening loop; its own packet projection fixes every original
query/value family. No supplied enabled flag, start memory or packet family can
bypass these connections. The generic local interfaces below are instantiated
with the native algebra in the concrete soundness module.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily

namespace FormalProof4FHE.HasteBoots.RepeatedLookupPCS

noncomputable section

variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions : ℕ} {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg}
  {g : Geometry c row count repetitions}

abbrev Emission (count repetitions : ℕ) (Digest SourceMemory HelperMemory : Type) :=
  (Root count repetitions → Digest) × LookupGroupedOpening.CommitMemory count repetitions Digest SourceMemory HelperMemory
abbrev Selection := RepeatedLookupSelector.Outcome (F := F) (K := K) (Memory := Memory)
  (width := d + padding) (count := count) (n := c + row) (repetitions := repetitions)
abbrev Result := Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) ×
  ShortCircuitSequence.Outcome (Root count repetitions) (Sigma (Data F Digest Response (d + padding) heights tag (layout g))) Memory

variable [SampleableType Digest]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

def select (run : Emission count repetitions Digest SourceMemory HelperMemory → Fin repetitions → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest)
      (PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row)))
    (memory : Emission count repetitions Digest SourceMemory HelperMemory → Memory)
    (emission : Emission count repetitions Digest SourceMemory HelperMemory) :=
  RepeatedLookupSelector.program (run emission) (memory emission)

def enabled (_ : Emission count repetitions Digest SourceMemory HelperMemory)
    (selected : Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions)) := selected.accepted

def start (_ : Emission count repetitions Digest SourceMemory HelperMemory)
    (selected : Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions)) := selected.memory.memory

def program (enc : MerkleOracle.Encoding Input Digest (List F)) (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (run : Emission count repetitions Digest SourceMemory HelperMemory → Fin repetitions → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row)))
    (memory : Emission count repetitions Digest SourceMemory HelperMemory → Memory)
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count repetitions Digest SourceMemory HelperMemory) :=
  HeterogeneousBatchOpening.continuation enc domain
    (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior)
    (select run memory) enabled start (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange repetitions)) emission

/-- Final native PCS acceptance forces a real accepted selector, with its
actual supported execution and exact retained result. -/
theorem support_accepts (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (run : Emission count repetitions Digest SourceMemory HelperMemory → Fin repetitions → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row)))
    (memory : Emission count repetitions Digest SourceMemory HelperMemory → Memory)
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count repetitions Digest SourceMemory HelperMemory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : Result (F := F) (K := K) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (repetitions := repetitions) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : last ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (program enc basis shape domain fallback run memory behavior emission)).run initial))
    (accepted : last.1.2.accepted = true) :
    ∃ earlier ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (select run memory emission)).run initial), last.1.1 = earlier.1 ∧ earlier.1.accepted = true := by
  rw [program, HeterogeneousBatchOpening.continuation, SharedContinuation.support_program] at supported
  obtain ⟨earlier, earlierSupported, later, laterSupported, equal⟩ := supported
  subst last
  cases flag : earlier.1.accepted with
  | false =>
    simp only [enabled, flag, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at laterSupported
    have equal := eq_of_mem_support_pure _ laterSupported
    subst later
    exact (Bool.false_ne_true accepted).elim
  | true => exact ⟨earlier, earlierSupported, rfl, flag⟩

/-- The accepted selected packet gives either its scalar event, a native PCS
arithmetic event, or the common availability exception in this exact run. -/
theorem reduce_acceptance (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (run : Emission count repetitions Digest SourceMemory HelperMemory → Fin repetitions → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row)))
    (memory : Emission count repetitions Digest SourceMemory HelperMemory → Memory)
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count repetitions Digest SourceMemory HelperMemory)
    (checkpoint : RecordedHeterogeneousBatchOpening.Snapshots Input Digest heights tag)
    (rootEq : ∀ root, (checkpoint root).root = emission.1 root)
    (selected : Fin repetitions)
    (arithmetic : PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row) → Prop)
    (localLaw : ∀ incoming state native,
      native ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (run emission selected incoming)).run state) → ∀ packet retainedMemory,
      native.1.2 = some (packet, retainedMemory) → arithmetic native.1 ∨
        LookupPairTerminal.WrongOpenings basis shape
          (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
          (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected)
          packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (recorded : ∀ root, ⟨tag root, checkpoint root⟩ ∈ initial.checkpoints.checkpoints)
    (last : Result (F := F) (K := K) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (repetitions := repetitions) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : last ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (program enc basis shape domain fallback run memory behavior emission)).run initial))
    (accepted : last.1.2.accepted = true) :
    SharedSequence.AnyBad (fun index earlier => index = selected ∧ arithmetic earlier) last.1.1.results ∨
      SharedSequence.AnyBad (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius
        (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results ∨
      CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) last.2 := by
  obtain ⟨earlier, earlierSupported, equal, passed⟩ := support_accepts enc dummy basis shape domain fallback run memory behavior emission initial last supported accepted
  have alternatives := RepeatedLookupCompletion.accepted_selected_or_wrong enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (run emission) selected arithmetic
    (fun packet => LookupPairTerminal.WrongOpenings basis shape
      (sourceTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint))
      (helperTables domain capacity radius (LookupGroupedOpening.words enc dummy g checkpoint) selected)
      packet.sumClaim packet.zeroClaim packet.values.sources packet.values.helper)
    localLaw (memory emission) fallback initial earlier earlierSupported passed
  rw [← equal] at alternatives
  obtain scalarBad | wrongPacket := alternatives
  · exact Or.inl scalarBad
  right
  have wrong := (LookupGroupedOpening.wrong_iff basis shape (RepeatedLookupSelector.packets fallback) domain capacity radius behavior
    enc dummy emission checkpoint last).mpr ⟨accepted, selected, wrongPacket⟩
  exact RecordedHeterogeneousBatchOpening.reduce_wrong enc dummy
    (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange repetitions))
    (StagedHeterogeneousBatchOpening.factors_complete _ _ (fun i => List.mem_finRange i) (fun i => List.mem_finRange i))
    domain capacity radius (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior)
    (select run memory) enabled start emission checkpoint rootEq initial recorded last supported wrong

variable [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

/-- Conditional scalar arithmetic and native PCS arithmetic share the actual
selector/opening run. Native PCS security is derived, not a local certificate. -/
theorem arithmetic_bound [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : Module.Basis (Fin (d + padding)) F L)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (fallback : PreparedLookupPair.Packet F K (d + padding) count (c + row))
    (run : Emission count repetitions Digest SourceMemory HelperMemory → Fin repetitions → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row)))
    (memory : Emission count repetitions Digest SourceMemory HelperMemory → Memory)
    (behavior : Emission count repetitions Digest SourceMemory HelperMemory →
      Selection (F := F) (K := K) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row) (count := count) (repetitions := repetitions) →
      (root : Root count repetitions) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count repetitions Digest SourceMemory HelperMemory)
    (checkpoint : RecordedHeterogeneousBatchOpening.Snapshots Input Digest heights tag)
    (selected : Fin repetitions) (arithmetic : PreparedLookupSoundness.Output F K Memory (d + padding) count (c + row) → Prop)
    (epsilon : ENNReal)
    (localBound : ∀ incoming state,
      Pr{let native ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (run emission selected incoming)).run state}[arithmetic native.1] ≤ epsilon)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (small : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    Pr{let last ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (program enc basis shape domain fallback run memory behavior emission)).run initial}[
        SharedSequence.AnyBad (fun index earlier => index = selected ∧ arithmetic earlier) last.1.1.results ∨
        SharedSequence.AnyBad (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius
          (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results] ≤
      epsilon + ((StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange repetitions)).map
        (fun root => JointMatrixOpening.error (K := L) (m := g.m root) (b := d + padding) (queries := g.queries root) (domain root) (radius root))).sum := by
  have native := RecordedHeterogeneousBatchOpening.arithmetic_bound analysisBasis enc dummy
    (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange repetitions)) domain enough capacity radius
    (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior)
    (select run memory) enabled start emission checkpoint initial small
  have scalar := RepeatedLookupSelector.selected_arithmetic_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (run emission) selected arithmetic epsilon localBound (memory emission) initial
  have retained := SharedContinuation.earlier_event_le enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (select run memory emission)
    (fun query => if enabled emission query then
      DependentShortCircuitSequence.program
        (fun root => NativeBatchVerifier.step (protocol enc heights tag (layout g) domain
          (LookupGroupedOpening.build basis shape g (RepeatedLookupSelector.packets fallback) behavior) emission query root))
        (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange repetitions)) (start emission query)
      else pure ⟨[], start emission query, false⟩) initial
    (fun query => SharedSequence.AnyBad (fun index earlier => index = selected ∧ arithmetic earlier) query.results)
  exact (prEvent_or_le _ _ _).trans (add_le_add (retained.trans scalar) native)

end

end FormalProof4FHE.HasteBoots.RepeatedLookupPCS
