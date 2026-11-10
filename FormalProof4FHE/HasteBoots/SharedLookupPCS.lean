module
public import FormalProof4FHE.HasteBoots.SharedLookupTerminalSoundness
public import FormalProof4FHE.HasteBoots.SharedLookupGroupedOpening
@[expose] public section

/-! One computed shared terminal selection followed by original grouped PCS.
Only a returned packet enables openings; its own vectors fix queries/values
and its actual bound memory starts the opening loop. All sources occur once
and all helpers occur once, in native helper-before-source order. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening
open FormalProof4FHE.HasteBoots.SharedLookupOpeningFamily
namespace FormalProof4FHE.HasteBoots.SharedLookupPCS
noncomputable section
variable {F K L Cfg Input Digest Response Memory SourceMemory HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count jobs : ℕ} {heights : Cfg → ℕ} {tag : Root count jobs → Cfg}
  {g : Geometry c row count jobs}

abbrev Emission (count jobs : ℕ) (Digest SourceMemory HelperMemory : Type) :=
  (Root count jobs → Digest) × SharedLookupGroupedOpening.CommitMemory count jobs Digest SourceMemory HelperMemory
abbrev Selection (F K Memory : Type) (width count jobs n : ℕ) :=
  SharedLookupTerminalSoundness.Result F K Memory width count jobs n
abbrev Result := Selection F K Memory (d + padding) count jobs (c + row) ×
  ShortCircuitSequence.Outcome (Root count jobs)
    (Sigma (Data F Digest Response (d + padding) heights tag (layout g))) Memory

def packets (fallback : Packet F K (d + padding) count (c + row) jobs)
    (selection : Selection F K Memory (d + padding) count jobs (c + row)) :=
  (selection.2.map Prod.fst).getD fallback

def enabled (_ : Emission count jobs Digest SourceMemory HelperMemory)
    (selection : Selection F K Memory (d + padding) count jobs (c + row)) := selection.2.isSome

def start (_ : Emission count jobs Digest SourceMemory HelperMemory)
    (selection : Selection F K Memory (d + padding) count jobs (c + row)) :=
  selection.2.elim selection.1.1.2 Prod.snd

variable [SampleableType Digest]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (d + padding))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]

def program (enc : MerkleOracle.Encoding Input Digest (List F)) (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (run : Emission count jobs Digest SourceMemory HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Selection F K Memory (d + padding) count jobs (c + row)))
    (behavior : Emission count jobs Digest SourceMemory HelperMemory →
      Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count jobs Digest SourceMemory HelperMemory) :=
  HeterogeneousBatchOpening.continuation enc domain
    (SharedLookupGroupedOpening.build basis shape g (packets fallback) behavior) run enabled start
    (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange jobs)) emission

/-- Final PCS acceptance forces an actual successful terminal selection.
Fallback packet data cannot enable or start an accepted opening run. -/
theorem support_accepts (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (run : Emission count jobs Digest SourceMemory HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Selection F K Memory (d + padding) count jobs (c + row)))
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count jobs Digest SourceMemory HelperMemory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (last : Result (F := F) (K := K) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : last ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (program enc basis shape domain fallback run behavior emission)).run initial))
    (accepted : last.1.2.accepted = true) :
    ∃ earlier ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (run emission)).run initial), ∃ packet memory, last.1.1 = earlier.1 ∧ earlier.1.2 = some (packet,memory) := by
  rw [program,HeterogeneousBatchOpening.continuation,SharedContinuation.support_program] at supported
  obtain ⟨earlier,earlierSupported,later,laterSupported,equal⟩ := supported
  subst last
  cases returned : earlier.1.2 with
  | none =>
    simp only [enabled,returned,Option.isSome_none,Bool.false_eq_true,reduceIte,simulateQ_pure,StateT.run_pure] at laterSupported
    have equal := eq_of_mem_support_pure _ laterSupported
    subst later
    exact (Bool.false_ne_true accepted).elim
  | some entry => exact ⟨earlier,earlierSupported,entry.1,entry.2,rfl,returned⟩

/-- Successful terminal and PCS checks reduce to scalar arithmetic, native
PCS arithmetic, or the common availability exception on this same run. -/
theorem reduce_acceptance {columns : Fin jobs → ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (coverage : ∀ source, ∃ job column, slots job column = source)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count jobs → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (run : Emission count jobs Digest SourceMemory HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Selection F K Memory (d + padding) count jobs (c + row)))
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count jobs Digest SourceMemory HelperMemory)
    (checkpoint : RecordedHeterogeneousBatchOpening.Snapshots Input Digest heights tag)
    (rootEq : ∀ root, (checkpoint root).root = emission.1 root)
    (arithmetic : Selection F K Memory (d + padding) count jobs (c + row) → Prop)
    (localLaw : ∀ state native,
      native ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (run emission)).run state) → ∀ packet retainedMemory, native.1.2 = some (packet,retainedMemory) → arithmetic native.1 ∨
        SharedLookupTerminalReduction.Wrong basis shape slots
          (sourceTables domain capacity radius (SharedLookupGroupedOpening.words enc dummy g checkpoint))
          (helperTables domain capacity radius (SharedLookupGroupedOpening.words enc dummy g checkpoint)) packet)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (recorded : ∀ root, ⟨tag root,checkpoint root⟩ ∈ initial.checkpoints.checkpoints)
    (last : Result (F := F) (K := K) (Response := Response) (Memory := Memory) (d := d) (padding := padding) (c := c) (row := row)
      (count := count) (jobs := jobs) (heights := heights) (tag := tag) (g := g) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : last ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (program enc basis shape domain fallback run behavior emission)).run initial))
    (accepted : last.1.2.accepted = true) :
    arithmetic last.1.1 ∨
      SharedSequence.AnyBad (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius
        (SharedLookupGroupedOpening.build basis shape g (packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results ∨
      CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) last.2 := by
  obtain ⟨earlier,earlierSupported,packet,memory,equal,returned⟩ :=
    support_accepts enc dummy basis shape domain fallback run behavior emission initial last supported accepted
  have alternatives := localLaw initial earlier earlierSupported packet memory returned
  rw [← equal] at alternatives
  rcases alternatives with scalar | wrongPacket
  · exact Or.inl scalar
  right
  have packetEq : packets fallback last.1.1 = packet := by simp only [packets,equal,returned,Option.map_some,Option.getD_some]
  have wrong := (SharedLookupGroupedOpening.wrong_iff slots coverage basis shape (packets fallback) domain capacity radius behavior
    enc dummy emission checkpoint last).mpr ⟨accepted,by simpa only [packetEq,SharedLookupTerminalReduction.Wrong] using wrongPacket⟩
  exact RecordedHeterogeneousBatchOpening.reduce_wrong enc dummy
    (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange jobs))
    (StagedHeterogeneousBatchOpening.factors_complete _ _ (fun i => List.mem_finRange i) (fun i => List.mem_finRange i))
    domain capacity radius (SharedLookupGroupedOpening.build basis shape g (packets fallback) behavior)
    run enabled start emission checkpoint rootEq initial recorded last supported wrong

variable [Field L] [Algebra F L] [Fintype F] [Fintype L] [DecidableEq L]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (d + padding)) → L)]

/-- Scalar and native PCS arithmetic bounds retain the actual common-point
selection/opening execution. Each original root contributes one PCS term. -/
theorem arithmetic_bound [NeZero (d + padding)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : Module.Basis (Fin (d + padding)) F L)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count jobs → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) jobs)
    (run : Emission count jobs Digest SourceMemory HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Selection F K Memory (d + padding) count jobs (c + row)))
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → Selection F K Memory (d + padding) count jobs (c + row) →
      (root : Root count jobs) → Protocol F Input Digest Cfg Response Memory (d + padding) heights tag (layout g) root)
    (emission : Emission count jobs Digest SourceMemory HelperMemory)
    (checkpoint : RecordedHeterogeneousBatchOpening.Snapshots Input Digest heights tag)
    (arithmetic : Selection F K Memory (d + padding) count jobs (c + row) → Prop) (epsilon : ENNReal)
    (localBound : ∀ state,
      Pr{let native ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (run emission)).run state}[arithmetic native.1] ≤ epsilon)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (small : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L)) : ℚ≥0) / 3) :
    Pr{let last ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (program enc basis shape domain fallback run behavior emission)).run initial}[
        arithmetic last.1.1 ∨ SharedSequence.AnyBad
          (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius
            (SharedLookupGroupedOpening.build basis shape g (packets fallback) behavior) emission checkpoint last.1.1) last.1.2.results] ≤
      epsilon + ((StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange jobs)).map
        (fun root => JointMatrixOpening.error (K := L) (m := g.m root) (b := d + padding) (queries := g.queries root) (domain root) (radius root))).sum := by
  have native := RecordedHeterogeneousBatchOpening.arithmetic_bound analysisBasis enc dummy
    (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange jobs)) domain enough capacity radius
    (SharedLookupGroupedOpening.build basis shape g (packets fallback) behavior) run enabled start emission checkpoint initial small
  have retained := SharedContinuation.earlier_event_le enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (run emission) (fun query => if enabled emission query then
      DependentShortCircuitSequence.program
        (fun root => NativeBatchVerifier.step (protocol enc heights tag (layout g) domain
          (SharedLookupGroupedOpening.build basis shape g (packets fallback) behavior) emission query root))
        (StagedHeterogeneousBatchOpening.factors (List.finRange count) (List.finRange jobs)) (start emission query)
      else pure ⟨[],start emission query,false⟩) initial arithmetic
  exact (prEvent_or_le _ _ _).trans (add_le_add (retained.trans (localBound initial)) native)
end
end FormalProof4FHE.HasteBoots.SharedLookupPCS
