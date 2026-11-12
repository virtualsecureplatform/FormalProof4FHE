module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondReconstruction
@[expose] public section

/-! Second-reconstruction risk is averaged over actual accepted first-comparison
returns, with original roots, actual returned memory and one ambient history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondReconstructionProbability
open PackedPBSSecondReconstruction (beforeState reconstruction finalState)
open PackedPBSFirstComparisons (erasePrior)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
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


/-- A fixed predecessor event cannot gain probability through later
reconstruction work, including stopped/nonreturning continuations. -/
theorem earlier_event_le (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Reached s → Prop) :
    Pr{let outcome ← (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)}[
      event outcome.1] ≤
    Pr{let before ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)}[event before] := by
  unfold PackedPBSSecondReconstruction.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  cases equal : before.2 with
  | none => simp [PackedPBSSecondReconstruction.finish,equal,prEvent_norm,outside]
  | some compared =>
    by_cases passed : compared.2.2.1.2.accepted = true
    · simp only [PackedPBSSecondReconstruction.finish,equal,passed,ite_true,prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => outside accepted)
    · simp [PackedPBSSecondReconstruction.finish,equal,passed,prEvent_norm,outside]

/-- Earlier safe risks transfer to the extended final exception without
charging authentication again or requiring a lossless reconstruction prover. -/
theorem earlier_safe_event_le (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Reached s → Prop) :
    Pr{let outcome ← (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (finalState s outcome)] ≤
    Pr{let before ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)}[
      event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (beforeState s before)] := by
  have included := prEvent_mono_of_support
    (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (finalState s outcome))
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (beforeState s outcome.1))
    (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro bad
      exact accepted.2 (PackedPBSSecondReconstruction.bad_persistent length psi primitive family inputs base hs nodesEnough radix linearBase
        dummy s secondBase initial outcome supported bad))
  exact included.trans (earlier_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial
    (fun before => event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (beforeState s before)))


variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType ((Fin (2^front) × Fin b) → P)]

/-- All original second-half linear relations and source openings have their
derived conditional rate on the extended prefix, outside the same exception. -/
theorem safe_second_risk_bound [NeZero m] [NeZero b]
    (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) P)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, s.heights ((secondBase memory).tag factor) = height)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (secondBase memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := P) (m := m) (b := b) (queries := queries)
        (secondBase memory).domain radius ≤ epsilon)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape s.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)}[
      ∃ compared child, outcome.1.2 = some compared ∧ outcome.2 = some child ∧
        AmbientLinear.OriginalRisk s.heights
          (reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
          dummy capacity radius child ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) child.2.2] ≤ epsilon := by
  unfold PackedPBSSecondReconstruction.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have incoming := PackedPBSSecondReconstruction.before_audited length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy s initial audited compatible restricted before supported
  cases equal : before.2 with
  | none => simp [PackedPBSSecondReconstruction.finish,equal,prEvent_norm]
  | some compared =>
    by_cases passed : compared.2.2.1.2.accepted = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape s.heights) compared.2.2.2 := by
        simpa only [beforeState,PackedPBSFirstComparisons.finalState,equal] using incoming
      let childScheme := reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory
      have conditional := AmbientDecompositionSoundness.native_original_safe_bound s.heights q nodesEnough
        (inputs.roots true) (fun level => family.coefficients (PackedPBSDecompositionReferences.digitSlot true level))
        radix {secondBase compared.2.2.1.2.memory with encoding := hs.encoding}
        (geometry compared.2.2.1.2.memory) basis dummy enough capacity radius (small compared.2.2.1.2.memory) compared.2.2.2 stateAudit
      change Pr{let child ← (AmbientLinear.witness s.heights childScheme dummy compared.2.2.2)}[
        AmbientLinear.OriginalRisk s.heights childScheme dummy capacity radius child ∧
          ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) child.2.2] ≤ _ at conditional
      have bound := conditional.trans (calibrated compared.2.2.1.2.memory)
      simp only [PackedPBSSecondReconstruction.finish,equal,passed,ite_true,prEvent_norm]
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
    · simp [PackedPBSSecondReconstruction.finish,equal,passed,prEvent_norm]

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondReconstructionProbability
