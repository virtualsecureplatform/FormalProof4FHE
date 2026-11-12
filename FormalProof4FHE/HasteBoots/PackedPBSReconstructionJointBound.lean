module
public import FormalProof4FHE.HasteBoots.PackedPBSFirstReconstructionProbability
@[expose] public section

/-! All original Hadamard, NTT and first-reconstruction risks share one
collision charge for the actual extended prefix, including rejected paths. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSReconstructionJointBound
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (Before LinearOutcome beforeState reconstruction)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev Outcome := Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height) ×
  Option (LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (d := d) (front := front) (suffix := suffix)
    (queries := queries) (height := height))

def finalState (outcome : Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
      (front := front) (suffix := suffix) (queries := queries) (height := height)) :=
  match outcome.2 with
  | none => beforeState outcome.1
  | some child => child.2.2

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

def BeforeRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (before : Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
      (front := front) (queries := queries) (height := height)) : Prop :=
  OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs)
    dummy capacity radius before.1 ∨
  ∃ later, before.2 = some later ∧ NTTLoopProbability.AnyRisk
    (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity (fun _ => radius) later.1

def LinearRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
      (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  ∃ later child, outcome.1.2 = some later ∧ outcome.2 = some child ∧
    OwnedLinearSoundness.OriginalRisk (reconstruction family inputs nodesEnough radix linearBase false later.1.memory)
      dummy capacity radius child

def Risk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
      (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  BeforeRisk length psi primitive family base hs dummy capacity radius outcome.1 ∨
    LinearRisk family inputs nodesEnough radix linearBase dummy capacity radius outcome

/-- Later adaptive execution cannot increase a fixed predecessor event,
without any losslessness premise for the adversary's continuation. -/
theorem earlier_event_le (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (event : Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
      (front := front) (queries := queries) (height := height) → Prop) :
    Pr{let outcome ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)}[
      event outcome.1] ≤
    Pr{let before ← (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial)}[event before] := by
  unfold PackedPBSFirstReconstruction.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  cases equal : before.2 with
  | none => simp [prEvent_norm,outside]
  | some later =>
    by_cases passed : later.1.accepted = true
    · simp only [passed,ite_true,prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ event => outside event)
    · simp [passed,prEvent_norm,outside]

/-- The predecessor's collision event persists to the exact extended final
state; a rejected loop retains its own final state without extra calls. -/
theorem before_bad_persistent (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (outcome : Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
      (front := front) (suffix := suffix) (queries := queries) (height := height))
    (supported : outcome ∈ support (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial))
    (bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (beforeState outcome.1)) :
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (finalState outcome) := by
  rcases outcome with ⟨before,optional⟩
  cases optional with
  | none => exact bad
  | some child =>
    obtain ⟨later,reached,_,_,present⟩ := PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs
      base hs nodesEnough radix linearBase dummy initial before child supported
    let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
    have initialBad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2 := by
      simpa only [beforeState,reached] using bad
    have projected : ((child.1.1,child.2.1),child.2.2) ∈ support
        ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
          (RecordedSourceCoherence.Shape Cfg height)) (AuthenticatedLinear.program l)).run later.2) := by
      unfold AuthenticatedLinear.program
      rw [←MultiCommitmentPrefix.project_witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
        (AuthenticatedLinear.continuation l) later.2,support_map]
      exact Set.mem_image_of_mem _ present
    exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (RecordedSourceCoherence.Shape Cfg height) (AuthenticatedLinear.program l) later.2 initialBad _ projected

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]
  [SampleableType (Fin n → ZMod q)] [SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]

/-- Every original stage risk in the extended prefix has one conditional
arithmetic budget from an arbitrary audited incoming history. -/
theorem native_safe_joint_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
  (hadNodes : 2*b ≤ (2*b-1)*2+1)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (nttEpsilon : Fin (2*d+1) → ENNReal) (linearEpsilon : ENNReal)
    (nttEncoding : ∀ slot memory, (base slot memory).encoding = hs.encoding)
    (linearEncoding : ∀ memory, (linearBase memory).encoding = hs.encoding)
    (hadSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (nttSmall : ∀ slot memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (linearSmall : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (linearBase memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (nttCalibrated : ∀ slot memory, HadamardNTTProbability.rate (K := K) (base slot memory) radius ≤ nttEpsilon slot)
    (linearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries)
        (linearBase memory).domain radius ≤ linearEpsilon)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy initial)}[
      Risk length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (finalState outcome)] ≤
      ((PackedPBSHadamardNTTJointBound.rate (K := K) hs radius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) := by
  let ns := (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs)
  have old := PackedPBSHadamardNTTJointBound.native_safe_risk_bound length psi primitive family base
    firstSmall roundSmall hadNodes hs basis dummy enough capacity radius hadSmall (fun _ => radius) nttEpsilon
    nttEncoding nttSmall nttCalibrated initial audited
  have earlier := earlier_event_le length psi primitive family inputs base ns nodesEnough radix linearBase dummy initial
    (fun before => BeforeRisk length psi primitive family base ns dummy capacity radius before ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (beforeState before))
  have predecessor : Pr{let outcome ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base ns
        nodesEnough radix linearBase dummy initial)}[
      BeforeRisk length psi primitive family base ns dummy capacity radius outcome.1 ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (beforeState outcome.1)] ≤
      PackedPBSHadamardNTTJointBound.rate (K := K) hs radius + ((List.finRange (2*d+1)).map nttEpsilon).sum := by
    apply earlier.trans
    convert old using 1
    apply prEvent_congr
    intro before
    cases equal : before.2 <;> simp [BeforeRisk,beforeState,equal,ns]
  have linear := PackedPBSFirstReconstructionProbability.safe_linear_risk_bound length psi primitive family inputs
    base ns nodesEnough radix linearBase basis dummy enough capacity radius linearEpsilon linearEncoding linearSmall
    linearCalibrated initial audited
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    (BeforeRisk length psi primitive family base ns dummy capacity radius outcome.1 ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (beforeState outcome.1)) ∨
    (∃ later child, outcome.1.2 = some later ∧ outcome.2 = some child ∧
      OwnedLinearSoundness.OriginalRisk (reconstruction family inputs nodesEnough radix linearBase false later.1.memory)
        dummy capacity radius child ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) child.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add predecessor linear)
  · intro outcome supported event
    obtain ⟨risk,safe⟩ := event
    rcases risk with beforeRisk | linearRisk
    · refine Or.inl ⟨beforeRisk,?_⟩
      intro bad
      exact safe (before_bad_persistent length psi primitive family inputs base ns nodesEnough radix linearBase
        dummy initial outcome supported bad)
    · obtain ⟨later,child,reached,present,risk⟩ := linearRisk
      refine Or.inr ⟨later,child,reached,present,risk,?_⟩
      intro bad
      apply safe
      simpa only [finalState,present] using bad

/-- All original Hadamard, retained NTT and reached reconstruction risks,
including the final collision, pay ONE charge on the entire actual prefix. -/
theorem native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
  (hadNodes : 2*b ≤ (2*b-1)*2+1)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (nttEpsilon : Fin (2*d+1) → ENNReal) (linearEpsilon : ENNReal)
    (nttEncoding : ∀ slot memory, (base slot memory).encoding = hs.encoding)
    (linearEncoding : ∀ memory, (linearBase memory).encoding = hs.encoding)
    (hadSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) hs.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (nttSmall : ∀ slot memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (linearSmall : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (linearBase memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (nttCalibrated : ∀ slot memory, HadamardNTTProbability.rate (K := K) (base slot memory) radius ≤ nttEpsilon slot)
    (linearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries)
        (linearBase memory).domain radius ≤ linearEpsilon) :
    Pr{let outcome ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      Risk length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy capacity radius outcome ∨
      CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (finalState outcome)] ≤
      ((PackedPBSHadamardNTTJointBound.rate (K := K) hs radius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  let ns := (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs)
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have arithmetic := native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase basis dummy enough capacity radius
    nttEpsilon linearEpsilon nttEncoding linearEncoding hadSmall nttSmall linearSmall nttCalibrated linearCalibrated
    _ ⟨initial.1,fun _ => initial.2.2⟩
  have hash := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (RecordedSourceCoherence.Shape Cfg height)
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base ns nodesEnough radix linearBase)
  have project := PackedPBSFirstReconstruction.project_witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))
  have enc : ns.encoding = hs.encoding := rfl
  rw [enc] at project
  rw [←project,prEvent_map] at hash
  apply le_trans (prEvent_mono _ _ (fun outcome =>
    (Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (finalState outcome)) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (finalState outcome)) ?_)
  · apply (prEvent_or_le _ _ _).trans
    apply add_le_add arithmetic
    convert hash using 1
    apply prEvent_congr
    intro outcome
    cases equal : outcome.2 <;> simp [finalState,equal]
  · intro outcome event
    by_cases bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) (finalState outcome)
    · exact Or.inr bad
    · exact Or.inl ⟨event.resolve_right bad,bad⟩

end
end FormalProof4FHE.HasteBoots.PackedPBSReconstructionJointBound
