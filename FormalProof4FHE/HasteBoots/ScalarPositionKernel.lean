module
public import FormalProof4FHE.HasteBoots.SafeIdentityKernel
@[expose] public section

/-! An actual first-read prefix determines its literal scalar input and the
finite equation count encoded there. Safe healing at any original job pays
a prefix-selected equation-count charge, rather than a union over all keys. -/
namespace FormalProof4FHE.HasteBoots.ScalarPositionKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

def key {A : Type} (program : Program A) (position : ℕ) (world : World) : Option Input :=
  CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run

def score {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : ENNReal :=
  match CausalStreamExposure.firstRead OracleProgramMachine.step packet with
  | none => (0 : ENNReal)
  | some input => match ScalarRecoveredReplay.recover input with
    | none => (0 : ENNReal)
    | some configuration => (configuration.view.history.statement.infos.val.length : ENNReal) * ((4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ))

def charge {A : Type} (program : Program A) (position : ℕ) (world : World) : ENNReal := score (runPrefix position program world).run

def Event {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (radius : ℕ) (world : World) : Prop :=
  ∃ input ordinal, SafeIdentityKernel.Event program position input ordinal dummy radius world

theorem packet_key {A : Type} {program : Program A} {position ordinal : ℕ} {input : Input} {world other : World}
    (packet : AttainableIdentityEvent.Packet program position input ordinal other)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) : key program position world = some input := by
  have selected := packet.classed.val.first.selected
  rw [packet.classed.val.first_position,packet.classed.property.1] at selected
  have previous := ParentFactorFiber.old_packet (runPrefix position program) world other same
  rw [previous] at selected
  exact selected

theorem ordinal_lt {A : Type} {program : Program A} {position ordinal : ℕ} {input : Input} {world : World}
    (packet : AttainableIdentityEvent.Packet program position input ordinal world) :
    ordinal < packet.configuration.view.history.statement.infos.val.length := by
  have linked := CandidateScalarPacket.of_found packet.classed.val packet.configuration packet.found
  have info := CandidateScalarPacket.identity_info packet.classed.val
  rw [← linked.2.1] at info
  have inside := (List.getElem?_eq_some_iff.mp info).1
  have original := packet.classed.property.2
  omega

theorem jobs_conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (count : ℕ)
    (world : World) (dummy : Digest) (radius : ℕ) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | ∃ i : Fin count, SafeIdentityKernel.Event program position input i.val dummy radius other} ≤
        (count : ENNReal) * ((4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  have union : {other | ∃ i : Fin count, SafeIdentityKernel.Event program position input i.val dummy radius other} =
      ⋃ i : Fin count, {other | SafeIdentityKernel.Event program position input i.val dummy radius other} := by ext other; simp
  rw [union]
  have bounded := (measure_iUnion_le (fun i : Fin count => {other | SafeIdentityKernel.Event program position input i.val dummy radius other})
    (μ := law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])).trans
    (ENNReal.tsum_le_tsum (fun i => SafeIdentityKernel.conditional program position input i.val world dummy radius))
  simpa [tsum_fintype,nsmul_eq_mul] using bounded

theorem conditional {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) (radius : ℕ) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position dummy radius other} ≤
        charge program position world := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  change _ ≤ match key program position world with
    | none => (0 : ENNReal)
    | some input => match ScalarRecoveredReplay.recover input with
      | none => (0 : ENNReal)
      | some configuration => (configuration.view.history.statement.infos.val.length : ENNReal) * ((4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ))
  cases selected : key program position world with
  | none =>
    have included := FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy radius) (fun _ => False) (by
      intro other fiber occurred
      obtain ⟨input,ordinal,⟨⟨packet,_⟩,_⟩⟩ := occurred
      have read := packet_key packet fiber
      rw [selected] at read
      cases read)
    simpa using included
  | some input =>
    simp only []
    cases found : ScalarRecoveredReplay.recover input with
    | none =>
      have included := FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy radius) (fun _ => False) (by
        intro other fiber occurred
        obtain ⟨otherInput,ordinal,⟨⟨packet,_⟩,_⟩⟩ := occurred
        have inputEq := Option.some.inj ((packet_key packet fiber).symm.trans selected)
        subst otherInput
        have recovered := packet.found
        rw [packet.classed.property.1,found] at recovered
        cases recovered)
      simpa using included
    | some configuration =>
      apply (FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy radius)
        (fun other => ∃ i : Fin configuration.view.history.statement.infos.val.length,
          SafeIdentityKernel.Event program position input i.val dummy radius other) (by
          intro other fiber occurred
          obtain ⟨otherInput,ordinal,⟨⟨packet,healing⟩,safe⟩⟩ := occurred
          have inputEq := Option.some.inj ((packet_key packet fiber).symm.trans selected)
          subst otherInput
          have recovered := packet.found
          rw [packet.classed.property.1] at recovered
          have configurationEq := Option.some.inj (recovered.symm.trans found)
          have inside := ordinal_lt packet
          rw [configurationEq] at inside
          exact ⟨⟨ordinal,inside⟩,⟨packet,healing⟩,safe⟩)).trans
      exact jobs_conditional program position input configuration.view.history.statement.infos.val.length world dummy radius

theorem charge_measurable {A : Type} (program : Program A) (position : ℕ) : Measurable (charge program position) :=
  OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) score



theorem charge_seen {A : Type} (program : Program A) (position : ℕ) (world : World) (input : Input) (offset count : ℕ)
    (next : Input → Program A) (active : (runPrefix position program world).run.1 = .inl (.read input offset count next))
    (seen : CausalStreamExposure.seen (runPrefix position program world).run.2 input = true) : charge program position world = 0 := by
  simp only [charge,score,CausalStreamExposure.firstRead,CausalSeedExposure.request,active,OracleProgramMachine.step,seen,
    Bool.true_eq_false,and_false,ite_false]

theorem charge_finished {A : Type} (program : Program A) (position : ℕ) (world : World) (value : A)
    (finished : (runPrefix position program world).run.1 = .inr value) : charge program position world = 0 := by
  simp only [charge,score,CausalStreamExposure.firstRead,CausalSeedExposure.request,finished]

theorem charge_after_finished {A : Type} (program : Program A) (position later : ℕ) (world : World) (value : A)
    (finished : (runPrefix position program world).run.1 = .inr value) : charge program (position+later) world = 0 := by
  have first : (OracleProgram.run (OracleMachine.take OracleProgramMachine.step position program) world).run.1 = .inr value := by
    rw [OracleProgramMachine.take_run]
    exact finished
  have same := OracleMachine.completed_run OracleProgramMachine.step position later program world value first
  rw [OracleProgramMachine.take_run,OracleProgramMachine.take_run] at same
  exact charge_finished program (position+later) world value ((congrArg Prod.fst same).trans finished)

theorem bound {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (radius : ℕ) :
    law {world | Event program position dummy radius world} ≤ ∫⁻ world, charge program position world ∂law := by
  apply OracleFiberOuterBound.score_bound (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))
    {world | Event program position dummy radius world} (fun packet => score packet.1.1.1.1)
  intro world
  exact conditional program position world dummy radius

end
end FormalProof4FHE.HasteBoots.ScalarPositionKernel
