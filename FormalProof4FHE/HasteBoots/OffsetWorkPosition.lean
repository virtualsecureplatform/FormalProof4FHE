module
public import FormalProof4FHE.HasteBoots.LookupStreamWorkRate
public import FormalProof4FHE.HasteBoots.ScalarEquationWork
@[expose] public section

/-! Every original reciprocal class at one earliest-read position is paid
by the literal selected key bytes. Unselected/stopped prefixes pay zero. -/
namespace FormalProof4FHE.HasteBoots.OffsetWorkPosition
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

def score {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : ENNReal :=
  (ScalarEquationWork.selectedBytes OracleProgramMachine.step packet : ENNReal)*LookupStreamWorkRate.rate

def charge {A : Type} (program : Program A) (position : ℕ) (world : World) : ENNReal := score (runPrefix position program world).run

abbrev Event {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop :=
  OffsetPositionKernel.SafeEvent program position dummy world

theorem conditional {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position dummy other} ≤
        charge program position world := by
  rcases OffsetPositionKernel.cost_alternative program position world dummy {other | Event program position dummy other}
      (fun _ _ occurred => occurred) with zero | attained
  · rw [zero]; exact zero_le
  · obtain ⟨reference,same,_,input,ordinal,cost,⟨⟨packet,_⟩,_⟩,bounded⟩ := attained
    have selected := packet.val.source.first.selected
    rw [packet.val.source.first_position] at selected
    rw [ParentFactorFiber.old_packet (runPrefix position program) world reference same] at selected
    have degree : cost ≤ OffsetDegreeBudget.budget := packet.property.2.2.1 ▸ OffsetDegreeBudget.complexity packet.val
    have numerator : (cost : ENNReal) ≤ OffsetDegreeBudget.budget := Nat.cast_le.mpr degree
    apply bounded.trans
    apply (ENNReal.div_le_div_right numerator _).trans
    have priced := LookupStreamWorkRate.input_rate packet.val
    simpa only [charge,score,ScalarEquationWork.selectedBytes,selected] using priced

theorem charge_measurable {A : Type} (program : Program A) (position : ℕ) : Measurable (charge program position) :=
  OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) score

theorem charge_seen {A : Type} (program : Program A) (position : ℕ) (world : World) (input : InputIndexedOracle.Input) (offset count : ℕ)
    (next : InputIndexedOracle.Input → Program A) (active : (runPrefix position program world).run.1 = .inl (.read input offset count next))
    (seen : CausalStreamExposure.seen (runPrefix position program world).run.2 input = true) : charge program position world = 0 := by
  simp only [charge,score,ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,active,OracleProgramMachine.step,seen,
    Bool.true_eq_false,and_false,ite_false,Nat.cast_zero,zero_mul]

theorem charge_finished {A : Type} (program : Program A) (position : ℕ) (world : World) (value : A)
    (finished : (runPrefix position program world).run.1 = .inr value) : charge program position world = 0 := by
  simp only [charge,score,ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,finished,Nat.cast_zero,zero_mul]

theorem bound {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    law {world | Event program position dummy world} ≤ ∫⁻ world, charge program position world ∂law := by
  apply OracleFiberOuterBound.score_bound (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))
    {world | Event program position dummy world} (fun packet => score packet.1.1.1.1)
  intro world
  exact conditional program position world dummy

end
end FormalProof4FHE.HasteBoots.OffsetWorkPosition
