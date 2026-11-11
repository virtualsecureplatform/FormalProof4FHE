module
import all FormalProof4FHE.HasteBoots.CalibratedAdaptiveSourceLedger
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke

namespace HasteBootsSourceFieldCoverageSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsSamplerAncestrySmoke (worldZero)
open FactorFiberSmoke (program input first resume)
open OracleProgram (Program runPrefix)
noncomputable section

def recovered := Classical.choose (ProgramStreamReadCoverage.first program worldZero 3 input first.selected)

theorem recovered_position : recovered.position = 3 := Classical.choose_spec
  (ProgramStreamReadCoverage.first program worldZero 3 input first.selected)

-- Recovering from causal selection preserves a far-offset one-byte read;
-- the preceding empty read and same-key hash are retained in the prefix.
theorem recovered_read : recovered.offset = 999 ∧ recovered.count = 1 := by
  have active := recovered.active
  rw [recovered_position] at active
  change Sum.inl (Program.read input 999 1 resume) = Sum.inl (Program.read input recovered.offset recovered.count recovered.next) at active
  have equal := Program.read.inj (Sum.inl.inj active)
  exact ⟨equal.2.1.symm,equal.2.2.1.symm⟩

-- The general prefix lineage theorem selects the same earliest position.
theorem lineage_position : ∃ position < 4,
    position = 3 ∧ CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program worldZero).run = some input := by
  have seen : CausalStreamExposure.seen (runPrefix 4 program worldZero).run.2 input = true := by decide +kernel
  obtain ⟨position,inside,selected,_⟩ := ProgramStreamReadCoverage.prefix_coverage program worldZero 4 input seen
  obtain ⟨found,atPosition⟩ := ProgramStreamReadCoverage.first program worldZero position input selected
  have equal := found.position_unique first
  exact ⟨position,inside,atPosition.symm.trans equal,selected⟩

-- A zero-length pending read cannot produce the candidate's causal selection.
theorem empty_read : CausalStreamExposure.firstRead OracleProgramMachine.step
    (runPrefix 0 (Program.read input 9000 0 (fun _ => Program.pure ())) worldZero).run = none := by decide +kernel

end
end HasteBootsSourceFieldCoverageSmoke
