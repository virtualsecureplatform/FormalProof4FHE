module
import all FormalProof4FHE.HasteBoots.ReceiptFirstReadCoverage
import all FormalProof4FHE.HasteBoots.LookupPreludeTrace
import all FormalProof4FHETest.HasteBootsFreshReceiptTargetSmoke

namespace FormalProof4FHE.HasteBoots.ReceiptCoverageSmoke
open FreshReceiptTargetSmoke (program input phase)
open HasteBootsSamplerAncestrySmoke (worldZero)
open OracleProgram (run runPrefix)
open ProgramFirstStreamRead (First)
open NativeReceiptPrefixView (key)
noncomputable section

/-- Starts, an empty read at offset 1000 and a SHA-512 observation do not
make the later positive SHAKE receipt read an earlier exposure. -/
theorem actual_order :
    ∃ outer : First program worldZero input,
      ∃ receipt : First program worldZero (key phase.consumed),
        outer.position < receipt.position ∧
          NativeTranscript.Observation.output input outer.offset
            (InputIndexedOracle.bytes worldZero input outer.offset outer.count) ∈
              (runPrefix receipt.position program worldZero).run.2 := by
  let outer : First program worldZero input :=
    ⟨3,77,1,(fun _ => .read (key phase.consumed) 999 1 (fun _ => FreshReceiptTargetSmoke.tail)),
      rfl,rfl,by decide +kernel,by decide,rfl⟩
  have receiptOutput : NativeTranscript.Observation.output (key phase.consumed) 999
      (InputIndexedOracle.bytes worldZero (key phase.consumed) 999 1) ∈ (run program worldZero).run.2 := by
    change _ ∈ [_,_,_,_,_,_]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))
  obtain ⟨receipt⟩ := ProgramFirstStreamRead.of_output program worldZero (key phase.consumed) 999 _
    (by intro empty; have length := congrArg List.length empty; simp only [InputIndexedOracle.bytes_length,List.length_nil] at length; contradiction) receiptOutput
  have unseen : CausalStreamExposure.seen (runPrefix outer.position program worldZero).run.2 (key phase.consumed) = false := by
    change CausalStreamExposure.seen [_,_,_] _ = false
    simp [CausalStreamExposure.seen,CausalStreamExposure.touches,InputIndexedOracle.bytes_length]
  have apart : input ≠ key phase.consumed := by decide +kernel
  have ordered := ReceiptFirstReadCoverage.before_of_unseen outer receipt apart unseen
  exact ⟨outer,receipt,ordered,ReceiptFirstReadCoverage.output_before outer receipt ordered⟩

end
end FormalProof4FHE.HasteBoots.ReceiptCoverageSmoke
