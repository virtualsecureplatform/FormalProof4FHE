import FormalProof4FHE.LWE.GSWBitSampling
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleComp FormalProof4FHE
open scoped ENNReal

namespace FormalProof4FHETest.BoundedUniformSmoke

/-- Consume a deterministic fair-bit tape while recording queries. Large-range
queries would set the flag to false, independently of the returned answer. -/
private def tapeOracle : QueryImpl unifSpec (StateM (List Bool × ℕ × Bool)) :=
  fun index => do
    let state ← get
    set (state.1.tail, state.2.1 + 1, state.2.2 && index == 1)
    return if state.1.headD false then Fin.last index else ⟨0, Nat.succ_pos index⟩

private def runTape {Output : Type} (sampler : ProbComp Output) (bits : List Bool) :
    Output × (List Bool × ℕ × Bool) :=
  (simulateQ tapeOracle sampler).run (bits, 0, true)

/-- info: true -/
#guard_msgs in
#eval
  let first := runTape (BoundedUniform.sampleFin 3 3) [false, true]
  let retry := runTape (BoundedUniform.sampleFin 3 3) [true, true, true, false]
  let exhausted := runTape (BoundedUniform.sampleFin 3 3) (List.replicate 6 true)
  let singleton := runTape (BoundedUniform.sampleFin 1 2) [true, true]
  let zeroBudget := runTape (BoundedUniform.sampleFin 3 0) []
  first.1.val == 1 && first.2.2.1 == 2 && first.2.2.2 &&
    retry.1.val == 2 && retry.2.2.1 == 4 && retry.2.2.2 &&
    exhausted.1.val == 0 && exhausted.2.2.1 == 6 && exhausted.2.2.2 &&
    singleton.1.val == 0 && singleton.2.2.1 == 2 && singleton.2.2.2 &&
    zeroBudget.1.val == 0 && zeroBudget.2.2.1 == 0

private def stored : WeightedSampler.Table ℕ where
  fallback := 999
  entries := [(8, 0), (7, 1), (8, 2)]
  total_pos := by decide

/-- Exhaustion selects a valid ticket, preserving the stored support even when
the table's own fallback is excluded by the intended property. -/
example : Pr[(fun value => value = 7 ∨ value = 8) | stored.bitSampler 3] = 1 := by
  apply WeightedSampler.Table.probEvent_bitSampler_eq_one_of_entries
  intro entry hentry
  simp only [stored, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl
  · simp
  · simp
  · simp

/-- info: true -/
#guard_msgs in
#eval
  let result := runTape (stored.bitSampler 3) (List.replicate 6 true)
  let huge := 2 ^ 256 + 5
  result.1 == 7 && result.2.2.1 == 6 && result.2.2.2 &&
    BoundedUniform.ticketWidth 1 == 1 && BoundedUniform.ticketWidth 3 == 2 &&
    BoundedUniform.ticketWidth 8 == 4 && BoundedUniform.ticketWidth huge == 257

/-- Enumerate all four-bit tapes, including unused suffixes after early acceptance.
The resulting counts check the finite distribution, rather than just one path. -/
private def fourBitTape (value : ℕ) : List Bool :=
  (List.range 4).map (fun position => value.testBit (3 - position))

/-- info: true -/
#guard_msgs in
#eval
  let runs := (List.range 16).map (fun value =>
    runTape (BoundedUniform.sampleFin 3 2) (fourBitTape value))
  let outputs := runs.map (fun run => run.1.val)
  outputs.count 0 == 6 && outputs.count 1 == 5 && outputs.count 2 == 5 &&
    runs.all (fun run => run.2.2.1 ≤ 4 && run.2.2.2)

end FormalProof4FHETest.BoundedUniformSmoke
