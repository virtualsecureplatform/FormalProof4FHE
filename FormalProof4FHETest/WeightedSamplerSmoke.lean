/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.WeightedSampler

open FormalProof4FHE.WeightedSampler
open scoped ENNReal

namespace FormalProof4FHETest.WeightedSamplerSmoke

private def small : Table Bool where
  fallback := false
  entries := [(true, 0), (false, 2), (true, 5), (false, 1), (true, 0)]
  total_pos := by decide

example : Pr[= true | small.sampler] = (5 : ℝ≥0∞) / 8 := by
  rw [Table.probOutput_sampler]
  norm_num [small, outcomeWeight, Table.ticketCount, totalWeight]

/-- info: true -/
#guard_msgs in
#eval
  let values := (List.range small.ticketCount).map (selectList small.entries small.fallback)
  values == [false, false, true, true, true, true, true, false] &&
    (List.range small.ticketCount).all (fun ticket ↦
      let result := selectCounted small.entries small.fallback ticket
      result.1 == selectList small.entries small.fallback ticket && result.2 ≤ small.entries.length)

private def hugeWeight : ℕ := 2 ^ 256

private def huge : Table ℕ where
  fallback := 7
  entries := [(99, 0), (1, hugeWeight), (2, 5), (1, 0)]
  total_pos := by simp [totalWeight]

/-- info: true -/
#guard_msgs in
#eval
  let boundaryCases := [(0, 1, 2), (hugeWeight - 1, 1, 2),
    (hugeWeight, 2, 3), (hugeWeight + 4, 2, 3)]
  huge.entries.length == 4 && huge.ticketCount == hugeWeight + 5 &&
    boundaryCases.all (fun (ticket, expected, inspected) ↦
      let result := selectCounted huge.entries huge.fallback ticket
      result.1 == expected && result.1 == selectList huge.entries huge.fallback ticket &&
        result.2 == inspected)

end FormalProof4FHETest.WeightedSamplerSmoke
