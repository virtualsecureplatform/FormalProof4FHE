/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.GaussianIntegerWeights

open FormalProof4FHE.GaussianIntegerWeights FormalProof4FHE.WeightedSampler

namespace FormalProof4FHETest.GaussianWeightsSmoke

/- The computed table covers all errors through the squared-width cutoff. Its
zero entry is exact, its quantized weights are symmetric, and modular collisions
preserve the decoder's results at representative tickets. -/
/-- info: true -/
#guard_msgs in
#eval
  let stored := table 3 24
  let reduced := modularTable 7 3 24
  stored.entries.length == 19 &&
    stored.entries.all (fun entry ↦ entry.1.natAbs ≤ 9 && entry.2 ≤ 2 ^ 24 &&
      entry.2 == integerWeight 3 24 (-entry.1)) &&
    integerWeight 3 24 0 == 2 ^ 24 &&
    selectList stored.entries stored.fallback 0 == -9 &&
    selectList stored.entries stored.fallback (stored.ticketCount - 1) == 9 &&
    stored.ticketCount == reduced.ticketCount &&
    [0, stored.ticketCount / 2, stored.ticketCount - 1].all (fun ticket ↦
      let integerValue := selectList stored.entries stored.fallback ticket
      let modularValue := selectList reduced.entries reduced.fallback ticket
      modularValue == (integerValue : ZMod 7))

/- The generator itself produces a large ticket space with only nine stored
entries; these boundary decoder checks allocate no repeated-ticket table. -/
/-- info: true -/
#guard_msgs in
#eval
  let stored := table 2 64
  stored.entries.length == 9 && stored.ticketCount > 2 ^ 64 &&
    integerWeight 2 64 0 == 2 ^ 64 &&
    selectList stored.entries stored.fallback 0 == -4 &&
    selectList stored.entries stored.fallback (stored.ticketCount - 1) == 4 &&
    (selectCounted stored.entries stored.fallback (stored.ticketCount - 1)).2 == 9

end FormalProof4FHETest.GaussianWeightsSmoke
