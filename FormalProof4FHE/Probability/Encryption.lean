/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.Discrete
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime

/-! # Executable one-time encryption experiments -/

open AsymmEncAlg OracleComp
open scoped FormalProof4FHE

namespace FormalProof4FHE

variable {M PK SK C : Type} {encAlg : AsymmEncAlg ProbComp M PK SK C}

/-- The one-time experiment with the canonical finite uniform runtime. -/
abbrev oneTimeGame (adv : IND_CPA_OneTime_Adversary encAlg) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _) ← encAlg.keygen
  let (m₁, m₂, state) ← adv.chooseMessages pk
  let c ← encAlg.encrypt pk (if b then m₁ else m₂)
  let b' ← adv.distinguish state c
  pure (b == b')

/-- The signed success excess over an independent fair guess. -/
noncomputable def oneTimeSignedAdvantage (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_OneTime_Adversary encAlg) : ℝ :=
  (probOutput (oneTimeGame adv) true).toReal - 1 / 2

/-- The executable experiment agrees with VCVio's runtime-parametric experiment. -/
theorem oneTimeGame_eq_native (adv : IND_CPA_OneTime_Adversary encAlg) :
    oneTimeGame adv = IND_CPA_OneTime_Game adv ProbCompRuntime.probComp := rfl

end FormalProof4FHE
